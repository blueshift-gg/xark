//! **Streamable R1CS row file** (`r1cs.stream`): a compact, windowed encoding of
//! an R1CS program that a prover can read row-window by row-window without ever
//! materializing the structured program.
//!
//! Used for circuits whose proving key is generated for the *boundary-minimized*
//! R1CS — a form the bytecode can't stream, because the global minimize pass runs
//! after expansion. `xark setup` writes it next to the key (tagged with the source
//! `circuit.xbc` fingerprint), so `xark prove` / `proveStreaming` stream it.
//!
//! Layout (all integers LEB128 unless noted):
//! ```text
//! "XRS1" | fp_len fp | n_vars (id public:u8)* | n_pool (len signed-LE-bytes)*
//! | n_rows | window | n_windows (u64 LE offset)* | rows
//! row = 3 × LC,  LC = const_idx n_terms (var_delta coeff_idx)*
//! ```
//! Coefficients are interned in a pool (a minimized circuit reuses a few distinct
//! constants millions of times); `const_idx == 0` / `pool[0]` is always zero. Term
//! vars are delta-encoded within an LC (sorted ascending), so typical rows cost a
//! few bytes per term. Window offsets let any window decode independently.

use num_bigint::BigInt;

use crate::field::FieldConst;
use crate::linear_combination::LinearCombination;
use crate::r1cs::{R1csProgram, Visibility};

const MAGIC: &[u8; 4] = b"XRS1";
/// Rows per indexed window.
pub const WINDOW_ROWS: usize = 4096;

fn put_uv(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn get_uv(b: &[u8], p: &mut usize) -> Option<u64> {
    let mut v = 0u64;
    let mut shift = 0;
    loop {
        let byte = *b.get(*p)?;
        *p += 1;
        v |= ((byte & 0x7f) as u64) << shift;
        if byte & 0x80 == 0 {
            return Some(v);
        }
        shift += 7;
        if shift > 63 {
            return None;
        }
    }
}

struct Pool {
    vals: Vec<Vec<u8>>,
    index: std::collections::HashMap<Vec<u8>, u32>,
}

impl Pool {
    fn intern(&mut self, f: &FieldConst) -> u32 {
        let bytes = if f.is_zero() {
            Vec::new()
        } else {
            f.big().to_signed_bytes_le()
        };
        if let Some(&i) = self.index.get(&bytes) {
            return i;
        }
        let i = self.vals.len() as u32;
        self.index.insert(bytes.clone(), i);
        self.vals.push(bytes);
        i
    }
}

fn put_lc(out: &mut Vec<u8>, lc: &LinearCombination, pool: &mut Pool) {
    put_uv(out, pool.intern(&lc.constant) as u64);
    let mut terms: Vec<(u32, u32)> = lc
        .terms
        .iter()
        .map(|t| (t.var, pool.intern(&t.coeff)))
        .collect();
    terms.sort_unstable_by_key(|t| t.0);
    put_uv(out, terms.len() as u64);
    let mut prev = 0u32;
    for (var, coeff) in terms {
        put_uv(out, (var - prev) as u64);
        put_uv(out, coeff as u64);
        prev = var;
    }
}

/// Encode `prog` (rows in order; LC terms are summed, so duplicates are harmless)
/// tagged with `fingerprint` (the source `circuit.xbc` SHA-256).
pub fn encode(fingerprint: &str, prog: &R1csProgram) -> Vec<u8> {
    let mut pool = Pool {
        vals: Vec::new(),
        index: Default::default(),
    };
    pool.intern(&FieldConst::zero()); // index 0 = zero
    let mut rows = Vec::new();
    let mut offsets = Vec::new();
    for (i, c) in prog.constraints.iter().enumerate() {
        if i % WINDOW_ROWS == 0 {
            offsets.push(rows.len() as u64);
        }
        put_lc(&mut rows, &c.a, &mut pool);
        put_lc(&mut rows, &c.b, &mut pool);
        put_lc(&mut rows, &c.c, &mut pool);
    }
    let mut out = Vec::with_capacity(rows.len() + 1024);
    out.extend_from_slice(MAGIC);
    put_uv(&mut out, fingerprint.len() as u64);
    out.extend_from_slice(fingerprint.as_bytes());
    put_uv(&mut out, prog.variables.len() as u64);
    for v in &prog.variables {
        put_uv(&mut out, v.id as u64);
        out.push((v.visibility == Visibility::Public) as u8);
    }
    put_uv(&mut out, pool.vals.len() as u64);
    for p in &pool.vals {
        put_uv(&mut out, p.len() as u64);
        out.extend_from_slice(p);
    }
    put_uv(&mut out, prog.constraints.len() as u64);
    put_uv(&mut out, WINDOW_ROWS as u64);
    put_uv(&mut out, offsets.len() as u64);
    for o in offsets {
        out.extend_from_slice(&o.to_le_bytes());
    }
    out.extend_from_slice(&rows);
    out
}

/// A parsed row file. Owns its bytes; rows are decoded per window on demand.
pub struct RowFile {
    bytes: Vec<u8>,
    fingerprint: String,
    vars: Vec<(u32, bool)>,
    pool: Vec<FieldConst>,
    num_rows: usize,
    window: usize,
    offsets: Vec<u64>,
    rows_start: usize,
}

impl RowFile {
    /// Parse the header (vars, pool, window index). `Err` on any malformation.
    pub fn parse(bytes: Vec<u8>) -> Result<Self, String> {
        let bad = || "malformed r1cs.stream".to_string();
        if bytes.len() < 4 || &bytes[..4] != MAGIC {
            return Err("not an r1cs.stream file".into());
        }
        let mut p = 4;
        let b = &bytes;
        let fl = get_uv(b, &mut p).ok_or_else(bad)? as usize;
        let fingerprint =
            String::from_utf8(b.get(p..p + fl).ok_or_else(bad)?.to_vec()).map_err(|_| bad())?;
        p += fl;
        let nv = get_uv(b, &mut p).ok_or_else(bad)? as usize;
        let mut vars = Vec::with_capacity(nv.min(b.len()));
        for _ in 0..nv {
            let id = get_uv(b, &mut p).ok_or_else(bad)? as u32;
            let public = *b.get(p).ok_or_else(bad)? == 1;
            p += 1;
            vars.push((id, public));
        }
        let np = get_uv(b, &mut p).ok_or_else(bad)? as usize;
        let mut pool = Vec::with_capacity(np.min(b.len()));
        for _ in 0..np {
            let l = get_uv(b, &mut p).ok_or_else(bad)? as usize;
            let raw = b.get(p..p + l).ok_or_else(bad)?;
            p += l;
            pool.push(if l == 0 {
                FieldConst::zero()
            } else {
                FieldConst::from_bigint(BigInt::from_signed_bytes_le(raw))
            });
        }
        let num_rows = get_uv(b, &mut p).ok_or_else(bad)? as usize;
        let window = get_uv(b, &mut p).ok_or_else(bad)? as usize;
        let nw = get_uv(b, &mut p).ok_or_else(bad)? as usize;
        if window == 0 || nw != num_rows.div_ceil(window) {
            return Err(bad());
        }
        let mut offsets = Vec::with_capacity(nw);
        for _ in 0..nw {
            let o = b.get(p..p + 8).ok_or_else(bad)?;
            offsets.push(u64::from_le_bytes(o.try_into().unwrap()));
            p += 8;
        }
        Ok(RowFile {
            fingerprint,
            vars,
            pool,
            num_rows,
            window,
            offsets,
            rows_start: p,
            bytes,
        })
    }

    pub fn fingerprint(&self) -> &str {
        &self.fingerprint
    }
    /// `(id, is_public)` for every variable, in file order.
    pub fn vars(&self) -> &[(u32, bool)] {
        &self.vars
    }
    pub fn pool(&self) -> &[FieldConst] {
        &self.pool
    }
    pub fn num_rows(&self) -> usize {
        self.num_rows
    }
    pub fn window_rows(&self) -> usize {
        self.window
    }
    pub fn num_windows(&self) -> usize {
        self.offsets.len()
    }
    /// Size of the encoded file in bytes.
    pub fn byte_len(&self) -> usize {
        self.bytes.len()
    }

    #[allow(clippy::type_complexity)]
    /// Decode window `w`: `lc(const_idx, terms)` is called three times per row
    /// (A, B, C), in row order, with `terms = [(var, coeff_idx)]`.
    pub fn decode_window(
        &self,
        w: usize,
        lc: &mut dyn FnMut(u32, &[(u32, u32)]),
    ) -> Result<(), String> {
        let bad = || "malformed r1cs.stream row".to_string();
        let b = &self.bytes;
        let mut p = self.rows_start + self.offsets[w] as usize;
        let rows = self.window.min(self.num_rows - w * self.window);
        let mut terms: Vec<(u32, u32)> = Vec::new();
        for _ in 0..rows * 3 {
            let k = get_uv(b, &mut p).ok_or_else(bad)? as u32;
            let n = get_uv(b, &mut p).ok_or_else(bad)? as usize;
            terms.clear();
            let mut var = 0u32;
            for _ in 0..n {
                var += get_uv(b, &mut p).ok_or_else(bad)? as u32;
                let c = get_uv(b, &mut p).ok_or_else(bad)? as u32;
                if c as usize >= self.pool.len() {
                    return Err(bad());
                }
                terms.push((var, c));
            }
            if k as usize >= self.pool.len() {
                return Err(bad());
            }
            lc(k, &terms);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::linear_combination::Term;
    use crate::r1cs::{FieldSpec, R1csConstraint, Variable};

    #[test]
    fn round_trips_rows_vars_and_coefficients() {
        let big = FieldConst::from_decimal(
            "21888242871839275222246405745257275088548364400416034343698204186575808495616",
        )
        .unwrap();
        let mut constraints = Vec::new();
        for i in 0..(WINDOW_ROWS * 2 + 17) as u32 {
            let a = LinearCombination {
                constant: if i % 3 == 0 {
                    big.clone()
                } else {
                    FieldConst::zero()
                },
                terms: vec![
                    Term {
                        coeff: FieldConst::from_i64(-(i as i64)),
                        var: i + 7,
                    },
                    Term {
                        coeff: FieldConst::one(),
                        var: 2,
                    },
                ],
            };
            constraints.push(R1csConstraint::general(
                i,
                a,
                LinearCombination::var(1),
                LinearCombination::zero(),
                "",
            ));
        }
        let variables = (0..(WINDOW_ROWS * 2 + 30) as u32)
            .map(|id| Variable {
                id,
                name: String::new(),
                visibility: if id == 1 {
                    Visibility::Public
                } else {
                    Visibility::Internal
                },
            })
            .collect();
        let prog = R1csProgram {
            field: FieldSpec::bn254(),
            variables,
            constraints,
        };
        let rf = RowFile::parse(encode("fp", &prog)).unwrap();
        assert_eq!(rf.fingerprint(), "fp");
        assert_eq!(rf.num_rows(), prog.constraints.len());
        assert_eq!(rf.vars()[1], (1, true));
        let mut row = 0usize;
        let mut m = 0usize;
        for w in 0..rf.num_windows() {
            rf.decode_window(w, &mut |k, terms| {
                let c = &prog.constraints[row];
                let lc = [&c.a, &c.b, &c.c][m];
                assert_eq!(rf.pool()[k as usize], lc.constant);
                let mut want: Vec<(u32, FieldConst)> =
                    lc.terms.iter().map(|t| (t.var, t.coeff.clone())).collect();
                want.sort_by_key(|t| t.0);
                let got: Vec<(u32, FieldConst)> = terms
                    .iter()
                    .map(|&(v, ci)| (v, rf.pool()[ci as usize].clone()))
                    .collect();
                assert_eq!(got, want);
                m += 1;
                if m == 3 {
                    m = 0;
                    row += 1;
                }
            })
            .unwrap();
        }
        assert_eq!(row, prog.constraints.len());
        // Truncation is an error, never a panic.
        let bytes = encode("fp", &prog);
        for cut in [3, 10, bytes.len() / 2] {
            if let Ok(rf) = RowFile::parse(bytes[..cut].to_vec()) {
                for w in 0..rf.num_windows() {
                    let _ = rf.decode_window(w, &mut |_, _| {});
                }
            }
        }
    }
}
