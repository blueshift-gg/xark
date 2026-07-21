//! On-disk cache of the **minimized** R1CS that `xark setup` keys the proving key
//! to, so `xark prove` can reload it instead of re-running the deterministic
//! boundary-minimize + `validate()` phase.
//!
//! Encoded with [`wincode`] as a lean, matrix-only view: coefficients as signed
//! little-endian bytes, variables as `(id, visibility)` only. Debug notes and
//! names are dropped — they don't affect the Groth16 matrix (so the reloaded
//! program keys to the same pk) and prove never reads them.
//!
//! Tagged with the SHA-256 fingerprint of the `circuit.xbc` it was built from; a
//! mismatch makes prove ignore the stale cache and recompute, so it can never
//! silently desync from the key.

use num_bigint::BigInt;
use wincode::config::Configuration;
use wincode::{SchemaRead, SchemaWrite};

use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, Term};
use crate::r1cs::{FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};

/// Magic + version for the raw header preceding the wincode body. The fingerprint
/// lives here (not in the body) so a stale/foreign cache is rejected by a cheap
/// byte compare *before* the large body is decoded.
const MAGIC: &[u8; 4] = b"XR1C";
const FORMAT_VERSION: u8 = 1;

#[derive(SchemaWrite, SchemaRead)]
struct CacheBody {
    field_name: String,
    /// Field modulus decimal, or empty for an unknown field.
    modulus: String,
    vars: Vec<CVar>,
    /// Distinct coefficient values (signed little-endian bytes), first-seen order.
    /// A minimized R1CS reuses the same few constants across millions of terms, so
    /// pooling + indexing shrinks the cache several-fold vs storing them inline.
    pool: Vec<Vec<u8>>,
    cons: Vec<CCon>,
}

#[derive(SchemaWrite, SchemaRead)]
struct CVar {
    id: u32,
    /// `Visibility` as `0=Private 1=Public 2=Internal`.
    vis: u8,
}

#[derive(SchemaWrite, SchemaRead)]
struct CCon {
    a: CLc,
    b: CLc,
    c: CLc,
}

#[derive(SchemaWrite, SchemaRead)]
struct CLc {
    /// Pool index of the constant term.
    k: u32,
    terms: Vec<CTerm>,
}

#[derive(SchemaWrite, SchemaRead)]
struct CTerm {
    var: u32,
    /// Pool index of the coefficient.
    coeff: u32,
}

/// Interns coefficient byte-strings into a pool, returning a stable index per
/// distinct value (first-seen order → deterministic given the fixed constraint
/// order).
struct Pool {
    pool: Vec<Vec<u8>>,
    index: std::collections::BTreeMap<Vec<u8>, u32>,
}

impl Pool {
    fn new() -> Self {
        Pool {
            pool: Vec::new(),
            index: std::collections::BTreeMap::new(),
        }
    }

    fn intern(&mut self, bytes: Vec<u8>) -> u32 {
        if let Some(&i) = self.index.get(&bytes) {
            return i;
        }
        let i = self.pool.len() as u32;
        self.index.insert(bytes.clone(), i);
        self.pool.push(bytes);
        i
    }
}

fn vis_to_u8(v: &Visibility) -> u8 {
    match v {
        Visibility::Private => 0,
        Visibility::Public => 1,
        Visibility::Internal => 2,
    }
}

fn u8_to_vis(b: u8) -> Visibility {
    match b {
        0 => Visibility::Private,
        1 => Visibility::Public,
        _ => Visibility::Internal,
    }
}

fn fc_to_bytes(f: &FieldConst) -> Vec<u8> {
    f.big().to_signed_bytes_le()
}

fn bytes_to_fc(b: &[u8]) -> FieldConst {
    FieldConst::from_bigint(BigInt::from_signed_bytes_le(b))
}

fn lc_to_c(lc: &LinearCombination, pool: &mut Pool) -> CLc {
    CLc {
        k: pool.intern(fc_to_bytes(&lc.constant)),
        terms: lc
            .terms
            .iter()
            .map(|t| CTerm {
                var: t.var,
                coeff: pool.intern(fc_to_bytes(&t.coeff)),
            })
            .collect(),
    }
}

fn c_to_lc(c: CLc, pool: &[Vec<u8>]) -> LinearCombination {
    LinearCombination {
        constant: bytes_to_fc(&pool[c.k as usize]),
        terms: c
            .terms
            .into_iter()
            .map(|t| Term {
                coeff: bytes_to_fc(&pool[t.coeff as usize]),
                var: t.var,
            })
            .collect(),
    }
}

/// wincode config: varint encoding with the preallocation-size guard disabled —
/// a multi-million-constraint R1CS blows past wincode's 4 MiB default, and the
/// cache is our own fingerprint-tagged artifact next to the equally-trusted pk.
fn cache_config() -> impl wincode::config::Config {
    Configuration::default()
        .with_varint_encoding()
        .disable_preallocation_size_limit()
}

/// Serialize `prog` (a minimized R1CS) with a raw `fingerprint` header followed
/// by the wincode-encoded body. Returns `Err` (rather than panicking) if wincode
/// serialization fails, so `xark setup --cache` can just skip the cache after a
/// successful keygen instead of aborting.
pub fn serialize(fingerprint: &str, prog: &R1csProgram) -> Result<Vec<u8>, String> {
    let mut pool = Pool::new();
    let cons: Vec<CCon> = prog
        .constraints
        .iter()
        .map(|con| CCon {
            a: lc_to_c(&con.a, &mut pool),
            b: lc_to_c(&con.b, &mut pool),
            c: lc_to_c(&con.c, &mut pool),
        })
        .collect();
    let body = CacheBody {
        field_name: prog.field.name.clone(),
        modulus: prog.field.modulus_decimal.clone().unwrap_or_default(),
        vars: prog
            .variables
            .iter()
            .map(|v| CVar {
                id: v.id,
                vis: vis_to_u8(&v.visibility),
            })
            .collect(),
        pool: pool.pool,
        cons,
    };
    let body_bytes = wincode::config::serialize(&body, cache_config())
        .map_err(|e| format!("wincode serialize R1CS cache: {e:?}"))?;

    let fp = fingerprint.as_bytes();
    let mut out = Vec::with_capacity(MAGIC.len() + 1 + 4 + fp.len() + body_bytes.len());
    out.extend_from_slice(MAGIC);
    out.push(FORMAT_VERSION);
    out.extend_from_slice(&(fp.len() as u32).to_le_bytes());
    out.extend_from_slice(fp);
    out.extend_from_slice(&body_bytes);
    Ok(out)
}

/// Parse the raw header, returning the fingerprint and the remaining body bytes.
/// `None` on bad magic/version or truncation.
fn parse_header(bytes: &[u8]) -> Option<(&str, &[u8])> {
    let rest = bytes.strip_prefix(MAGIC.as_slice())?;
    let (&ver, rest) = rest.split_first()?;
    if ver != FORMAT_VERSION {
        return None;
    }
    let (len_bytes, rest) = rest.split_first_chunk::<4>()?;
    let fp_len = u32::from_le_bytes(*len_bytes) as usize;
    if rest.len() < fp_len {
        return None;
    }
    let (fp_bytes, body) = rest.split_at(fp_len);
    let fp = std::str::from_utf8(fp_bytes).ok()?;
    Some((fp, body))
}

fn body_to_prog(body: CacheBody) -> R1csProgram {
    R1csProgram {
        field: FieldSpec {
            name: body.field_name,
            modulus_decimal: if body.modulus.is_empty() {
                None
            } else {
                Some(body.modulus)
            },
        },
        variables: body
            .vars
            .into_iter()
            .map(|v| Variable {
                id: v.id,
                name: String::new(),
                visibility: u8_to_vis(v.vis),
            })
            .collect(),
        constraints: body
            .cons
            .into_iter()
            .enumerate()
            .map(|(i, con)| R1csConstraint {
                id: i as u32,
                a: c_to_lc(con.a, &body.pool),
                b: c_to_lc(con.b, &body.pool),
                c: c_to_lc(con.c, &body.pool),
                debug: None,
            })
            .collect(),
    }
}

/// Load the cached program **only if** its header fingerprint equals `expected`.
/// A missing header, mismatched fingerprint, or corrupt body all return `None`
/// (caller recomputes). The fingerprint is checked before the body is decoded.
/// Variable names and debug notes are reconstructed empty.
pub fn deserialize_if_fingerprint(bytes: &[u8], expected: &str) -> Option<R1csProgram> {
    let (fp, body) = parse_header(bytes)?;
    if fp != expected {
        return None;
    }
    let cache: CacheBody = wincode::config::deserialize(body, cache_config()).ok()?;
    Some(body_to_prog(cache))
}

/// Full decode (fingerprint + program) with no fingerprint filter — used by the
/// round-trip test. Returns `Err` on any decode failure.
pub fn deserialize(bytes: &[u8]) -> Result<(String, R1csProgram), String> {
    let (fp, body) = parse_header(bytes).ok_or_else(|| "bad cache header".to_string())?;
    let fp = fp.to_string();
    let cache: CacheBody = wincode::config::deserialize(body, cache_config())
        .map_err(|e| format!("wincode decode: {e:?}"))?;
    Ok((fp, body_to_prog(cache)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::linear_combination::LinearCombination;

    fn sample_prog() -> R1csProgram {
        R1csProgram {
            field: FieldSpec::bn254(),
            variables: vec![
                Variable {
                    id: 0,
                    name: "a".into(),
                    visibility: Visibility::Public,
                },
                Variable {
                    id: 1,
                    name: "t".into(),
                    visibility: Visibility::Internal,
                },
            ],
            constraints: vec![R1csConstraint::general(
                0,
                LinearCombination::var(0),
                LinearCombination::var(0),
                LinearCombination::var(1),
                "a*a=t",
            )],
        }
    }

    #[test]
    fn round_trips_matrix_and_fingerprint() {
        let prog = sample_prog();
        let bytes = serialize("deadbeef", &prog).unwrap();
        let (fp, back) = deserialize(&bytes).unwrap();
        assert_eq!(fp, "deadbeef");
        assert_eq!(back.field.modulus_decimal, prog.field.modulus_decimal);
        assert_eq!(back.variables.len(), 2);
        assert_eq!(back.variables[1].visibility, Visibility::Internal);
        assert_eq!(back.constraints.len(), 1);
        // Matrix preserved (coefficients + vars), which is what the pk keys to.
        assert_eq!(back.constraints[0].a, prog.constraints[0].a);
        assert_eq!(back.constraints[0].c, prog.constraints[0].c);
    }

    #[test]
    fn loads_only_on_matching_fingerprint() {
        let bytes = serialize("goodfp", &sample_prog()).unwrap();
        // Matching fingerprint → loads.
        assert!(deserialize_if_fingerprint(&bytes, "goodfp").is_some());
        // Stale/foreign fingerprint → rejected, no decode.
        assert!(deserialize_if_fingerprint(&bytes, "otherfp").is_none());
    }

    #[test]
    fn corrupt_or_truncated_cache_is_rejected_not_paniced() {
        let bytes = serialize("fp", &sample_prog()).unwrap();
        // Truncated at every length: never panics, always None/Err.
        for cut in 0..bytes.len() {
            let head = &bytes[..cut];
            assert!(deserialize_if_fingerprint(head, "fp").is_none());
            assert!(deserialize(head).is_err() || cut == bytes.len());
        }
        // Body bit-flip (header intact): decode must not panic (mis-decode is fine).
        let mut flipped = bytes.clone();
        *flipped.last_mut().unwrap() ^= 0xFF;
        let _ = deserialize_if_fingerprint(&flipped, "fp"); // must not panic
        // Wrong magic → rejected.
        assert!(deserialize_if_fingerprint(b"NOPEnot-a-cache", "fp").is_none());
        assert!(deserialize_if_fingerprint(&[], "fp").is_none());
    }
}
