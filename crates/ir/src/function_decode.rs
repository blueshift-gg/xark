//! Decoder for the DAG-compact `XBC` circuit artifact (container version 2, what
//! `xark-frontend` writes; version 1 came from the removed MIR frontend and is
//! rejected).
//!
//! After the signature inputs: a constant pool (constant tags `0` = small int,
//! `2` = binary big constant, `3` = pool index, `4`/`5` = ±2^k); var lists and LC
//! term vars zigzag-delta-coded. Item tags: `0` a row / witness op, `5` a CALL
//! (delta-coded plugs), `6` a rolled CALL block, `7` a rolled run (varint
//! integers, constants pooled), `8` a row / witness op whose LCs may be `6` + an
//! index into the scope's table of row LCs, and in a witness stream `4` (the
//! next CALLs of the scope's constraint stream). Template bodies may contain
//! CALLs (nested templates).
//!
//! Decode half of `xark-frontend`'s `build_function_blob` (`output.rs`); lives in `xark-ir` so both the
//! `xark` CLI and the compiler can reach it. Parses the container (function defs +
//! top-level streams) and expands it to a full [`CircuitProgram`]. Wire format is defined jointly with the encoder; both
//! must move together.

use crate::circuit::{CircuitProgram, R1csRow};
use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, Term, VarId};
use crate::primitive::{FieldSpec, Var, VarRole, WitnessGen};
use std::collections::BTreeMap;

// Low-level readers (mirror the encoder's `put_*`).
fn get_uv(b: &[u8], p: &mut usize) -> u64 {
    let mut v = 0u64;
    let mut s = 0;
    loop {
        let byte = b[*p];
        *p += 1;
        v |= u64::from(byte & 0x7f) << s;
        if byte & 0x80 == 0 {
            break;
        }
        s += 7;
    }
    v
}
fn get_iv(b: &[u8], p: &mut usize) -> i64 {
    let u = get_uv(b, p);
    ((u >> 1) as i64) ^ -((u & 1) as i64)
}
/// A count of things that follow at `*p`, each encoded in at least `min_width`
/// bytes. Panics (a malformed artifact) when they can't fit in the bytes left, so
/// a hostile count is caught before it sizes an allocation.
fn get_len(b: &[u8], p: &mut usize, min_width: u64) -> usize {
    let n = get_uv(b, p);
    let left = b.len().saturating_sub(*p) as u64;
    assert!(
        n.checked_mul(min_width).is_some_and(|w| w <= left),
        "count {n} overruns the artifact"
    );
    n as usize
}

/// The most an artifact may declare or expand to: 2^30 variables, and 2^30 rows,
/// witness ops and template calls in all (what parsing materializes and what
/// expanding walks are each held to it). Groth16 over BN254 keys at most 2^28 rows
/// (the scalar field's two-adicity bounds the FFT domain) and the largest examples
/// are under 2^23, so this rejects only artifacts no prover could use, while
/// keeping a few hostile bytes from asking for an unbounded walk or allocation.
const SIZE_CAP: u64 = 1 << 30;

thread_local! {
    /// What parsing the current artifact has materialized so far (rolled calls,
    /// rolled-run ops), against [`SIZE_CAP`].
    static SPENT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Charge `n` items parsing is about to materialize.
fn charge(n: u64) {
    SPENT.with(|s| {
        let total = s.get().saturating_add(n);
        assert!(total <= SIZE_CAP, "the artifact expands past the size cap");
        s.set(total);
    });
}

/// A rolled run (item tag `7`), expanded, its cost charged.
fn rolled_run(blob: &[u8]) -> (Vec<R1csRow>, Vec<WitnessGen>) {
    let mut left = SIZE_CAP - SPENT.with(std::cell::Cell::get);
    let out = crate::bytecode::decode_and_expand_ops_compact(blob, &pool(), &mut left)
        .unwrap_or_else(|e| panic!("bad rolled run: {e}"));
    SPENT.with(|s| s.set(SIZE_CAP - left));
    out
}

fn get_fc(b: &[u8], p: &mut usize) -> FieldConst {
    let tag = b[*p];
    *p += 1;
    match tag {
        0 => FieldConst::from_i64(get_iv(b, p)),
        // A big constant as sign (1 = +, 2 = −) + length + LE magnitude.
        2 => {
            let sign = match b[*p] {
                1 => num_bigint::Sign::Plus,
                2 => num_bigint::Sign::Minus,
                t => panic!("bad constant sign {t}"),
            };
            *p += 1;
            let n = get_len(b, p, 1);
            let v = num_bigint::BigInt::from_bytes_le(sign, &b[*p..*p + n]);
            *p += n;
            FieldConst::from_bigint(v)
        }
        // An entry of the container's constant pool.
        3 => {
            let i = get_uv(b, p) as usize;
            POOL.with(|pool| pool.borrow()[i].clone())
        }
        // ±2^k.
        4 | 5 => {
            let k = get_uv(b, p);
            assert!(k < 4096, "bad exponent");
            if k < 63 {
                let v = 1i64 << k;
                return FieldConst::from_i64(if tag == 5 { -v } else { v });
            }
            let v = num_bigint::BigInt::from(1) << k;
            FieldConst::from_bigint(if tag == 5 { -v } else { v })
        }
        t => panic!("bad constant tag {t}"),
    }
}
/// A var id in an LC or id list: a zigzag delta from the previous one in the
/// same list.
fn get_var(b: &[u8], p: &mut usize, prev: &mut i64) -> u32 {
    *prev += get_iv(b, p);
    *prev as u32
}
fn get_lc(b: &[u8], p: &mut usize) -> LinearCombination {
    let constant = get_fc(b, p);
    let n = get_len(b, p, 1);
    let mut terms = Vec::with_capacity(n.min(1 << 20));
    let mut prev = 0i64;
    for _ in 0..n {
        let coeff = get_fc(b, p);
        let var = get_var(b, p, &mut prev);
        terms.push(Term { coeff, var });
    }
    LinearCombination { constant, terms }
}
fn get_ids(b: &[u8], p: &mut usize) -> Vec<VarId> {
    let n = get_len(b, p, 1);
    let mut prev = 0i64;
    (0..n).map(|_| get_var(b, p, &mut prev)).collect()
}
fn get_str(b: &[u8], p: &mut usize) -> String {
    let n = get_len(b, p, 1);
    let s = std::str::from_utf8(&b[*p..*p + n]).unwrap().to_string();
    *p += n;
    s
}
fn byte_role(b: u8) -> VarRole {
    match b {
        0 => VarRole::PublicInput,
        1 => VarRole::PrivateInput,
        _ => VarRole::Derived,
    }
}
fn get_witness(b: &[u8], p: &mut usize) -> WitnessGen {
    get_witness_with(b, p, &mut get_lc)
}
/// [`get_witness`] with every LC read by `lc` (a back-reference reader for tag
/// `8` ops).
fn get_witness_with(
    b: &[u8],
    p: &mut usize,
    lc: &mut dyn FnMut(&[u8], &mut usize) -> LinearCombination,
) -> WitnessGen {
    let lcs =
        |b: &[u8], p: &mut usize, lc: &mut dyn FnMut(&[u8], &mut usize) -> LinearCombination| {
            let n = get_len(b, p, 1);
            (0..n).map(|_| lc(b, p)).collect::<Vec<_>>()
        };
    let tag = b[*p];
    *p += 1;
    match tag {
        0 => WitnessGen::Product {
            out: get_uv(b, p) as u32,
            left: lc(b, p),
            right: lc(b, p),
        },
        1 => WitnessGen::Linear {
            out: get_uv(b, p) as u32,
            lc: lc(b, p),
        },
        2 => WitnessGen::Xor {
            out: get_uv(b, p) as u32,
            a: lc(b, p),
            b: lc(b, p),
        },
        3 => WitnessGen::Or {
            out: get_uv(b, p) as u32,
            a: lc(b, p),
            b: lc(b, p),
        },
        4 => WitnessGen::Inverse {
            out: get_uv(b, p) as u32,
            input: lc(b, p),
        },
        5 => WitnessGen::InverseOrZero {
            out: get_uv(b, p) as u32,
            input: lc(b, p),
        },
        6 => WitnessGen::Bit {
            out: get_uv(b, p) as u32,
            input: lc(b, p),
            index: get_uv(b, p) as u32,
        },
        7 => WitnessGen::Bits {
            outs: get_ids(b, p),
            input: lc(b, p),
        },
        8 => WitnessGen::DivRem {
            q: get_uv(b, p) as u32,
            r: get_uv(b, p) as u32,
            num: lc(b, p),
            den: lc(b, p),
        },
        9 => WitnessGen::MulModDivMod {
            q: get_ids(b, p),
            r: get_ids(b, p),
            a: lcs(b, p, lc),
            b: lcs(b, p, lc),
            modulus: lcs(b, p, lc),
            limb_bits: get_uv(b, p) as u32,
        },
        10 => WitnessGen::ModInverse {
            out: get_ids(b, p),
            a: lcs(b, p, lc),
            modulus: lcs(b, p, lc),
            limb_bits: get_uv(b, p) as u32,
        },
        12 => WitnessGen::FakeGlv {
            out: get_ids(b, p),
            u: lcs(b, p, lc),
            modulus: lcs(b, p, lc),
            lambda: lcs(b, p, lc),
            limb_bits: get_uv(b, p) as u32,
        },
        11 => WitnessGen::Sub2 {
            qabs: get_uv(b, p) as u32,
            r: get_ids(b, p),
            a: lcs(b, p, lc),
            b: lcs(b, p, lc),
            c: lcs(b, p, lc),
            modulus: lcs(b, p, lc),
            limb_bits: get_uv(b, p) as u32,
        },
        _ => unreachable!("bad witness tag {tag}"),
    }
}

/// Primary output var of a witness op;
/// decides whether the op survives the var prune.
fn witness_out(op: &WitnessGen) -> VarId {
    match op {
        WitnessGen::Product { out, .. }
        | WitnessGen::Linear { out, .. }
        | WitnessGen::Xor { out, .. }
        | WitnessGen::Or { out, .. }
        | WitnessGen::Inverse { out, .. }
        | WitnessGen::InverseOrZero { out, .. }
        | WitnessGen::Bit { out, .. } => *out,
        WitnessGen::Bits { outs, .. } => *outs.first().unwrap_or(&0),
        WitnessGen::DivRem { q, .. } => *q,
        WitnessGen::MulModDivMod { q, r, .. } => *q.first().or_else(|| r.first()).unwrap_or(&0),
        WitnessGen::ModInverse { out, .. } | WitnessGen::FakeGlv { out, .. } => {
            *out.first().unwrap_or(&0)
        }
        WitnessGen::Sub2 { qabs, .. } => *qabs,
    }
}

// Substitution: internals shift base+offset; plug vars map to plug LCs.
/// Substitute an LC under `s`: each term `coeff·var` becomes `coeff · s(var)`.
/// Mirrors the encoder's substitution (`xark-frontend`'s `subst_witness_vars`), so a bytecode CALL expands
/// byte-identically to a walked replay.
/// A variable substitution: the identity (top level), or a template call's —
/// the def's fresh internals shifted to the call's `base`, its plugs replaced by
/// the caller's expressions, anything else (globals) unchanged.
struct Subst {
    dbase: u32,
    base: u32,
    /// `(plug var, caller expression)`, sorted by var.
    plugs: Vec<(u32, LinearCombination)>,
    identity: bool,
}

/// Where a substitution sends one variable.
enum Image<'a> {
    Var(u32),
    Lc(&'a LinearCombination),
}

/// Top-level (identity) substitution. A `static` so it is `Send + Sync` and can
/// be handed to rayon workers during parallel expansion.
static IDENTITY: Subst = Subst {
    dbase: 0,
    base: 0,
    plugs: Vec::new(),
    identity: true,
};

impl Subst {
    fn get(&self, v: u32) -> Image<'_> {
        if self.identity {
            Image::Var(v)
        } else if v >= self.dbase {
            Image::Var(self.base + (v - self.dbase))
        } else if let Ok(i) = self.plugs.binary_search_by_key(&v, |p| p.0) {
            Image::Lc(&self.plugs[i].1)
        } else {
            Image::Var(v)
        }
    }
}

/// `lc` under `s`. Terms are written straight into one vector and simplified
/// once; coefficients are exact integers, so the result is the same as
/// substituting and simplifying term by term.
fn subst_lc(lc: &LinearCombination, s: &Subst) -> LinearCombination {
    let mut constant = lc.constant.clone();
    let mut terms: Vec<Term> = Vec::with_capacity(lc.terms.len());
    for t in &lc.terms {
        match s.get(t.var) {
            Image::Var(v) => terms.push(Term {
                coeff: t.coeff.clone(),
                var: v,
            }),
            Image::Lc(p) => {
                if !p.constant.is_zero() {
                    constant = constant.add(&p.constant.mul(&t.coeff));
                }
                terms.extend(p.terms.iter().map(|pt| Term {
                    coeff: pt.coeff.mul(&t.coeff),
                    var: pt.var,
                }));
            }
        }
    }
    LinearCombination { constant, terms }.simplified()
}
/// The single var an out/id witness field maps to. Out/id fields are always fresh
/// internals, so `s` maps them to a bare var. (Invariant relied on here.)
fn subst_out(v: u32, s: &Subst) -> u32 {
    match s.get(v) {
        Image::Var(v) => v,
        Image::Lc(p) => p.terms[0].var,
    }
}
/// `w` under `s`.
fn subst_witness(w: &WitnessGen, s: &Subst) -> WitnessGen {
    w.map(|l| subst_lc(l, s), |&v| subst_out(v, s))
}

/// Build the substitution for a CALL: plug var → caller's (already
/// outer-substituted) plug LC; internal var (`>= def.base_var`) → shifted single
/// var at `base`; anything else → itself.
fn call_subst(def: &GDef, base: u32, plugs: Vec<LinearCombination>) -> Subst {
    let mut plugs: Vec<(u32, LinearCombination)> = def.plugs.iter().copied().zip(plugs).collect();
    // Sorted for lookup; a repeated plug var keeps its last expression (as the
    // map this replaced did).
    plugs.reverse();
    plugs.sort_by_key(|p| p.0);
    plugs.dedup_by_key(|p| p.0);
    Subst {
        dbase: def.base_var,
        base,
        plugs,
        identity: false,
    }
}

// Parsed items.
enum CItem {
    Row(R1csRow),
    /// `(def index, fresh var base, plug LCs)`. Plug LCs are in the enclosing
    /// scope's coords, substituted into the def body on expand.
    Call(u32, u32, Vec<LinearCombination>),
    /// A rolled run of ≥2 inline rows, in the def's own coords (remapped at
    /// expansion like an inline `Row`).
    Rolled(Vec<R1csRow>),
}
enum WItem {
    Row(WitnessGen),
    Call(u32, u32, Vec<LinearCombination>),
    /// A rolled run of ≥2 witness ops.
    Rolled(Vec<WitnessGen>),
}
struct GDef {
    base_var: u32,
    plugs: Vec<u32>,
    outputs: Vec<u32>,
    c_items: Vec<CItem>,
    w_items: Vec<WItem>,
}
/// A CALL's plug LCs, version-2 form (tag `5`): each plug is a varint header —
/// even: a bare variable (`1·v`), `v` = previous bare plug (initially `base`) +
/// zigzag(header / 2); `1`: a general LC follows.
fn get_plugs_compact(b: &[u8], p: &mut usize, base: u32) -> Vec<LinearCombination> {
    let n = get_len(b, p, 1);
    let mut prev = i64::from(base);
    let mut out = Vec::with_capacity(n.min(1 << 20));
    for _ in 0..n {
        let h = get_uv(b, p);
        if h & 1 == 0 {
            let u = h >> 1;
            prev += ((u >> 1) as i64) ^ -((u & 1) as i64);
            out.push(LinearCombination::var(prev as u32));
        } else {
            out.push(get_lc(b, p));
        }
    }
    out
}
/// Version-2 rolled-CALL block (tag `6`): [`parse_rolled_calls`] with bare-var
/// plugs delta-coded as in [`get_plugs_compact`] (each followed by its step).
fn parse_rolled_calls_compact(b: &[u8], p: &mut usize) -> Vec<(u32, u32, Vec<LinearCombination>)> {
    let count = get_uv(b, p) as i64;
    let period = get_len(b, p, 1);
    #[allow(clippy::type_complexity)]
    let mut body: Vec<(
        u32,
        i64,
        i64,
        Vec<(FieldConst, Vec<(FieldConst, i64, i64)>)>,
    )> = Vec::with_capacity(period.min(1 << 20));
    for _ in 0..period {
        let def = get_uv(b, p) as u32;
        let base0 = get_uv(b, p) as i64;
        let base_step = get_iv(b, p);
        let nplugs = get_len(b, p, 1);
        let mut prev = base0;
        let mut plugs = Vec::with_capacity(nplugs.min(1 << 20));
        for _ in 0..nplugs {
            let h = get_uv(b, p);
            if h & 1 == 0 {
                let u = h >> 1;
                prev += ((u >> 1) as i64) ^ -((u & 1) as i64);
                let step = get_iv(b, p);
                plugs.push((FieldConst::zero(), vec![(FieldConst::one(), prev, step)]));
            } else {
                let constant = get_fc(b, p);
                let nterms = get_len(b, p, 1);
                let mut terms = Vec::with_capacity(nterms.min(1 << 20));
                for _ in 0..nterms {
                    let coeff = get_fc(b, p);
                    let var0 = get_uv(b, p) as i64;
                    let step = get_iv(b, p);
                    terms.push((coeff, var0, step));
                }
                plugs.push((constant, terms));
            }
        }
        body.push((def, base0, base_step, plugs));
    }
    // The block repeats its body `count` times: bounded by the cap, not the bytes.
    // An empty body still costs the loop its iterations.
    charge((count.max(0) as u64).saturating_mul(period.max(1) as u64));
    let mut out = Vec::with_capacity((count.max(0) as usize).saturating_mul(period).min(1 << 20));
    for k in 0..count {
        for (def, base0, base_step, plugs) in &body {
            let lcs = plugs
                .iter()
                .map(|(c, terms)| LinearCombination {
                    constant: c.clone(),
                    terms: terms
                        .iter()
                        .map(|(coeff, var0, step)| Term {
                            coeff: coeff.clone(),
                            var: (var0 + k * step) as u32,
                        })
                        .collect(),
                })
                .collect();
            out.push((*def, (base0 + k * base_step) as u32, lcs));
        }
    }
    out
}
/// A scope's row LCs of ≥ 2 terms, in stream order (version 2): what a tag-`8`
/// row or witness op refers back to (`6` + index in place of an LC). An entry
/// names the LC by position — `item` in the parsed stream (`PENDING`: the row
/// being parsed), `sub` row of a rolled item, `which` of a/b/c — so the table
/// costs no LC copies.
#[derive(Clone, Copy)]
struct LcRef {
    item: u32,
    sub: u32,
    which: u8,
}
const PENDING: u32 = u32::MAX;

fn row_lc(r: &R1csRow, which: u8) -> &LinearCombination {
    match which {
        0 => &r.a,
        1 => &r.b,
        _ => &r.c,
    }
}
fn resolve_ref(items: &[CItem], e: LcRef) -> &LinearCombination {
    match &items[e.item as usize] {
        CItem::Row(r) => row_lc(r, e.which),
        CItem::Rolled(rows) => row_lc(&rows[e.sub as usize], e.which),
        CItem::Call(..) => panic!("LC reference to a call"),
    }
}
/// Append the table entries of the last parsed item (rows only).
fn push_refs(items: &[CItem], table: &mut Vec<LcRef>) {
    let item = items.len() - 1;
    let rows: &[R1csRow] = match &items[item] {
        CItem::Row(r) => std::slice::from_ref(r),
        CItem::Rolled(rows) => rows,
        CItem::Call(..) => return,
    };
    for (sub, r) in rows.iter().enumerate() {
        for which in 0..3u8 {
            if row_lc(r, which).terms.len() >= 2 {
                table.push(LcRef {
                    item: item as u32,
                    sub: sub as u32,
                    which,
                });
            }
        }
    }
}

/// Parse a constraint item stream and its LC table.
fn parse_c_items(b: &[u8], p: &mut usize) -> (Vec<CItem>, Vec<LcRef>) {
    let n = get_len(b, p, 1);
    let mut out = Vec::with_capacity(n.min(1 << 20));
    let mut table: Vec<LcRef> = Vec::new();
    for _ in 0..n {
        let tag = b[*p];
        *p += 1;
        if tag == 8 {
            {
                // A row whose LCs may be references (`6` + index), possibly to
                // this row's own earlier LCs.
                let mut lcs: [LinearCombination; 3] =
                    std::array::from_fn(|_| LinearCombination::zero());
                let first = table.len();
                for which in 0..3u8 {
                    let l = if b[*p] == 6 {
                        *p += 1;
                        let e = table[get_uv(b, p) as usize];
                        if e.item == PENDING {
                            lcs[e.which as usize].clone()
                        } else {
                            resolve_ref(&out, e).clone()
                        }
                    } else {
                        get_lc(b, p)
                    };
                    if l.terms.len() >= 2 {
                        table.push(LcRef {
                            item: PENDING,
                            sub: 0,
                            which,
                        });
                    }
                    lcs[which as usize] = l;
                }
                for e in &mut table[first..] {
                    e.item = out.len() as u32;
                }
                let [a, bb, c] = lcs;
                out.push(CItem::Row(R1csRow {
                    a,
                    b: bb,
                    c,
                    note: None,
                }));
                continue;
            }
        }
        match tag {
            0 => out.push(CItem::Row(R1csRow {
                a: get_lc(b, p),
                b: get_lc(b, p),
                c: get_lc(b, p),
                note: None,
            })),
            5 => {
                let d = get_uv(b, p) as u32;
                let base = get_uv(b, p) as u32;
                out.push(CItem::Call(d, base, get_plugs_compact(b, p, base)));
            }
            6 => {
                for (d, base, plugs) in parse_rolled_calls_compact(b, p) {
                    out.push(CItem::Call(d, base, plugs));
                }
            }
            7 => {
                let len = get_len(b, p, 1);
                let blob = &b[*p..*p + len];
                *p += len;
                out.push(CItem::Rolled(rolled_run(blob).0));
            }
            t => panic!("bad constraint item tag {t}"),
        }
        push_refs(&out, &mut table);
    }
    (out, table)
}
/// Parse a witness item stream. `c_items` is the same scope's constraint stream:
/// a tag `4` reuses its CALLs (in order) instead of repeating them.
fn parse_w_items(b: &[u8], p: &mut usize, c_items: &[CItem], table: &[LcRef]) -> Vec<WItem> {
    let n = get_len(b, p, 1);
    let mut out = Vec::with_capacity(n.min(1 << 20));
    let mut c_calls = c_items.iter().filter_map(|it| match it {
        CItem::Call(d, base, plugs) => Some((*d, *base, plugs)),
        _ => None,
    });
    for _ in 0..n {
        let tag = b[*p];
        *p += 1;
        match tag {
            0 => out.push(WItem::Row(get_witness(b, p))),
            8 => out.push(WItem::Row(get_witness_with(b, p, &mut |b, p| {
                if b[*p] == 6 {
                    *p += 1;
                    resolve_ref(c_items, table[get_uv(b, p) as usize]).clone()
                } else {
                    get_lc(b, p)
                }
            }))),
            4 => {
                let skip = get_uv(b, p) as usize;
                let n = get_uv(b, p) as usize;
                if skip > 0 {
                    c_calls.nth(skip - 1);
                }
                for _ in 0..n {
                    let (d, base, plugs) = c_calls.next().expect("CALL reference in range");
                    out.push(WItem::Call(d, base, plugs.clone()));
                }
            }
            5 => {
                let d = get_uv(b, p) as u32;
                let base = get_uv(b, p) as u32;
                out.push(WItem::Call(d, base, get_plugs_compact(b, p, base)));
            }
            6 => {
                for (d, base, plugs) in parse_rolled_calls_compact(b, p) {
                    out.push(WItem::Call(d, base, plugs));
                }
            }
            7 => {
                let len = get_len(b, p, 1);
                let blob = &b[*p..*p + len];
                *p += len;
                out.push(WItem::Rolled(rolled_run(blob).1));
            }
            t => panic!("bad witness item tag {t}"),
        }
    }
    out
}

/// Expand the top-level constraint stream, optionally in parallel.
///
/// The top-level substitution is the identity and every item's var ids are already
/// absolute (baked in by the encoder's monotonic walk), so items share no running
/// counter and are independent: expanding each into a local buffer and concatenating
/// them in item order is byte-for-byte the serial walk's output. That is what makes
/// the rayon fan-out sound.
fn expand_c_top(defs: &[GDef], items: &[CItem], parallel: bool) -> Vec<R1csRow> {
    if parallel {
        use rayon::prelude::*;
        let chunks: Vec<Vec<R1csRow>> = items
            .par_iter()
            .map(|it| {
                let mut buf = Vec::new();
                expand_c(defs, std::slice::from_ref(it), &IDENTITY, &mut buf);
                buf
            })
            .collect();
        let mut out = Vec::with_capacity(chunks.iter().map(Vec::len).sum());
        for c in chunks {
            out.extend(c);
        }
        out
    } else {
        let mut out = Vec::new();
        expand_c(defs, items, &IDENTITY, &mut out);
        out
    }
}

/// Witness-stream counterpart of [`expand_c_top`] — same independence argument
/// (absolute out/id vars, identity-substituted input LCs), so parallel expansion
/// concatenated in order equals the serial walk.
fn expand_w_top(defs: &[GDef], items: &[WItem], parallel: bool) -> Vec<WitnessGen> {
    if parallel {
        use rayon::prelude::*;
        let chunks: Vec<Vec<WitnessGen>> = items
            .par_iter()
            .map(|it| {
                let mut buf = Vec::new();
                expand_w(defs, std::slice::from_ref(it), &IDENTITY, &mut buf);
                buf
            })
            .collect();
        let mut out = Vec::with_capacity(chunks.iter().map(Vec::len).sum());
        for c in chunks {
            out.extend(c);
        }
        out
    } else {
        let mut out = Vec::new();
        expand_w(defs, items, &IDENTITY, &mut out);
        out
    }
}

/// Streaming twin of [`expand_c`]: emits each expanded R1CS row to `emit`
/// instead of collecting into a `Vec`, so a consumer never materializes the flat
/// system.
fn expand_c_visit(defs: &[GDef], items: &[CItem], subst: &Subst, emit: &mut dyn FnMut(R1csRow)) {
    for it in items {
        match it {
            CItem::Row(r) => emit(R1csRow {
                a: subst_lc(&r.a, subst),
                b: subst_lc(&r.b, subst),
                c: subst_lc(&r.c, subst),
                note: None,
            }),
            CItem::Rolled(rows) => {
                for r in rows {
                    emit(R1csRow {
                        a: subst_lc(&r.a, subst),
                        b: subst_lc(&r.b, subst),
                        c: subst_lc(&r.c, subst),
                        note: None,
                    });
                }
            }
            CItem::Call(d, base, plugs) => {
                let def = &defs[*d as usize];
                let base = subst_out(*base, subst);
                let sub_plugs: Vec<LinearCombination> =
                    plugs.iter().map(|lc| subst_lc(lc, subst)).collect();
                let sub = call_subst(def, base, sub_plugs);
                expand_c_visit(defs, &def.c_items, &sub, emit);
            }
        }
    }
}

/// Decode a function blob to the **compact** form (header + templates + top-level
/// items) without expanding the constraint stream. Mirrors the front of
/// `expand_function_blob_inner`, minus `expand_c_top` and the global prune.
type CompactDecoded = (
    FieldSpec,
    Vec<Var>,
    Vec<GDef>,
    Vec<CItem>,
    Vec<WItem>,
    std::collections::BTreeSet<u32>,
    usize, // num_inputs (leading input vars; used by the var prune)
);

/// The compact form without a per-variable table: only the signature inputs get a
/// `Var` (role + name); every other variable is `Derived` and unnamed. What
/// streaming consumers need — a full table costs ~60 B × millions of vars.
struct CompactCore {
    field: FieldSpec,
    num_vars: usize,
    inputs: Vec<Var>,
    defs: Vec<GDef>,
    top_c: Vec<CItem>,
    top_w: Vec<WItem>,
    keep_extra: std::collections::BTreeSet<u32>,
}

/// The field a circuit artifact was built for (its header's name and modulus), or
/// `None` if `b` isn't one.
pub fn stream_field(b: &[u8]) -> Option<FieldSpec> {
    if b.len() < 6 || b[..4] != crate::bytecode::MAGIC {
        return None;
    }
    catch_quietly(|| decode_header(b).0).ok()
}

/// Parse the header through the signature inputs; returns the cursor after them.
fn decode_header(b: &[u8]) -> (FieldSpec, usize, Vec<Var>, usize) {
    let mut p = 6usize;
    let name = get_str(b, &mut p);
    let modulus_decimal = get_str(b, &mut p);
    let num_vars = get_uv(b, &mut p);
    assert!(
        num_vars <= SIZE_CAP,
        "{num_vars} variables is past the size cap"
    );
    let num_vars = num_vars as usize;
    // Each input is a role byte and a name (at least its length byte).
    let num_inputs = get_len(b, &mut p, 2);
    assert!(num_inputs <= num_vars, "more inputs than variables");
    let mut inputs = Vec::with_capacity(num_inputs);
    for id in 0..num_inputs {
        let role = byte_role(b[p]);
        p += 1;
        inputs.push(Var {
            id: id as u32,
            name: get_str(b, &mut p),
            role,
        });
    }
    (
        FieldSpec {
            name,
            modulus_decimal,
        },
        num_vars,
        inputs,
        p,
    )
}

thread_local! {
    /// The container's constant pool while its body is being parsed.
    static POOL: std::cell::RefCell<std::rc::Rc<Vec<FieldConst>>> =
        std::cell::RefCell::new(std::rc::Rc::new(Vec::new()));
}

/// The pool `get_fc` resolves tag-3 references against.
fn pool() -> std::rc::Rc<Vec<FieldConst>> {
    POOL.with(|p| p.borrow().clone())
}

/// Everything after the header's signature inputs: the constant pool,
/// the function defs, the top-level streams and the keep-set exceptions.
#[allow(clippy::type_complexity)]
fn parse_body(
    b: &[u8],
    mut p: usize,
) -> (
    Vec<GDef>,
    Vec<CItem>,
    Vec<WItem>,
    std::collections::BTreeSet<u32>,
) {
    let version = u16::from_le_bytes([b[4], b[5]]);
    assert_eq!(version, 2, "unsupported XBC container version {version}");
    let n = get_len(b, &mut p, 1);
    let pool: Vec<FieldConst> = (0..n).map(|_| get_fc(b, &mut p)).collect();
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            POOL.with(|p| *p.borrow_mut() = std::rc::Rc::new(Vec::new()));
            SPENT.with(|s| s.set(0));
        }
    }
    POOL.with(|p| *p.borrow_mut() = std::rc::Rc::new(pool));
    SPENT.with(|s| s.set(0));
    let _reset = Reset;
    let n_defs = get_len(b, &mut p, 1);
    let mut defs = Vec::with_capacity(n_defs.min(1 << 20));
    for _ in 0..n_defs {
        let base_var = get_uv(b, &mut p) as u32;
        let plugs = get_ids(b, &mut p);
        let outputs = get_ids(b, &mut p);
        let (c_items, table) = parse_c_items(b, &mut p);
        let w_items = parse_w_items(b, &mut p, &c_items, &table);
        defs.push(GDef {
            base_var,
            plugs,
            outputs,
            c_items,
            w_items,
        });
    }
    let (top_c, table) = parse_c_items(b, &mut p);
    let top_w = parse_w_items(b, &mut p, &top_c, &table);
    let keep_extra: std::collections::BTreeSet<u32> = get_ids(b, &mut p).into_iter().collect();
    check_calls(&defs, &top_c, &top_w);
    (defs, top_c, top_w, keep_extra)
}

/// Reject a template call graph the expanders can't walk, before anything walks
/// it: a call to a missing template, a cycle (expansion would recurse until the
/// stack overflows, which aborts rather than unwinds), or nesting that expands
/// past [`SIZE_CAP`] (template `k` calling `k - 1` twice, 40 deep, is a few
/// hundred bytes and 2^40 rows). Templates call each other in either index order
/// in real artifacts, so the order comes from a topological sort (Kahn's), callees
/// first; each template's cost is then its own items plus its callees' costs.
fn check_calls(defs: &[GDef], top_c: &[CItem], top_w: &[WItem]) {
    let n = defs.len();
    let c_calls = |items: &[CItem]| -> Vec<u32> {
        items
            .iter()
            .filter_map(|it| match it {
                CItem::Call(d, ..) => Some(*d),
                _ => None,
            })
            .collect()
    };
    let w_calls = |items: &[WItem]| -> Vec<u32> {
        items
            .iter()
            .filter_map(|it| match it {
                WItem::Call(d, ..) => Some(*d),
                _ => None,
            })
            .collect()
    };
    for d in c_calls(top_c).into_iter().chain(w_calls(top_w)) {
        assert!((d as usize) < n, "a call to missing template {d}");
    }
    // Per template: its calls not yet costed; per callee: its callers, once per call.
    let mut pending = vec![0usize; n];
    let mut callers: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, def) in defs.iter().enumerate() {
        for d in c_calls(&def.c_items)
            .into_iter()
            .chain(w_calls(&def.w_items))
        {
            assert!((d as usize) < n, "a call to missing template {d}");
            pending[i] += 1;
            callers[d as usize].push(i);
        }
    }
    // The rows (or ops) and calls a stream expands to, saturating past the cap. An
    // empty rolled run still costs its item.
    let c_cost = |items: &[CItem], cost: &[(u64, u64)]| -> u64 {
        items.iter().fold(0u64, |acc, it| {
            acc.saturating_add(match it {
                CItem::Row(_) => 1,
                CItem::Rolled(rows) => rows.len().max(1) as u64,
                CItem::Call(d, ..) => cost[*d as usize].0.saturating_add(1),
            })
        })
    };
    let w_cost = |items: &[WItem], cost: &[(u64, u64)]| -> u64 {
        items.iter().fold(0u64, |acc, it| {
            acc.saturating_add(match it {
                WItem::Row(_) => 1,
                WItem::Rolled(ops) => ops.len().max(1) as u64,
                WItem::Call(d, ..) => cost[*d as usize].1.saturating_add(1),
            })
        })
    };
    let mut cost = vec![(0u64, 0u64); n];
    let mut ready: Vec<usize> = (0..n).filter(|&i| pending[i] == 0).collect();
    let mut costed = 0;
    while let Some(d) = ready.pop() {
        cost[d] = (
            c_cost(&defs[d].c_items, &cost),
            w_cost(&defs[d].w_items, &cost),
        );
        costed += 1;
        for &i in &callers[d] {
            pending[i] -= 1;
            if pending[i] == 0 {
                ready.push(i);
            }
        }
    }
    assert!(costed == n, "template calls form a cycle");
    let total = c_cost(top_c, &cost).saturating_add(w_cost(top_w, &cost));
    assert!(total <= SIZE_CAP, "the artifact expands past the size cap");
}

fn decode_core(b: &[u8]) -> CompactCore {
    let (field, num_vars, inputs, p) = decode_header(b);
    let (defs, top_c, top_w, keep_extra) = parse_body(b, p);
    CompactCore {
        field,
        num_vars,
        inputs,
        defs,
        top_c,
        top_w,
        keep_extra,
    }
}

fn decode_compact(b: &[u8]) -> CompactDecoded {
    let c = decode_core(b);
    let num_inputs = c.inputs.len();
    let mut inputs = c.inputs.into_iter();
    let vars = (0..c.num_vars)
        .map(|id| match inputs.next() {
            Some(v) => v,
            None => Var {
                id: id as u32,
                name: format!("v{id}"),
                role: VarRole::Derived,
            },
        })
        .collect();
    (
        c.field,
        vars,
        c.defs,
        c.top_c,
        c.top_w,
        c.keep_extra,
        num_inputs,
    )
}

/// Just the signature inputs (role + name), from the header alone — what input
/// resolution needs, without decoding templates or a table of every variable. A
/// malformed header is an `Err`.
pub fn decode_input_vars(b: &[u8]) -> Result<Vec<Var>, String> {
    catch_quietly(|| decode_header(b).2)
        .map_err(|()| "malformed function artifact (XBC header decode failed)".to_string())
}

/// [`stream_solve`] returning the solver's dense slots (`slots[id]`) instead of a
/// map — no per-variable map nodes, for provers that read every value once.
pub fn stream_solve_dense(
    b: &[u8],
    inputs: &std::collections::BTreeMap<u32, String>,
) -> Result<Vec<Option<crate::solver::Fp>>, String> {
    let c = decode_core(b);
    let modulus = num_bigint::BigUint::parse_bytes(c.field.modulus_decimal.as_bytes(), 10)
        .ok_or_else(|| "bad modulus".to_string())?;
    let slots = solve_streamed(&c.inputs, c.num_vars, &c.defs, &c.top_w, &modulus, inputs);
    // Freeing the decoded program takes a few ms the caller needn't wait for. Where
    // threads can't be spawned (wasm), the unrun closure frees it here instead.
    let _ = std::thread::Builder::new().spawn(move || drop(c));
    slots
}

/// **Streaming constraint check** — solve the witness, then verify every R1CS row
/// by expanding it out of the compact bytecode and evaluating on the fly, so the
/// flat R1CS is *never materialized*. Peak memory is the witness + one row, not
/// the full constraint system. Correctness-equivalent to
/// `solve_and_check(&cp.to_primitive(), inputs)`, minus the two flat copies.
pub fn stream_check(
    b: &[u8],
    inputs: &std::collections::BTreeMap<u32, String>,
) -> Result<(), String> {
    let (field, vars, defs, top_c, top_w, _keep, _num_inputs) = decode_compact(b);
    let modulus = num_bigint::BigUint::parse_bytes(field.modulus_decimal.as_bytes(), 10)
        .ok_or_else(|| "bad modulus".to_string())?;
    let assign = solve_streamed(&vars, vars.len(), &defs, &top_w, &modulus, inputs)?;
    // Each top-level item is an independent constraint shard (absolute var ids),
    // so evaluate them in parallel against the shared read-only assignment,
    // streaming+dropping rows within each shard. Short-circuits on first failure.
    use rayon::prelude::*;
    let ok = top_c.par_iter().all(|item| {
        let mut shard_ok = true;
        expand_c_visit(
            &defs,
            std::slice::from_ref(item),
            &IDENTITY,
            &mut |row: R1csRow| {
                if shard_ok
                    && !crate::solver::row_satisfied(&row.a, &row.b, &row.c, &assign[..], &modulus)
                {
                    shard_ok = false;
                }
            },
        );
        shard_ok
    });
    if ok {
        Ok(())
    } else {
        Err("a constraint is unsatisfied".to_string())
    }
}

/// The first constraint, in build order (the order `sources.json` and `r1cs.json`
/// index), that the solved `slots` (from [`stream_solve_dense`]) don't satisfy.
/// Rows are streamed one at a time; for naming a failure after a prover rejects
/// a witness, whatever order its own rows are in.
pub fn first_failing_row(b: &[u8], slots: &[Option<crate::solver::Fp>]) -> Option<usize> {
    let CompactCore {
        field, defs, top_c, ..
    } = decode_core(b);
    let modulus = num_bigint::BigUint::parse_bytes(field.modulus_decimal.as_bytes(), 10)?;
    let (mut i, mut failed) = (0usize, None);
    expand_c_visit(&defs, &top_c, &IDENTITY, &mut |row: R1csRow| {
        if failed.is_none()
            && !crate::solver::row_satisfied(&row.a, &row.b, &row.c, slots, &modulus)
        {
            failed = Some(i);
        }
        i += 1;
    });
    failed
}

/// **Streaming witness solve** — the assignment only, with no constraint check or
/// analysis: the hint program is expanded op-by-op straight out of the bytecode, so
/// neither the flat program nor the flat R1CS is ever materialized. For a prover
/// that checks satisfaction itself (a Groth16 proof self-verifies).
pub fn stream_solve(
    b: &[u8],
    inputs: &std::collections::BTreeMap<u32, String>,
) -> Result<std::collections::BTreeMap<u32, crate::solver::Fp>, String> {
    let (field, vars, defs, _top_c, top_w, _keep, _num_inputs) = decode_compact(b);
    let modulus = num_bigint::BigUint::parse_bytes(field.modulus_decimal.as_bytes(), 10)
        .ok_or_else(|| "bad modulus".to_string())?;
    solve_streamed(&vars, vars.len(), &defs, &top_w, &modulus, inputs)
        .map(crate::solver::slots_into_map)
}

/// Decode just the variable table (roles + names) from a function blob, without
/// expanding any constraints — cheap input resolution for a streaming check.
pub fn decode_vars(b: &[u8]) -> Vec<Var> {
    decode_compact(b).1
}

/// How many function templates (defs) the container holds: `0` for a circuit
/// with no repeated calls worth templating.
pub fn count_templates(b: &[u8]) -> usize {
    decode_core(b).defs.len()
}

// Per-variable classification flags accumulated by the streaming pass 1.
const F_SEEN: u8 = 1; // some constraint references this var
const F_RESTRICTED: u8 = 2; // some referencing row has a≠0 or b≠0 (var not free)
const F_PINNED: u8 = 4; // some referencing row is linear in the var (a=0, b≠0)

/// Fold one row's contribution into the per-variable classification flags. For
/// each distinct variable the row references, reduce the row to its univariate
/// `A·v² + B·v + C` (fixing all other vars to the witness) and [`note`] it.
fn apply_row_flags(
    row: &R1csRow,
    assign: &[Option<crate::solver::Fp>],
    modulus: &num_bigint::BigUint,
    flags: &[std::sync::atomic::AtomicU8],
    quadratic: &[Quadratic],
) {
    for (v, (a, b, _c)) in crate::solver::univariate_r1cs_row(row, assign, modulus) {
        note(v, a, b, flags, quadratic);
    }
}

/// Pass 1's record of one row's univariate reduction `a·v² + b·v + c` for `v`: OR
/// in `SEEN` always, `RESTRICTED` if `a≠0 ∨ b≠0`, `PINNED` if the row is linear in
/// the var (`a=0 ∧ b≠0`); a quadratic row (`a≠0`) is kept for pass 2. `fetch_or` is
/// commutative, so parallel shards may call this in any order.
fn note(
    v: u32,
    a: crate::solver::Fp,
    b: crate::solver::Fp,
    flags: &[std::sync::atomic::AtomicU8],
    quadratic: &[Quadratic],
) {
    use std::sync::atomic::Ordering;
    let mut bits = F_SEEN;
    if !(a.is_zero() && b.is_zero()) {
        bits |= F_RESTRICTED;
        if a.is_zero() {
            bits |= F_PINNED;
        } else if let Some(q) = quadratic.get(v as usize) {
            let _ = q.set((a, b));
        }
    }
    flags[v as usize].fetch_or(bits, Ordering::Relaxed);
}

/// One row's `(a, b)` with `a ≠ 0` for a var — any of them (the first to land).
type Quadratic = std::sync::OnceLock<(crate::solver::Fp, crate::solver::Fp)>;

/// Streaming pass 1: classify every variable with a **dense flag byte** while
/// (optionally) checking satisfiability, in a single parallel sweep of the
/// compact constraint stream. Returns the flag array (indexed by var id),
/// whether every row `a·b = c` held, and each var's kept quadratic row.
///
/// This is the memory win: instead of storing each row's univariate `(a,b,c)`
/// reduction (3 field elements per var-reference — GBs on a heavy EC circuit),
/// we fold each reference into 3 bits. The verdict is **order-independent**
/// (`pinned` beats everything and the two-valued candidate set is consulted only
/// when a var is never pinned), so the parallel `fetch_or` merge across shards is
/// sound — no need to preserve global row order.
fn classify_and_check(
    defs: &[GDef],
    top_c: &[CItem],
    assign: &[Option<crate::solver::Fp>],
    modulus: &num_bigint::BigUint,
    num_vars: usize,
    check_sat: bool,
    compiled: Option<&eval::Compiled>,
) -> (Vec<std::sync::atomic::AtomicU8>, bool, Vec<Quadratic>) {
    use rayon::prelude::*;
    use std::sync::atomic::AtomicU8;
    let flags: Vec<AtomicU8> = (0..num_vars).map(|_| AtomicU8::new(0)).collect();
    // Only a satisfied witness can use them (see `two_valued_satisfied`).
    let quadratic: Vec<Quadratic> = if check_sat {
        (0..num_vars).map(|_| Quadratic::new()).collect()
    } else {
        Vec::new()
    };
    if let Some(c) = compiled {
        // Over BN254: the rows as the prover's evaluator compiles them (`Fr`
        // coefficients, resolved references), each costing its field operations and
        // nothing else, where building a row allocated three LCs and a map.
        use crate::solver::Fp;
        let z = bn254_values(assign);
        let sat_ok = c
            .top
            .par_iter()
            .map(|item| {
                let mut flag = |v: u32, a: ark_bn254::Fr, b: ark_bn254::Fr, _c: ark_bn254::Fr| {
                    note(v, Fp::Bn254(a), Fp::Bn254(b), &flags, &quadratic);
                };
                eval::classify(c, item, &eval::TOP, &[], &z, &mut Vec::new(), &mut flag)
            })
            .reduce(|| true, |x, y| x && y);
        return (flags, !check_sat || sat_ok, quadratic);
    }
    let sat_ok = top_c
        .par_iter()
        .map(|item| {
            let mut shard_ok = true;
            expand_c_visit(
                defs,
                std::slice::from_ref(item),
                &IDENTITY,
                &mut |row: R1csRow| {
                    if check_sat
                        && shard_ok
                        && !crate::solver::row_satisfied(&row.a, &row.b, &row.c, assign, modulus)
                    {
                        shard_ok = false;
                    }
                    apply_row_flags(&row, assign, modulus, &flags, &quadratic);
                },
            );
            shard_ok
        })
        .reduce(|| true, |x, y| x && y);
    (flags, sat_ok, quadratic)
}

/// The witness as the compiled evaluator reads it: a variable's BN254 value, zero
/// when unassigned (as the generic path treats a missing slot).
fn bn254_values(assign: &[Option<crate::solver::Fp>]) -> impl Fn(u32) -> ark_bn254::Fr + Sync + '_ {
    use ark_ff::Zero;
    move |id: u32| match assign.get(id as usize) {
        Some(Some(crate::solver::Fp::Bn254(v))) => *v,
        _ => ark_bn254::Fr::zero(),
    }
}

/// Streaming pass 2 for a witness not known to satisfy every row: re-stream the
/// constraints, gathering each *suspect* var's univariate `(a,b,c)` reductions,
/// then run the exact flat two-valued test on them. Suspects are vars that
/// survived pass 1 restricted-but-unpinned. Returns the subset that is
/// genuinely two-valued.
fn two_valued_suspects(
    defs: &[GDef],
    top_c: &[CItem],
    assign: &[Option<crate::solver::Fp>],
    modulus: &num_bigint::BigUint,
    suspects: &std::collections::BTreeSet<u32>,
) -> std::collections::BTreeSet<u32> {
    use crate::solver::Fp;
    use rayon::prelude::*;
    // Gather every suspect's referencing rows, in parallel over the shards (a
    // suspect's verdict doesn't depend on the order of its rows). On circuits
    // built from multiplications nearly every derived var is a suspect.
    let mut is_suspect = vec![false; assign.len()];
    for &v in suspects {
        if let Some(s) = is_suspect.get_mut(v as usize) {
            *s = true;
        }
    }
    let suspect = |v: u32| is_suspect.get(v as usize).copied().unwrap_or(false);
    let mut found: Vec<(u32, (Fp, Fp, Fp))> = top_c
        .par_iter()
        .fold(Vec::new, |mut found, item| {
            expand_c_visit(
                defs,
                std::slice::from_ref(item),
                &IDENTITY,
                &mut |row: R1csRow| {
                    let mut terms = row.a.terms.iter().chain(&row.b.terms).chain(&row.c.terms);
                    if !terms.any(|t| suspect(t.var)) {
                        return;
                    }
                    found.extend(
                        crate::solver::univariate_r1cs_row(&row, assign, modulus)
                            .into_iter()
                            .filter(|(v, _)| suspect(*v)),
                    );
                },
            );
            found
        })
        .reduce(Vec::new, |mut a, mut b| {
            a.append(&mut b);
            a
        });
    found.par_sort_by_key(|(v, _)| *v);
    let mut polys: std::collections::BTreeMap<u32, Vec<(Fp, Fp, Fp)>> =
        std::collections::BTreeMap::new();
    for (v, poly) in found {
        polys.entry(v).or_default().push(poly);
    }
    two_valued_from_polys(&polys, assign, modulus)
}

/// Streaming pass 2 for a witness that satisfies every row. A suspect `v = α`
/// is two-valued iff some `β ≠ α` satisfies all its rows. Each row with `a ≠ 0`
/// has the roots `α` and `−b/a − α`, so such a `β` is the other root of every
/// one of them, and the one row pass 1 kept gives the only candidate. Same
/// verdicts as [`two_valued_suspects`] in one parallel sweep, without gathering
/// the rows: on circuits built from multiplications nearly every derived var
/// is a suspect. Over BN254 the sweep runs the compiled rows, as pass 1 did.
fn two_valued_satisfied(
    defs: &[GDef],
    top_c: &[CItem],
    assign: &[Option<crate::solver::Fp>],
    modulus: &num_bigint::BigUint,
    suspects: &std::collections::BTreeSet<u32>,
    quadratic: &[Quadratic],
    compiled: Option<&eval::Compiled>,
) -> std::collections::BTreeSet<u32> {
    use rayon::prelude::*;
    let test = SecondRoots::new(assign, modulus, suspects, quadratic);
    if let Some(c) = compiled {
        use crate::solver::Fp;
        let z = bn254_values(assign);
        c.top.par_iter().for_each(|item| {
            let mut check = |v: u32, a: ark_bn254::Fr, b: ark_bn254::Fr, cc: ark_bn254::Fr| {
                test.check_poly(v, &Fp::Bn254(a), &Fp::Bn254(b), &Fp::Bn254(cc));
            };
            eval::classify(c, item, &eval::TOP, &[], &z, &mut Vec::new(), &mut check);
        });
        return test.survivors();
    }
    top_c.par_iter().for_each(|item| {
        expand_c_visit(
            defs,
            std::slice::from_ref(item),
            &IDENTITY,
            &mut |row: R1csRow| test.check(&row, assign, modulus),
        );
    });
    test.survivors()
}

/// The other root of `a·v² + b·v + c` given one root `α` and `a ≠ 0`, as `n/a` with
/// `n = −b − a·α` (no inversion); `None` when it is `α` again.
fn other_root(
    a: &crate::solver::Fp,
    b: &crate::solver::Fp,
    alpha: &crate::solver::Fp,
) -> Option<crate::solver::Fp> {
    let n = b.neg().sub(&a.mul(alpha));
    (n != a.mul(alpha)).then_some(n)
}

/// Whether `n/a` is a root of `aj·v² + bj·v + cj`: `aj·n² + bj·n·a + cj·a² = 0`.
fn vanishes(
    (n, a): (&crate::solver::Fp, &crate::solver::Fp),
    (aj, bj, cj): &(crate::solver::Fp, crate::solver::Fp, crate::solver::Fp),
) -> bool {
    aj.mul(&n.mul(n))
        .add(&bj.mul(&n.mul(a)))
        .add(&cj.mul(&a.mul(a)))
        .is_zero()
}

/// Each suspect's one candidate second root (as `n/a`), and whether some row
/// rejected it.
struct SecondRoots {
    beta: Vec<Option<(crate::solver::Fp, crate::solver::Fp)>>,
    failed: Vec<std::sync::atomic::AtomicBool>,
}

impl SecondRoots {
    fn new(
        assign: &[Option<crate::solver::Fp>],
        modulus: &num_bigint::BigUint,
        suspects: &std::collections::BTreeSet<u32>,
        quadratic: &[Quadratic],
    ) -> Self {
        use crate::solver::Fp;
        use rayon::prelude::*;
        let zero = Fp::zero(modulus);
        let candidates: Vec<(u32, (Fp, Fp))> = suspects
            .par_iter()
            .filter_map(|&v| {
                let (a, b) = quadratic.get(v as usize)?.get()?;
                let alpha = assign
                    .get(v as usize)
                    .cloned()
                    .flatten()
                    .unwrap_or_else(|| zero.clone());
                Some((v, (other_root(a, b, &alpha)?, a.clone())))
            })
            .collect();
        let mut beta = vec![None; quadratic.len()];
        for (v, x) in candidates {
            beta[v as usize] = Some(x);
        }
        let failed = (0..beta.len())
            .map(|_| std::sync::atomic::AtomicBool::new(false))
            .collect();
        SecondRoots { beta, failed }
    }

    fn candidate(&self, v: u32) -> Option<(&crate::solver::Fp, &crate::solver::Fp)> {
        self.beta.get(v as usize)?.as_ref().map(|(n, a)| (n, a))
    }

    /// Reject the candidates `row` doesn't hold for.
    fn check(
        &self,
        row: &R1csRow,
        assign: &[Option<crate::solver::Fp>],
        modulus: &num_bigint::BigUint,
    ) {
        let mut terms = row.a.terms.iter().chain(&row.b.terms).chain(&row.c.terms);
        if !terms.any(|t| self.candidate(t.var).is_some()) {
            return;
        }
        for (v, (a, b, c)) in crate::solver::univariate_r1cs_row(row, assign, modulus) {
            self.check_poly(v, &a, &b, &c);
        }
    }

    /// Reject `v`'s candidate if `a·v² + b·v + c` (one of its rows) doesn't hold for it.
    fn check_poly(
        &self,
        v: u32,
        a: &crate::solver::Fp,
        b: &crate::solver::Fp,
        c: &crate::solver::Fp,
    ) {
        use std::sync::atomic::Ordering;
        let Some(x) = self.candidate(v) else { return };
        let failed = &self.failed[v as usize];
        if !failed.load(Ordering::Relaxed) && !vanishes(x, &(a.clone(), b.clone(), c.clone())) {
            failed.store(true, Ordering::Relaxed);
        }
    }

    fn survivors(&self) -> std::collections::BTreeSet<u32> {
        use std::sync::atomic::Ordering;
        (0..self.beta.len())
            .filter(|&v| self.beta[v].is_some() && !self.failed[v].load(Ordering::Relaxed))
            .map(|v| v as u32)
            .collect()
    }
}

/// The exact flat two-valued test over already-gathered per-suspect univariate
/// reductions: a suspect is under-constrained iff some second root `β≠α`
/// satisfies *all* of its rows. Mirrors `analyze_*_cp`'s candidate loop. Runs in
/// parallel over the suspects.
fn two_valued_from_polys(
    polys: &std::collections::BTreeMap<
        u32,
        Vec<(crate::solver::Fp, crate::solver::Fp, crate::solver::Fp)>,
    >,
    assign: &[Option<crate::solver::Fp>],
    modulus: &num_bigint::BigUint,
) -> std::collections::BTreeSet<u32> {
    use crate::solver::Fp;
    use rayon::prelude::*;
    polys
        .par_iter()
        .filter_map(|(&v, ps)| {
            let alpha = assign
                .get(v as usize)
                .cloned()
                .flatten()
                .unwrap_or_else(|| Fp::zero(modulus));
            for (a, b, _c) in ps {
                if a.is_zero() {
                    continue;
                }
                let Some(n) = other_root(a, b, &alpha) else {
                    continue;
                };
                if ps.iter().all(|p| vanishes((&n, a), p)) {
                    return Some(v);
                }
            }
            None
        })
        .collect()
}

/// Core streaming soundness pass shared by [`stream_analyze`] and
/// [`stream_verify`]: classify (pass 1) + optional satisfiability check, then
/// resolve the suspects (pass 2), and assemble the under-constraint list in
/// var-id order. Peak extra memory over the witness is a flag byte and, when
/// checking satisfiability, one row's `(a, b)` per var — never the flat
/// constraint system.
#[allow(clippy::too_many_arguments)]
fn stream_underconstrained(
    defs: &[GDef],
    top_c: &[CItem],
    vars: &[Var],
    keep_extra: &std::collections::BTreeSet<u32>,
    assign: &[Option<crate::solver::Fp>],
    modulus: &num_bigint::BigUint,
    check_sat: bool,
) -> (bool, Vec<crate::solver::UnderConstrained>) {
    // Over BN254 both passes run the compiled rows (`eval`); compiled once here.
    let compiled = crate::solver::is_bn254(modulus).then(|| eval::compile(defs, top_c));
    let compiled = compiled.as_ref();
    let (flags, sat_ok, quadratic) = classify_and_check(
        defs,
        top_c,
        assign,
        modulus,
        vars.len(),
        check_sat,
        compiled,
    );
    let suspects = select_suspects(&flags, vars);
    let two_valued = if suspects.is_empty() {
        std::collections::BTreeSet::new()
    } else if check_sat && sat_ok {
        two_valued_satisfied(
            defs, top_c, assign, modulus, &suspects, &quadratic, compiled,
        )
    } else {
        two_valued_suspects(defs, top_c, assign, modulus, &suspects)
    };
    let out = assemble_underconstrained(&flags, vars, keep_extra, &two_valued);
    (sat_ok, out)
}

/// Vars that survived pass-1 classification restricted-but-never-pinned — the
/// only ones that need the pass-2 two-valued test.
fn select_suspects(
    flags: &[std::sync::atomic::AtomicU8],
    vars: &[Var],
) -> std::collections::BTreeSet<u32> {
    use crate::primitive::VarRole;
    use std::sync::atomic::Ordering;
    vars.iter()
        .filter(|var| matches!(var.role, VarRole::Derived))
        .filter(|var| {
            let f = flags[var.id as usize].load(Ordering::Relaxed);
            f & F_SEEN != 0 && f & F_RESTRICTED != 0 && f & F_PINNED == 0
        })
        .map(|var| var.id)
        .collect()
}

/// Turn the classification flags (+ the resolved two-valued suspect set) into the
/// under-constraint verdict list, in var-id order — byte-identical to
/// `analyze_underconstrained_cp`'s output on the same circuit.
fn assemble_underconstrained(
    flags: &[std::sync::atomic::AtomicU8],
    vars: &[Var],
    keep_extra: &std::collections::BTreeSet<u32>,
    two_valued: &std::collections::BTreeSet<u32>,
) -> Vec<crate::solver::UnderConstrained> {
    use crate::primitive::VarRole;
    use std::sync::atomic::Ordering;
    vars.iter()
        .filter(|var| matches!(var.role, VarRole::Derived))
        .filter_map(|var| {
            let v = var.id;
            let f = flags[v as usize].load(Ordering::Relaxed);
            let reason = if f & F_SEEN == 0 {
                // Unreferenced: the flat analyzer only sees vars that survive the
                // expand-time prune (kept only for an explicit advice-keep).
                if keep_extra.contains(&v) {
                    "no constraint references this variable"
                } else {
                    return None;
                }
            } else if f & F_PINNED != 0 {
                return None; // linearly pinned → uniquely determined
            } else if f & F_RESTRICTED == 0 {
                "variable's coefficient is zero in every referencing constraint (free)"
            } else if two_valued.contains(&v) {
                "a different value also satisfies all its constraints (two-valued)"
            } else {
                return None; // restricted, single-valued → fine
            };
            Some(crate::solver::UnderConstrained {
                var: v,
                name: var.name.clone(),
                reason: reason.into(),
            })
        })
        .collect()
}

/// **Streaming under-constraint analyzer** — the soundness twin of
/// [`stream_check`]. Solves the witness, then classifies every variable in a
/// single parallel sweep of the compact bytecode using one flag byte per var
/// (never the flat constraint system, and — unlike a naive stream — never the
/// per-reference univariate reductions either). Results are identical to
/// `analyze_underconstrained_cp(&cp, &assign)`.
pub fn stream_analyze(
    b: &[u8],
    inputs: &std::collections::BTreeMap<u32, String>,
) -> Result<Vec<crate::solver::UnderConstrained>, String> {
    let (field, vars, defs, top_c, top_w, keep_extra, _num_inputs) = decode_compact(b);
    let modulus = num_bigint::BigUint::parse_bytes(field.modulus_decimal.as_bytes(), 10)
        .ok_or_else(|| "bad modulus".to_string())?;
    let assign = solve_streamed(&vars, vars.len(), &defs, &top_w, &modulus, inputs)?;
    let (_sat, out) =
        stream_underconstrained(&defs, &top_c, &vars, &keep_extra, &assign, &modulus, false);
    Ok(out)
}

/// **Streaming verify** — the low-memory analogue of the flat
/// `solve_and_check` + `analyze_underconstrained` that the test harness'
/// `check()` runs. Solves the witness *once*, then does a single combined
/// streaming pass that both checks every row `a·b = c` and classifies every
/// variable, plus the rare suspect pass. Extra peak memory over the witness is a
/// flag byte per var — it never materializes the flat constraint system nor the
/// per-reference univariate reductions. So it strictly wins on constraint-bound
/// circuits (the flat `Expression`/R1CS system is the bulk) and matches the flat
/// path on witness-bound ones (where the solve dominates and neither analyzer
/// representation matters). Returns the (unfiltered) under-constraint list, or
/// `Err` if the inputs do not satisfy the circuit.
pub fn stream_verify(
    b: &[u8],
    inputs: &std::collections::BTreeMap<u32, String>,
) -> Result<Vec<crate::solver::UnderConstrained>, String> {
    stream_solve_verify(b, inputs).map(|(_assign, out)| out)
}

/// Like [`stream_verify`], but also returns the solved witness assignment — so
/// the prove path can stream-solve (never materializing the flat program or
/// `witness_gen`), run the soundness gate, and hand the witness straight to the
/// Groth16 backend, all from one streamed solve. On a witness-heavy circuit
/// (non-native folding/IVC) it replaces the multi-GB `expand_function_blob` +
/// `solve_cp`. Returns `(assignment, under-constraint list)`; on an unsatisfied
/// witness it returns `Err`, and the caller may re-expand flat for a precise
/// which-constraint diagnostic on that rare path.
pub fn stream_solve_verify(
    b: &[u8],
    inputs: &std::collections::BTreeMap<u32, String>,
) -> Result<
    (
        std::collections::BTreeMap<u32, crate::solver::Fp>,
        Vec<crate::solver::UnderConstrained>,
    ),
    String,
> {
    let (field, vars, defs, top_c, top_w, keep_extra, _num_inputs) = decode_compact(b);
    let modulus = num_bigint::BigUint::parse_bytes(field.modulus_decimal.as_bytes(), 10)
        .ok_or_else(|| "bad modulus".to_string())?;
    let assign = solve_streamed(&vars, vars.len(), &defs, &top_w, &modulus, inputs)?;
    let (sat_ok, out) =
        stream_underconstrained(&defs, &top_c, &vars, &keep_extra, &assign, &modulus, true);
    if !sat_ok {
        return Err("a constraint is unsatisfied".to_string());
    }
    Ok((crate::solver::slots_into_map(assign), out))
}

/// Count the R1CS constraints by **streaming** them out of the compact bytecode
/// (never materializing the flat `Vec`). Same count as
/// `expand_function_blob(b).constraints.len()`, but at a tiny fraction of the
/// resident set — the memory-win measurement point. Parallel over shards.
pub fn stream_count_constraints(b: &[u8]) -> usize {
    use rayon::prelude::*;
    let CompactCore { defs, top_c, .. } = decode_core(b);
    top_c
        .par_iter()
        .map(|item| {
            let mut n = 0usize;
            expand_c_visit(&defs, std::slice::from_ref(item), &IDENTITY, &mut |_row| {
                n += 1
            });
            n
        })
        .sum()
}

/// Count the **multiplication gates** (R1CS rows where both `a` and `b` carry a
/// variable term — a genuine `a·b` product, not a linear/constant row) by
/// streaming the constraints out of the bytecode. Same count as
/// `expand_function_blob(b).constraints.iter().filter(|k| !k.a.terms.is_empty()
/// && !k.b.terms.is_empty()).count()`, but O(1) resident set — for the R1CS↔Lean
/// gate-count bridges. Parallel over shards.
pub fn stream_count_mul_gates(b: &[u8]) -> usize {
    use rayon::prelude::*;
    let CompactCore { defs, top_c, .. } = decode_core(b);
    top_c
        .par_iter()
        .map(|item| {
            let mut n = 0usize;
            expand_c_visit(
                &defs,
                std::slice::from_ref(item),
                &IDENTITY,
                &mut |row: R1csRow| {
                    if !row.a.terms.is_empty() && !row.b.terms.is_empty() {
                        n += 1;
                    }
                },
            );
            n
        })
        .sum()
}

/// Count the witness-gen ops by **streaming** them out of the compact bytecode
/// (never materializing the full `Vec<WitnessGen>` the flat solve builds). Same
/// count as `expand_function_blob(b).witness_gen.len()`, at a tiny fraction of
/// the resident set — the memory-win measurement point for the streamed solve.
pub fn stream_count_witness(b: &[u8]) -> usize {
    let CompactCore { defs, top_w, .. } = decode_core(b);
    let mut n = 0usize;
    expand_w_visit(&defs, &top_w, &IDENTITY, &mut |_op| n += 1);
    n
}

// 128-bit FNV-1a — a fixed, portable, deterministic fold (unlike `DefaultHasher`,
// whose output is unspecified across toolchains). Stable across machines/runs, so
// a committed digest constant is a valid regression pin.
fn fnv1a_128(acc: &mut u128, bytes: &[u8]) {
    const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013B;
    for &b in bytes {
        *acc ^= u128::from(b);
        *acc = acc.wrapping_mul(PRIME);
    }
}

/// Fold one linear combination into `acc` in a canonical, order-stable way.
fn digest_lc(acc: &mut u128, lc: &LinearCombination) {
    fnv1a_128(acc, lc.constant.decimal().as_bytes());
    fnv1a_128(acc, b"|");
    for t in &lc.terms {
        fnv1a_128(acc, &t.var.to_le_bytes());
        fnv1a_128(acc, t.coeff.decimal().as_bytes());
        fnv1a_128(acc, b",");
    }
    fnv1a_128(acc, b";");
}

/// **Streaming circuit digest** — a stable 128-bit fingerprint of the R1CS the
/// artifact expands to, computed by folding every `a·b = c` row straight out of
/// the bytecode (never materializing the flat system, O(1) resident set beyond
/// the walk). Because the flat R1CS uniquely determines the *minimized* one
/// (minimization is a pure function), this is a sound regression pin for proving
/// cost/shape — any change to the proven circuit changes the digest — without the
/// multi-GB expand+minimize the old constraint-count pin required. Witness-program
/// changes that leave the R1CS intact are covered separately by the solver check.
pub fn stream_digest(b: &[u8]) -> u128 {
    let CompactCore { defs, top_c, .. } = decode_core(b);
    // FNV-1a 128-bit offset basis.
    let mut acc: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
    expand_c_visit(&defs, &top_c, &IDENTITY, &mut |row: R1csRow| {
        digest_lc(&mut acc, &row.a);
        digest_lc(&mut acc, &row.b);
        digest_lc(&mut acc, &row.c);
        fnv1a_128(&mut acc, b"\n");
    });
    acc
}

/// [`stream_digest`] as `xark build` prints it (32 hex digits). A key's
/// `metadata.json` `digest` and a minimized key's `r1cs.stream` record it: every
/// build of a circuit has it, whichever Rust compiled `circuit.xbc`.
pub fn stream_digest_hex(b: &[u8]) -> String {
    format!("{:032x}", stream_digest(b))
}

/// Whether an `r1cs.stream` recording `fingerprint` holds rows for the circuit in
/// `xbc`: its file hash (`xbc_sha256`, how row files were first marked) or its
/// digest (how they are now, so another build of the circuit keeps its rows).
pub fn row_file_fits(fingerprint: &str, xbc_sha256: &str, xbc: &[u8]) -> bool {
    fingerprint == xbc_sha256 || fingerprint == stream_digest_hex(xbc)
}

/// **Build-time faithfulness gate, streamed.** Verify that the just-built compact
/// artifact `blob` expands byte-identically to the flat lowering (`r1cs` +
/// `prim`) — same R1CS rows, same (pruned) witness ops, same (pruned) var table —
/// WITHOUT materializing a second `CircuitProgram` on either side. The artifact's
/// rows/ops are streamed out of the bytecode and compared in place against the
/// already-held flat structures; only a dense referenced-var bitset (for the
/// prune) is allocated. Returns `(constraints, witness_ops, vars)` on success, or
/// a precise diff `Err`, with no second ~2 GB copy of the circuit.
pub fn verify_blob_matches(
    blob: &[u8],
    r1cs: &crate::r1cs::R1csProgram,
    prim: &crate::primitive::PrimitiveProgram,
) -> Result<(usize, usize, usize), String> {
    let (_field, decoded_vars, defs, top_c, top_w, keep_extra, num_inputs) = decode_compact(blob);
    let num_vars = decoded_vars.len();

    // Pass 1 — constraints: compare each streamed artifact row to the flat R1CS
    // constraint at the same index, and mark referenced vars (for the prune).
    let mut referenced = vec![false; num_vars];
    let mut ci = 0usize;
    let mut err: Option<String> = None;
    expand_c_visit(&defs, &top_c, &IDENTITY, &mut |row: R1csRow| {
        if err.is_some() {
            return;
        }
        match r1cs.constraints.get(ci) {
            Some(fc) if fc.a == row.a && fc.b == row.b && fc.c == row.c => {}
            Some(_) => {
                err = Some(format!(
                    "constraint #{ci} differs between flat lowering and artifact"
                ))
            }
            None => {
                err = Some(format!(
                    "artifact has more constraints than flat (>={})",
                    ci + 1
                ))
            }
        }
        for lc in [&row.a, &row.b, &row.c] {
            for t in &lc.terms {
                if (t.var as usize) < num_vars {
                    referenced[t.var as usize] = true;
                }
            }
        }
        ci += 1;
    });
    if let Some(e) = err {
        return Err(e);
    }
    if ci != r1cs.constraints.len() {
        return Err(format!(
            "constraint count flat={} vs artifact={ci}",
            r1cs.constraints.len()
        ));
    }

    // The exact prune `expand_function_blob` applies: keep inputs, referenced
    // vars, and advice-keeps; drop everything else (and the witness ops that
    // produce a dropped var).
    let keep = |id: usize| -> bool {
        id < num_inputs || referenced[id] || keep_extra.contains(&(id as u32))
    };

    // Pass 2 — witness ops: stream, drop pruned, compare the survivors in order.
    let mut wi = 0usize;
    let mut werr: Option<String> = None;
    expand_w_visit(&defs, &top_w, &IDENTITY, &mut |op: WitnessGen| {
        if werr.is_some() {
            return;
        }
        if !keep(witness_out(&op) as usize) {
            return; // pruned — not part of the flat witness program
        }
        match prim.witness_gen.get(wi) {
            Some(fo) if *fo == op => {}
            Some(_) => {
                werr = Some(format!(
                    "witness op #{wi} differs between flat lowering and artifact"
                ))
            }
            None => {
                werr = Some(format!(
                    "artifact has more witness ops than flat (>={})",
                    wi + 1
                ))
            }
        }
        wi += 1;
    });
    if let Some(e) = werr {
        return Err(e);
    }
    if wi != prim.witness_gen.len() {
        return Err(format!(
            "witness-op count flat={} vs artifact={wi}",
            prim.witness_gen.len()
        ));
    }

    // Vars: the pruned artifact var table (id + role) vs the flat one.
    let mut vi = 0usize;
    for (id, dv) in decoded_vars.iter().enumerate() {
        if !keep(id) {
            continue;
        }
        let fv = prim
            .vars
            .get(vi)
            .ok_or_else(|| format!("artifact has more vars than flat (>={})", vi + 1))?;
        if fv.id as usize != id || fv.role != dv.role {
            return Err(format!(
                "variable differs — flat (id={}, {:?}) vs artifact (id={id}, {:?})",
                fv.id, fv.role, dv.role
            ));
        }
        vi += 1;
    }
    if vi != prim.vars.len() {
        return Err(format!(
            "variable count flat={} vs artifact={vi}",
            prim.vars.len()
        ));
    }

    Ok((ci, wi, vi))
}

fn expand_c(defs: &[GDef], items: &[CItem], subst: &Subst, out: &mut Vec<R1csRow>) {
    for it in items {
        match it {
            CItem::Row(r) => out.push(R1csRow {
                a: subst_lc(&r.a, subst),
                b: subst_lc(&r.b, subst),
                c: subst_lc(&r.c, subst),
                note: None,
            }),
            CItem::Rolled(rows) => {
                for r in rows {
                    out.push(R1csRow {
                        a: subst_lc(&r.a, subst),
                        b: subst_lc(&r.b, subst),
                        c: subst_lc(&r.c, subst),
                        note: None,
                    });
                }
            }
            CItem::Call(d, base, plugs) => {
                let def = &defs[*d as usize];
                // Pull base var and plug LCs into global coords via the outer subst first.
                let base = subst_out(*base, subst);
                let sub_plugs: Vec<LinearCombination> =
                    plugs.iter().map(|lc| subst_lc(lc, subst)).collect();
                let sub = call_subst(def, base, sub_plugs);
                expand_c(defs, &def.c_items, &sub, out);
            }
        }
    }
}
fn expand_w(defs: &[GDef], items: &[WItem], subst: &Subst, out: &mut Vec<WitnessGen>) {
    for it in items {
        match it {
            WItem::Row(w) => {
                out.push(subst_witness(w, subst));
            }
            WItem::Rolled(wits) => {
                for w in wits {
                    out.push(subst_witness(w, subst));
                }
            }
            WItem::Call(d, base, plugs) => {
                let def = &defs[*d as usize];
                let base = subst_out(*base, subst);
                let sub_plugs: Vec<LinearCombination> =
                    plugs.iter().map(|lc| subst_lc(lc, subst)).collect();
                let sub = call_subst(def, base, sub_plugs);
                expand_w(defs, &def.w_items, &sub, out);
            }
        }
    }
}

/// Streaming twin of [`expand_w`]: emits each witness-gen op to `emit` in the
/// same topological order (dependencies before uses) instead of collecting the
/// whole `Vec<WitnessGen>`. Lets the solver consume ops in bounded batches so the
/// fully-expanded hint program (the dominant footprint on heavy non-native EC
/// circuits — GBs of substituted `LinearCombination`s) is never materialized.
fn expand_w_visit(defs: &[GDef], items: &[WItem], subst: &Subst, emit: &mut dyn FnMut(WitnessGen)) {
    for it in items {
        match it {
            WItem::Row(w) => {
                emit(subst_witness(w, subst));
            }
            WItem::Rolled(wits) => {
                for w in wits {
                    emit(subst_witness(w, subst));
                }
            }
            WItem::Call(d, base, plugs) => {
                let def = &defs[*d as usize];
                let base = subst_out(*base, subst);
                let sub_plugs: Vec<LinearCombination> =
                    plugs.iter().map(|lc| subst_lc(lc, subst)).collect();
                let sub = call_subst(def, base, sub_plugs);
                expand_w_visit(defs, &def.w_items, &sub, emit);
            }
        }
    }
}

/// Solve the witness into dense slots (`slots[id]`, `n` presized) without
/// materializing the flat hint program: over BN254 by running each template's
/// compiled ops against its calls ([`eval::solve_witness`]); over another field
/// by expanding the ops one by one into the batched solver. Produces the
/// identical assignment to `expand_w_top` + `solve`, at a fraction of the peak
/// (the full expanded `Vec<WitnessGen>` is the bulk of a heavy EC circuit's RSS).
fn solve_streamed(
    vars: &[Var],
    n: usize,
    defs: &[GDef],
    top_w: &[WItem],
    modulus: &num_bigint::BigUint,
    inputs: &BTreeMap<u32, String>,
) -> Result<Vec<Option<crate::solver::Fp>>, String> {
    if !crate::solver::is_bn254(modulus) {
        return crate::solver::solve_witness_streamed_dense(vars, n, modulus, inputs, |sink| {
            expand_w_visit(defs, top_w, &IDENTITY, &mut |op| sink(op));
        })
        .map_err(|e| format!("solve: {e:?}"));
    }
    let w = eval::solve_witness(defs, top_w, vars, n, modulus, inputs)
        .map_err(|e| format!("solve: {e:?}"))?;
    Ok(w.vals
        .into_iter()
        .zip(w.set)
        .map(|(v, set)| set.then_some(crate::solver::Fp::Bn254(v)))
        .collect())
}

thread_local! {
    /// How many [`catch_quietly`] calls this thread is inside.
    static QUIET: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// Run `f`, turning a panic into `Err`, without printing it: a malformed artifact
/// panics deep in the parser (bounds, tags, UTF-8), and one clean error line is
/// what the caller reports. The process's panic hook is wrapped once, never
/// swapped per call: swapping it raced between concurrent decodes and could leave
/// a no-op installed for good. The wrapper hands every panic to the hook it
/// wrapped unless it is on a thread inside here, so the host's hook keeps working.
/// A panic on a rayon worker of a decode still prints (the worker isn't inside
/// here); it is caught all the same when it resurfaces on this thread.
fn catch_quietly<T>(f: impl FnOnce() -> T) -> Result<T, ()> {
    static WRAPPED: std::sync::Once = std::sync::Once::new();
    WRAPPED.call_once(|| {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            // `try_with`: a panic while the thread's locals are torn down prints.
            if QUIET.try_with(std::cell::Cell::get).unwrap_or(0) == 0 {
                prev(info);
            }
        }));
    });
    struct Quiet;
    impl Drop for Quiet {
        fn drop(&mut self) {
            QUIET.with(|q| q.set(q.get() - 1));
        }
    }
    QUIET.with(|q| q.set(q.get() + 1));
    let _quiet = Quiet;
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).map_err(|_| ())
}

/// Parse an `XBC` (version 2) container and expand it to a full `CircuitProgram`.
/// The 6-byte header (`XBC` + version) is assumed already dispatched on.
///
/// Total: a `circuit.xbc` may be foreign or corrupted, so this must never crash the
/// process — it catches the inner parser's bounds/utf8/tag panics and returns a clean
/// `Err`. (Fuzzed by `gadgets/tests/tests/fuzz.rs`.)
pub fn expand_function_blob(b: &[u8]) -> Result<CircuitProgram, String> {
    expand_function_blob_impl(b)
}

fn expand_function_blob_impl(b: &[u8]) -> Result<CircuitProgram, String> {
    // Rayon fan-out panics propagate to this thread and are caught here too.
    catch_quietly(|| expand_function_blob_inner(b))
        .map_err(|()| "malformed function artifact (XBC decode failed)".to_string())
}

/// The variables the prune keeps, in id order: the signature inputs (the first
/// `inputs.len()` ids), then every other id below `num_vars` that a row references
/// or an advice exception keeps, `Derived` and unnamed. Walks the sets, not
/// `0..num_vars`, so a declared count costs nothing it doesn't name.
fn kept_vars(
    num_vars: usize,
    inputs: Vec<Var>,
    referenced: &std::collections::BTreeSet<u32>,
    keep_extra: &std::collections::BTreeSet<u32>,
) -> Vec<Var> {
    let first = inputs.len();
    let rest = referenced
        .union(keep_extra)
        .map(|&id| id as usize)
        .filter(|&id| id >= first && id < num_vars)
        .map(|id| Var {
            id: id as u32,
            name: format!("v{id}"),
            role: VarRole::Derived,
        });
    inputs.into_iter().chain(rest).collect()
}

fn expand_function_blob_inner(b: &[u8]) -> CircuitProgram {
    // The first `num_inputs` vars are signature inputs (role + name); all others
    // `Derived`.
    let (field, num_vars, inputs, p) = decode_header(b);
    let num_inputs = inputs.len();
    let (defs, top_c, top_w, keep_extra) = parse_body(b, p);

    // Constraints and witness are independent; expand across a rayon `join`.
    // Byte-identical to the serial monotonic walk — see `expand_c_top`.
    let (constraints, mut witness_gen) = rayon::join(
        || expand_c_top(&defs, &top_c, true),
        || expand_w_top(&defs, &top_w, true),
    );

    // Prune exactly like `finish`: drop unreferenced vars that aren't inputs or an
    // advice exception (`keep_extra`), then drop witness ops producing a dropped var.
    // Keeps the reconstructed circuit byte-identical to the flat one.
    let mut referenced: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    for c in &constraints {
        for lc in [&c.a, &c.b, &c.c] {
            for t in &lc.terms {
                referenced.insert(t.var);
            }
        }
    }
    let keep = |id: usize| -> bool {
        id < num_inputs || referenced.contains(&(id as u32)) || keep_extra.contains(&(id as u32))
    };
    witness_gen.retain(|op| keep(witness_out(op) as usize));
    CircuitProgram {
        field,
        vars: kept_vars(num_vars, inputs, &referenced, &keep_extra),
        constraints,
        witness_gen,
    }
}

/// Minimize one item stream's own `Row`s in isolation, pinning the def interface
/// (`base_pins` = plugs + outputs) plus every nested `Call`'s plug vars; everything
/// else is eliminated. Returns reduced `Row`s then the unchanged `Call`s. Per-template
/// reduction: each template's internal redundancy is removed once, here, avoiding
/// materializing and pruning the full flat R1CS.
/// Inline the nested calls of every def the top stream calls, so each such def
/// is minimized over its whole body — as when templates didn't nest — rather
/// than per nesting level (a call boundary pins its interface, which would keep
/// rows the flat body can eliminate). Defs only called from inside others are
/// left as they are (no longer reached).
fn flatten_nested(defs: &mut [GDef], top: &[CItem]) {
    let mut used = vec![false; defs.len()];
    for it in top {
        if let CItem::Call(d, ..) = it {
            used[*d as usize] = true;
        }
    }
    for d in 0..defs.len() {
        if !used[d]
            || !defs[d]
                .c_items
                .iter()
                .any(|it| matches!(it, CItem::Call(..)))
        {
            continue;
        }
        // The body is in its own (first call's) coordinates, so the identity
        // substitution expands its calls in place.
        let mut rows = Vec::new();
        expand_c(defs, &defs[d].c_items, &IDENTITY, &mut rows);
        defs[d].c_items = vec![CItem::Rolled(rows)];
    }
}

/// Each def's `(base_var, outputs)`: what a caller must pin around its calls.
fn call_interfaces(defs: &[GDef]) -> Vec<(u32, Vec<u32>)> {
    defs.iter()
        .map(|d| (d.base_var, d.outputs.clone()))
        .collect()
}

fn minimize_items(
    items: &[CItem],
    base_pins: &BTreeMap<u32, ()>,
    iface: &[(u32, Vec<u32>)],
    name: &str,
    modulus: &str,
    certs: Option<&mut Vec<Certificate>>,
) -> Vec<CItem> {
    let mut rows: Vec<crate::r1cs::R1csConstraint> = Vec::new();
    let mut calls: Vec<CItem> = Vec::new();
    let mut pins: std::collections::BTreeSet<u32> = base_pins.keys().copied().collect();
    for it in items {
        match it {
            CItem::Row(r) => rows.push(crate::r1cs::R1csConstraint {
                id: 0,
                a: r.a.clone(),
                b: r.b.clone(),
                c: r.c.clone(),
                debug: None,
            }),
            CItem::Rolled(rs) => rows.extend(rs.iter().map(|r| crate::r1cs::R1csConstraint {
                id: 0,
                a: r.a.clone(),
                b: r.b.clone(),
                c: r.c.clone(),
                debug: None,
            })),
            CItem::Call(d, base, plugs) => {
                // Plug LCs reference vars in this body; pin them so the minimizer
                // keeps the call interface intact.
                for lc in plugs {
                    pins.extend(lc.terms.iter().map(|t| t.var));
                }
                // The call's outputs, as this stream sees them: rows here that read
                // one must keep it (eliminating it here would cut it loose from the
                // call body that defines it).
                let (dbase, outs) = &iface[*d as usize];
                // (An output naming a plug is already pinned through the plug LC.)
                pins.extend(
                    outs.iter()
                        .filter(|&&o| o >= *dbase)
                        .map(|&o| base + (o - dbase)),
                );
                calls.push(CItem::Call(*d, *base, plugs.clone()));
            }
        }
    }
    let mut vs: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    for c in &rows {
        for lc in [&c.a, &c.b, &c.c] {
            for t in &lc.terms {
                vs.insert(t.var);
            }
        }
    }
    let variables: Vec<crate::r1cs::Variable> = vs
        .iter()
        .map(|&id| crate::r1cs::Variable {
            id,
            name: String::new(),
            visibility: if pins.contains(&id) {
                crate::r1cs::Visibility::Private
            } else {
                crate::r1cs::Visibility::Internal
            },
        })
        .collect();
    let prog = crate::r1cs::R1csProgram {
        field: crate::r1cs::FieldSpec {
            name: name.to_string(),
            modulus_decimal: Some(modulus.to_string()),
        },
        variables,
        constraints: rows,
    };
    // Per-template bodies are small; skip the fill-in guard and minimize fully.
    let reduced = match certs {
        Some(certs) => {
            let (reduced, trace) = crate::minimize::minimize_traced(&prog, usize::MAX);
            certs.push(Certificate {
                input: prog,
                output: reduced.clone(),
                trace,
            });
            reduced
        }
        None => crate::minimize::minimize_with_fill(&prog, usize::MAX),
    };
    let mut out: Vec<CItem> = reduced
        .constraints
        .into_iter()
        .map(|c| {
            CItem::Row(R1csRow {
                a: c.a,
                b: c.b,
                c: c.c,
                note: None,
            })
        })
        .collect();
    out.extend(calls);
    out
}

/// One minimizer run on the keyed path, for the Lean checker: its input and output rows
/// and its [`Trace`](crate::minimize::Trace).
pub struct Certificate {
    pub input: crate::r1cs::R1csProgram,
    pub output: crate::r1cs::R1csProgram,
    pub trace: crate::minimize::Trace,
}

/// Like [`expand_function_blob`] but produces the minimized R1CS directly: minimize
/// each template body once and expand the reduced templates, instead of expanding the
/// full flat R1CS and minimizing that. Witness program left empty — this is the
/// Groth16 (R1CS) view; the solver loads the full circuit separately.
pub fn expand_function_blob_reduced(b: &[u8]) -> Result<CircuitProgram, String> {
    expand_reduced(b, None)
}

/// As [`expand_function_blob_reduced`], also returning a [`Certificate`] of each
/// template body's and the top stream's minimization.
pub fn expand_function_blob_reduced_certified(
    b: &[u8],
) -> Result<(CircuitProgram, Vec<Certificate>), String> {
    let mut certs = Vec::new();
    let prog = expand_reduced(b, Some(&mut certs))?;
    Ok((prog, certs))
}

fn expand_reduced(
    b: &[u8],
    certs: Option<&mut Vec<Certificate>>,
) -> Result<CircuitProgram, String> {
    let prog = catch_quietly(|| expand_reduced_inner(b, certs))
        .map_err(|()| "malformed function artifact (XBC reduced decode failed)".to_string())?;
    // Every public input is pinned by a constraint at build time (the compiler's
    // pinning check), so a reduction that leaves one unreferenced has cut it loose
    // — any value would verify. Refuse rather than key such a circuit.
    let mut used = vec![false; prog.vars.len()];
    for r in &prog.constraints {
        for lc in [&r.a, &r.b, &r.c] {
            for t in &lc.terms {
                if let Some(u) = used.get_mut(t.var as usize) {
                    *u = true;
                }
            }
        }
    }
    if let Some(v) = prog.vars.iter().find(|v| {
        v.role == VarRole::PublicInput && !used.get(v.id as usize).copied().unwrap_or(false)
    }) {
        return Err(format!(
            "internal error: reducing the circuit left public input `{}` unconstrained \
             (please report)",
            v.name
        ));
    }
    Ok(prog)
}

fn expand_reduced_inner(b: &[u8], mut certs: Option<&mut Vec<Certificate>>) -> CircuitProgram {
    let (field, num_vars, inputs, p) = decode_header(b);
    let num_inputs = inputs.len();
    let (name, modulus_decimal) = (&field.name, &field.modulus_decimal);
    let (mut defs, top_c, _top_w, keep_extra) = parse_body(b, p);

    // Reduce each template body (plugs + outputs pinned) and the top stream (inputs
    // pinned); `expand_c` on the reduced defs then yields the minimized R1CS.
    flatten_nested(&mut defs, &top_c);
    let iface = call_interfaces(&defs);
    for def in &mut defs {
        let base_pins: BTreeMap<u32, ()> = def
            .plugs
            .iter()
            .chain(def.outputs.iter())
            .map(|&v| (v, ()))
            .collect();
        def.c_items = minimize_items(
            &def.c_items,
            &base_pins,
            &iface,
            name,
            modulus_decimal,
            certs.as_deref_mut(),
        );
    }
    let input_pins: BTreeMap<u32, ()> = (0..num_inputs as u32).map(|v| (v, ())).collect();
    let top_reduced = minimize_items(&top_c, &input_pins, &iface, name, modulus_decimal, certs);

    let mut constraints = Vec::new();
    expand_c(&defs, &top_reduced, &IDENTITY, &mut constraints);
    if crate::dbg_flag("XARK_BUILD_TIME") {
        eprintln!(
            "TEMPLATE-MINIMIZE: reduced R1CS = {} constraints",
            constraints.len()
        );
    }

    let mut referenced: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    for c in &constraints {
        for lc in [&c.a, &c.b, &c.c] {
            for t in &lc.terms {
                referenced.insert(t.var);
            }
        }
    }
    CircuitProgram {
        vars: kept_vars(num_vars, inputs, &referenced, &keep_extra),
        field,
        constraints,
        witness_gen: Vec::new(),
    }
}

/// The **template-reduced R1CS as a stream**: the same rows, in the same order, as
/// [`expand_function_blob_reduced`] — but never materialized. Holds only the
/// compact form (reduced template bodies + top-level items, ~the bytecode's size)
/// plus a per-item row count, and expands any run of top-level items on demand.
///
/// Top-level items carry absolute var ids (identity substitution), so they are
/// independent: a consumer can expand disjoint item windows in parallel and still
/// place every row at its exact global index (`item_row_start`). This is the
/// constraint source a streaming prover reads instead of the flat system.
pub struct ReducedRowStream {
    /// The circuit's field.
    pub field: FieldSpec,
    /// Kept variables, id order: `(id, is_public)`.
    vars: Vec<(u32, bool)>,
    defs: Vec<GDef>,
    top: Vec<CItem>,
    /// Prefix sums of rows per top-level item (`len = items + 1`).
    item_start: Vec<usize>,
    /// The templates compiled for numeric evaluation (built on first use).
    compiled: std::sync::OnceLock<eval::Compiled>,
}

impl ReducedRowStream {
    /// Decode `b` (a function blob) and reduce each template, exactly as
    /// [`expand_function_blob_reduced`] does, then make one streaming pass to
    /// count rows per item and collect the referenced-var set (for the var prune).
    /// Total: a malformed artifact is a clean `Err`, never a panic.
    pub fn new(b: &[u8]) -> Result<Self, String> {
        catch_quietly(|| Self::new_inner(b))
            .map_err(|()| "malformed function artifact (XBC reduced decode failed)".to_string())
    }

    fn new_inner(b: &[u8]) -> Self {
        use rayon::prelude::*;
        use std::sync::atomic::{AtomicU64, Ordering};
        let CompactCore {
            field,
            num_vars,
            inputs,
            mut defs,
            top_c,
            keep_extra,
            ..
        } = decode_core(b);
        let num_inputs = inputs.len();
        flatten_nested(&mut defs, &top_c);
        let iface = call_interfaces(&defs);
        for def in &mut defs {
            let base_pins: BTreeMap<u32, ()> = def
                .plugs
                .iter()
                .chain(def.outputs.iter())
                .map(|&v| (v, ()))
                .collect();
            def.c_items = minimize_items(
                &def.c_items,
                &base_pins,
                &iface,
                &field.name,
                &field.modulus_decimal,
                None,
            );
        }
        let input_pins: BTreeMap<u32, ()> = (0..num_inputs as u32).map(|v| (v, ())).collect();
        let top = minimize_items(
            &top_c,
            &input_pins,
            &iface,
            &field.name,
            &field.modulus_decimal,
            None,
        );

        // One streaming pass: rows per item + referenced vars (atomic bitset).
        let words: Vec<AtomicU64> = (0..num_vars.div_ceil(64))
            .map(|_| AtomicU64::new(0))
            .collect();
        // A var past the table is a malformed artifact: noted here and panicked on
        // below, on the thread that catches it, rather than on a rayon worker.
        let past = std::sync::atomic::AtomicBool::new(false);
        let counts: Vec<usize> = top
            .par_iter()
            .map(|it| {
                let mut n = 0usize;
                expand_c_visit(&defs, std::slice::from_ref(it), &IDENTITY, &mut |row| {
                    n += 1;
                    for lc in [&row.a, &row.b, &row.c] {
                        for t in &lc.terms {
                            let v = t.var as usize;
                            match words.get(v / 64) {
                                Some(w) => _ = w.fetch_or(1 << (v % 64), Ordering::Relaxed),
                                None => past.store(true, Ordering::Relaxed),
                            }
                        }
                    }
                });
                n
            })
            .collect();
        assert!(!past.into_inner(), "a row names a variable past the table");
        let mut item_start = Vec::with_capacity(counts.len() + 1);
        let mut acc = 0usize;
        item_start.push(0);
        for c in counts {
            acc += c;
            item_start.push(acc);
        }
        let referenced = |v: usize| words[v / 64].load(Ordering::Relaxed) >> (v % 64) & 1 == 1;
        let vars = (0..num_vars)
            .filter(|&id| id < num_inputs || referenced(id) || keep_extra.contains(&(id as u32)))
            .map(|id| {
                let public = inputs
                    .get(id)
                    .is_some_and(|v| matches!(v.role, VarRole::PublicInput));
                (id as u32, public)
            })
            .collect();
        ReducedRowStream {
            field,
            vars,
            defs,
            top,
            item_start,
            compiled: std::sync::OnceLock::new(),
        }
    }

    /// The kept variables in id order as `(id, is_public)` — the ids of
    /// `expand_function_blob_reduced(b)?.vars`.
    pub fn vars(&self) -> &[(u32, bool)] {
        &self.vars
    }

    /// Free the kept-variable list (e.g. once a prover has built its own layout).
    pub fn release_vars(&mut self) {
        self.vars = Vec::new();
    }

    /// Total rows (== `expand_function_blob_reduced(b)?.constraints.len()`).
    pub fn num_constraints(&self) -> usize {
        *self.item_start.last().unwrap_or(&0)
    }

    /// Number of independent top-level items.
    pub fn num_items(&self) -> usize {
        self.top.len()
    }

    /// Global index of the first row item `i` expands to (`i == num_items()` gives
    /// the total).
    pub fn item_row_start(&self, i: usize) -> usize {
        self.item_start[i]
    }

    /// Expand top-level items `items` in order, emitting each row. Rows arrive in
    /// global order starting at `item_row_start(items.start)`.
    pub fn visit_items(&self, items: std::ops::Range<usize>, emit: &mut dyn FnMut(R1csRow)) {
        expand_c_visit(&self.defs, &self.top[items], &IDENTITY, emit);
    }

    /// The **transpose** of [`eval_items`](Self::eval_items), for every row:
    /// `emit(var, m, Σ_rows w[row]·M[row][var])` contributions for each matrix `m`
    /// (A, B, C), where `var = None` is the constant column. Contributions to one
    /// variable may arrive in several pieces; the caller sums them. Plug terms are
    /// pushed back through the caller's plug expressions once per call, so the cost
    /// matches one evaluation pass. `w.len()` must be `num_constraints()`.
    pub fn transpose_eval(
        &self,
        w: &[ark_bn254::Fr],
        emit: &mut dyn FnMut(Option<u32>, usize, ark_bn254::Fr),
    ) {
        assert_eq!(w.len(), self.num_constraints());
        let c = self
            .compiled
            .get_or_init(|| eval::compile(&self.defs, &self.top));
        let mut row = 0usize;
        for item in &c.top {
            eval::adjoint(c, item, 0, &mut [], w, &mut row, emit);
        }
    }

    /// **Evaluate** rows of top-level items `items` against an assignment instead
    /// of expanding them: `emit([⟨A,z⟩, ⟨B,z⟩, ⟨C,z⟩])` per row, in row order
    /// (matrices not in `want` are left zero). Each template is compiled once to
    /// field coefficients and resolved variable references; a call evaluates its
    /// plug expressions to values once and runs the template body against them —
    /// no symbolic substitution, no allocation per term. Equal to evaluating the
    /// rows [`visit_items`](Self::visit_items) emits (evaluation is linear), for
    /// the BN254 scalar field. `z(id)` is the value of global variable `id`.
    pub fn eval_items(
        &self,
        items: std::ops::Range<usize>,
        z: &(dyn Fn(u32) -> ark_bn254::Fr + Sync),
        want: [bool; 3],
        emit: &mut dyn FnMut([ark_bn254::Fr; 3]),
    ) {
        let c = self
            .compiled
            .get_or_init(|| eval::compile(&self.defs, &self.top));
        let top = eval::Frame {
            base: 0,
            plugs: &[],
        };
        for item in &c.top[items] {
            eval::eval(c, item, &top, z, want, emit);
        }
    }
}

/// Numeric template evaluation (see [`ReducedRowStream::eval_items`]).
mod eval {
    use super::{CItem, GDef, R1csRow};
    use crate::linear_combination::LinearCombination;
    use crate::primitive::{Var, VarRole, WitnessGen};
    use crate::solver::{Fp, SolveError, exec_witness_op};
    use ark_bn254::Fr;
    use ark_ff::{BigInteger, PrimeField, Zero};
    use num_bigint::BigUint;
    use std::collections::BTreeMap;

    /// A variable as seen from inside a template body.
    #[derive(Clone, Copy, PartialEq)]
    pub enum VRef {
        /// A fresh internal: `call base + offset`.
        Internal(u32),
        /// The `i`-th plug: the caller's (evaluated) argument.
        Plug(u32),
        /// An absolute variable id.
        Global(u32),
    }

    #[derive(PartialEq)]
    pub struct Lc {
        k: Fr,
        terms: Vec<(VRef, Fr)>,
    }

    pub enum Item {
        Rows(Vec<[Lc; 3]>),
        Call {
            def: u32,
            base: VRef,
            plugs: Vec<Lc>,
        },
    }

    pub struct Compiled {
        defs: Vec<Vec<Item>>,
        /// One entry per top-level item (indices match the stream's items).
        pub top: Vec<Vec<Item>>,
    }

    pub struct Frame<'a> {
        pub base: u32,
        pub plugs: &'a [Fr],
    }

    /// The top-level frame: absolute variables, no plugs.
    pub const TOP: Frame<'static> = Frame {
        base: 0,
        plugs: &[],
    };

    fn resolve(v: u32, def: Option<&GDef>) -> VRef {
        match def {
            None => VRef::Global(v),
            Some(d) if v >= d.base_var => VRef::Internal(v - d.base_var),
            // A repeated plug var keeps its last expression, as in `call_subst`.
            Some(d) => match d.plugs.iter().rposition(|&p| p == v) {
                Some(i) => VRef::Plug(i as u32),
                None => VRef::Global(v),
            },
        }
    }

    fn lc(l: &LinearCombination, def: Option<&GDef>) -> Lc {
        Lc {
            k: l.constant.to_bn254_fr(),
            terms: l
                .terms
                .iter()
                .map(|t| (resolve(t.var, def), t.coeff.to_bn254_fr()))
                .collect(),
        }
    }

    fn row(r: &R1csRow, def: Option<&GDef>) -> [Lc; 3] {
        [lc(&r.a, def), lc(&r.b, def), lc(&r.c, def)]
    }

    fn items(src: &[CItem], def: Option<&GDef>) -> Vec<Item> {
        let mut out: Vec<Item> = Vec::new();
        let push_row = |out: &mut Vec<Item>, r: [Lc; 3]| match out.last_mut() {
            Some(Item::Rows(rs)) => rs.push(r),
            _ => out.push(Item::Rows(vec![r])),
        };
        for it in src {
            match it {
                CItem::Row(r) => push_row(&mut out, row(r, def)),
                CItem::Rolled(rs) => {
                    for r in rs {
                        push_row(&mut out, row(r, def));
                    }
                }
                CItem::Call(d, base, plugs) => out.push(Item::Call {
                    def: *d,
                    base: resolve(*base, def),
                    plugs: plugs.iter().map(|p| lc(p, def)).collect(),
                }),
            }
        }
        out
    }

    pub fn compile(defs: &[GDef], top: &[CItem]) -> Compiled {
        Compiled {
            defs: defs.iter().map(|d| items(&d.c_items, Some(d))).collect(),
            top: top
                .iter()
                .map(|it| items(std::slice::from_ref(it), None))
                .collect(),
        }
    }

    #[inline]
    fn val(r: VRef, f: &Frame, z: &dyn Fn(u32) -> Fr) -> Fr {
        match r {
            VRef::Internal(o) => z(f.base + o),
            VRef::Plug(i) => f.plugs[i as usize],
            VRef::Global(id) => z(id),
        }
    }

    #[inline]
    fn eval_lc(l: &Lc, f: &Frame, z: &dyn Fn(u32) -> Fr) -> Fr {
        let mut acc = l.k;
        for &(r, c) in &l.terms {
            acc += val(r, f, z) * c;
        }
        acc
    }

    /// Push `w[row]·coeff` back onto variables for every row of `items` (in a frame
    /// with internal base `base`); plug terms accumulate into `my_adj[plug][m]` for
    /// the caller to route through its plug expressions.
    pub fn adjoint(
        c: &Compiled,
        items: &[Item],
        base: u32,
        my_adj: &mut [[Fr; 3]],
        w: &[Fr],
        row: &mut usize,
        emit: &mut dyn FnMut(Option<u32>, usize, Fr),
    ) {
        // Route `s · lc` (an LC in this frame) to variables / this frame's plugs.
        fn route(
            l: &Lc,
            s: Fr,
            m: usize,
            base: u32,
            my_adj: &mut [[Fr; 3]],
            emit: &mut dyn FnMut(Option<u32>, usize, Fr),
        ) {
            if !l.k.is_zero() {
                emit(None, m, s * l.k);
            }
            for &(r, coef) in &l.terms {
                let v = s * coef;
                match r {
                    VRef::Internal(o) => emit(Some(base + o), m, v),
                    VRef::Global(id) => emit(Some(id), m, v),
                    VRef::Plug(i) => my_adj[i as usize][m] += v,
                }
            }
        }
        for it in items {
            match it {
                Item::Rows(rows) => {
                    for r in rows {
                        let wr = w[*row];
                        *row += 1;
                        if wr.is_zero() {
                            continue;
                        }
                        for (m, l) in r.iter().enumerate() {
                            route(l, wr, m, base, my_adj, emit);
                        }
                    }
                }
                Item::Call {
                    def,
                    base: cb,
                    plugs,
                } => {
                    let child_base = match *cb {
                        VRef::Internal(o) => base + o,
                        VRef::Global(id) => id,
                        VRef::Plug(_) => unreachable!("a call base is always a fresh var"),
                    };
                    let mut child_adj = vec![[Fr::zero(); 3]; plugs.len()];
                    adjoint(
                        c,
                        &c.defs[*def as usize],
                        child_base,
                        &mut child_adj,
                        w,
                        row,
                        emit,
                    );
                    for (p, adj) in plugs.iter().zip(&child_adj) {
                        for (m, &s) in adj.iter().enumerate() {
                            if !s.is_zero() {
                                route(p, s, m, base, my_adj, emit);
                            }
                        }
                    }
                }
            }
        }
    }

    /// A plug of the running call as terms on absolute variables: the caller's
    /// expression with the caller's own plugs resolved, so a template row's term on
    /// the plug is a term on each of these (its constant only moves the row's value,
    /// which [`eval_lc`] carries).
    pub type Flat = Vec<(u32, Fr)>;

    fn flatten(l: &Lc, f: &Frame, flat: &[Flat]) -> Flat {
        let mut out = Vec::with_capacity(l.terms.len());
        for &(r, c) in &l.terms {
            match r {
                VRef::Internal(o) => out.push((f.base + o, c)),
                VRef::Global(id) => out.push((id, c)),
                VRef::Plug(i) => out.extend(flat[i as usize].iter().map(|&(v, pc)| (v, pc * c))),
            }
        }
        out
    }

    /// For every row of `items` under `z`: whether it holds, and for each variable it
    /// references its univariate reduction `a·v² + b·v + c` (every other variable
    /// fixed at `z`), through `emit(var, a, b, c)`. The BN254 twin of
    /// [`crate::solver::univariate_r1cs_terms`] over compiled rows: a call evaluates
    /// its plugs once for the values and flattens them once for the coefficients, so
    /// no row is ever built. `scratch` is reused across rows. Returns whether every
    /// row held.
    pub fn classify(
        c: &Compiled,
        items: &[Item],
        f: &Frame,
        flat: &[Flat],
        z: &dyn Fn(u32) -> Fr,
        scratch: &mut Vec<(u32, usize, Fr)>,
        emit: &mut dyn FnMut(u32, Fr, Fr, Fr),
    ) -> bool {
        let mut ok = true;
        for it in items {
            match it {
                Item::Rows(rows) => {
                    for r in rows {
                        let full = [
                            eval_lc(&r[0], f, z),
                            eval_lc(&r[1], f, z),
                            eval_lc(&r[2], f, z),
                        ];
                        ok &= full[0] * full[1] == full[2];
                        scratch.clear();
                        for (m, l) in r.iter().enumerate() {
                            for &(vr, coef) in &l.terms {
                                match vr {
                                    VRef::Internal(o) => scratch.push((f.base + o, m, coef)),
                                    VRef::Global(id) => scratch.push((id, m, coef)),
                                    VRef::Plug(i) => scratch.extend(
                                        flat[i as usize].iter().map(|&(v, pc)| (v, m, pc * coef)),
                                    ),
                                }
                            }
                        }
                        scratch.sort_unstable_by_key(|t| t.0);
                        let mut k = 0;
                        while k < scratch.len() {
                            let v = scratch[k].0;
                            let mut own = [Fr::zero(); 3];
                            while let Some(&(_, m, coef)) = scratch.get(k).filter(|t| t.0 == v) {
                                own[m] += coef;
                                k += 1;
                            }
                            let [av, bv, cv] = own;
                            let x = z(v);
                            let a0 = full[0] - av * x;
                            let b0 = full[1] - bv * x;
                            let c0 = full[2] - cv * x;
                            emit(v, av * bv, av * b0 + a0 * bv - cv, a0 * b0 - c0);
                        }
                    }
                }
                Item::Call { def, base, plugs } => {
                    let pv: Vec<Fr> = plugs.iter().map(|p| eval_lc(p, f, z)).collect();
                    let pf: Vec<Flat> = plugs.iter().map(|p| flatten(p, f, flat)).collect();
                    let base = match *base {
                        VRef::Internal(o) => f.base + o,
                        VRef::Global(id) => id,
                        VRef::Plug(_) => unreachable!("a call base is always a fresh var"),
                    };
                    let inner = Frame { base, plugs: &pv };
                    ok &= classify(c, &c.defs[*def as usize], &inner, &pf, z, scratch, emit);
                }
            }
        }
        ok
    }

    pub fn eval(
        c: &Compiled,
        items: &[Item],
        f: &Frame,
        z: &dyn Fn(u32) -> Fr,
        want: [bool; 3],
        emit: &mut dyn FnMut([Fr; 3]),
    ) {
        for it in items {
            match it {
                Item::Rows(rows) => {
                    for r in rows {
                        let mut v = [Fr::zero(); 3];
                        for m in 0..3 {
                            if want[m] {
                                v[m] = eval_lc(&r[m], f, z);
                            }
                        }
                        emit(v);
                    }
                }
                Item::Call { def, base, plugs } => {
                    let pv: Vec<Fr> = plugs.iter().map(|p| eval_lc(p, f, z)).collect();
                    let base = match *base {
                        VRef::Internal(o) => f.base + o,
                        VRef::Global(id) => id,
                        VRef::Plug(_) => unreachable!("a call base is always a fresh var"),
                    };
                    let inner = Frame { base, plugs: &pv };
                    eval(c, &c.defs[*def as usize], &inner, z, want, emit);
                }
            }
        }
    }

    /// A witness op with template-local variable references and `Fr` coefficients.
    type WOp = WitnessGen<Lc, VRef>;

    /// A compiled witness item. An op's flag marks a `Bit` on the same input as
    /// the `Bit` just before it, which reads no output of that op, so the input's
    /// value carries over (see [`run`]).
    enum WItem {
        Op(WOp, bool),
        Call {
            def: u32,
            base: VRef,
            plugs: Vec<Lc>,
        },
    }

    fn w_items(src: &[super::WItem], def: Option<&GDef>) -> Vec<WItem> {
        let mut out: Vec<WItem> = Vec::new();
        let push_op = |out: &mut Vec<WItem>, op: &WitnessGen| {
            let op = op.map(|l| lc(l, def), |&v| resolve(v, def));
            let same = match (out.last(), &op) {
                (
                    Some(WItem::Op(
                        WitnessGen::Bit {
                            out, input: prev, ..
                        },
                        _,
                    )),
                    WitnessGen::Bit { input, .. },
                ) => {
                    // In a template an absolute variable might be one of the call's
                    // internals at run time, so the input must have none.
                    input == prev
                        && input.terms.iter().all(|&(r, _)| {
                            r != *out && (def.is_none() || !matches!(r, VRef::Global(_)))
                        })
                }
                _ => false,
            };
            out.push(WItem::Op(op, same));
        };
        for it in src {
            match it {
                super::WItem::Row(op) => push_op(&mut out, op),
                super::WItem::Rolled(ops) => ops.iter().for_each(|op| push_op(&mut out, op)),
                super::WItem::Call(d, base, plugs) => out.push(WItem::Call {
                    def: *d,
                    base: resolve(*base, def),
                    plugs: plugs.iter().map(|p| lc(p, def)).collect(),
                }),
            }
        }
        out
    }

    /// Whether some op under template `d` writes a variable that isn't one of its
    /// call's fresh internals (an absolute output, or a call at an absolute base).
    fn escapes(defs: &[Vec<WItem>], d: usize, memo: &mut [Option<bool>]) -> bool {
        if let Some(e) = memo[d] {
            return e;
        }
        let mut e = false;
        for it in &defs[d] {
            e |= match it {
                WItem::Op(op, _) => {
                    let mut out = false;
                    op.map(|_| (), |v| out |= !matches!(v, VRef::Internal(_)));
                    out
                }
                WItem::Call { def, base, .. } => {
                    !matches!(base, VRef::Internal(_)) || escapes(defs, *def as usize, memo)
                }
            };
        }
        memo[d] = Some(e);
        e
    }

    struct WProgram {
        defs: Vec<Vec<WItem>>,
        /// Per template: [`escapes`].
        escapes: Vec<bool>,
        top: Vec<WItem>,
    }

    /// A BN254 witness: values by var id, and which ids an input or an op
    /// assigned. An unassigned id reads as zero, as in the substituting solver.
    pub struct Witness {
        pub vals: Vec<Fr>,
        pub set: Vec<bool>,
    }

    impl Witness {
        fn get(&self, id: u32) -> Fr {
            self.vals.get(id as usize).copied().unwrap_or_default()
        }

        fn put(&mut self, id: u32, v: Fr) {
            let i = id as usize;
            if i >= self.vals.len() {
                self.vals.resize(i + 1, Fr::zero());
                self.set.resize(i + 1, false);
            }
            self.vals[i] = v;
            self.set[i] = true;
        }
    }

    /// A call's frame: the base of its fresh internals, and its plugs as LCs over
    /// absolute variables (`Global` terms only).
    struct WFrame {
        base: u32,
        plugs: Vec<Lc>,
        /// The plugs' values, when nothing the call writes can change them and
        /// it writes only its own internals (always, at the top level).
        vals: Option<Vec<Fr>>,
    }

    const ONE: Fr = ark_ff::MontFp!("1");

    impl WFrame {
        fn var(&self, r: VRef, w: &Witness) -> Fr {
            match r {
                VRef::Internal(o) => w.get(self.base + o),
                VRef::Global(id) => w.get(id),
                VRef::Plug(i) => match &self.vals {
                    Some(vals) => vals[i as usize],
                    // Read through the plug's expression now, as the substituted
                    // op would.
                    None => self.lc(&self.plugs[i as usize], w),
                },
            }
        }

        fn lc(&self, l: &Lc, w: &Witness) -> Fr {
            let mut acc = l.k;
            for &(r, c) in &l.terms {
                let x = self.var(r, w);
                // Most terms are bits, so a 0 or 1 skips the multiply.
                if x.is_zero() {
                } else if x == ONE {
                    acc += c;
                } else {
                    acc += if c == ONE { x } else { x * c };
                }
            }
            acc
        }

        /// The absolute variable an op output or call base names: always a fresh
        /// var, never a plug (`subst_out` relies on the same).
        fn out(&self, r: VRef) -> u32 {
            match r {
                VRef::Internal(o) => self.base + o,
                VRef::Global(id) => id,
                VRef::Plug(_) => unreachable!("an op output is always a fresh var"),
            }
        }

        /// The frame of a call to a template that does or doesn't `escape`.
        fn call(&self, base: VRef, plugs: &[Lc], escapes: bool, w: &Witness) -> WFrame {
            let base = self.out(base);
            let plugs: Vec<Lc> = plugs.iter().map(|l| self.absolute(l)).collect();
            // The call writes only its internals, from `base` on, so plugs reading
            // variables below `base` keep their values throughout it.
            let fixed = !escapes
                && plugs
                    .iter()
                    .flat_map(|l| &l.terms)
                    .all(|&(r, _)| matches!(r, VRef::Global(id) if id < base));
            let mut f = WFrame {
                base,
                plugs,
                vals: None,
            };
            if fixed {
                f.vals = Some(f.plugs.iter().map(|l| f.lc(l, w)).collect());
            }
            f
        }

        /// `l` (an LC in this frame) over absolute variables.
        fn absolute(&self, l: &Lc) -> Lc {
            let mut k = l.k;
            let mut terms = Vec::with_capacity(l.terms.len());
            for &(r, c) in &l.terms {
                match (r, &self.vals) {
                    (VRef::Plug(i), Some(vals)) => k += vals[i as usize] * c,
                    (VRef::Plug(i), None) => {
                        let p = &self.plugs[i as usize];
                        k += p.k * c;
                        terms.extend(p.terms.iter().map(|&(t, pc)| (t, pc * c)));
                    }
                    _ => terms.push((VRef::Global(self.out(r)), c)),
                }
            }
            Lc { k, terms }
        }
    }

    fn run(
        p: &WProgram,
        items: &[WItem],
        f: &WFrame,
        w: &mut Witness,
        modulus: &BigUint,
        outs: &mut Vec<(u32, Fp)>,
    ) -> Result<(), SolveError> {
        // A carried input stays current only if nothing it reads can change:
        // fixed plugs, and a template that writes only its own internals.
        let fixed = f.vals.is_some();
        let last = std::cell::Cell::new(None);
        // The carried input's canonical integer, once a `Bit` has computed it.
        let mut repr = None;
        for it in items {
            match it {
                WItem::Op(op, same) => {
                    let carried = last.get().filter(|_| *same && fixed);
                    if let WitnessGen::Bit { out, input, index } = op {
                        let x = carried.unwrap_or_else(|| {
                            repr = None;
                            f.lc(input, w)
                        });
                        last.set(Some(x));
                        let b: &ark_ff::BigInt<4> = repr.get_or_insert_with(|| x.into_bigint());
                        let bit = if b.get_bit(*index as usize) {
                            ONE
                        } else {
                            Fr::zero()
                        };
                        w.put(f.out(*out), bit);
                        continue;
                    }
                    repr = None;
                    let eval = |l: &Lc| {
                        let x = carried.unwrap_or_else(|| f.lc(l, w));
                        last.set(Some(x));
                        Fp::Bn254(x)
                    };
                    // Outputs land after the op has read all its inputs, as in
                    // `solve_witness_sequential`.
                    exec_witness_op(op, eval, modulus, &mut |r, x| outs.push((f.out(r), x)))?;
                    for (id, x) in outs.drain(..) {
                        w.put(
                            id,
                            x.as_bn254_fr().expect("a BN254 op yields a BN254 value"),
                        );
                    }
                }
                WItem::Call { def, base, plugs } => {
                    let d = *def as usize;
                    let inner = f.call(*base, plugs, p.escapes[d], w);
                    run(p, &p.defs[d], &inner, w, modulus, outs)?;
                }
            }
        }
        Ok(())
    }

    /// Solve the hint program over BN254 without expanding it: each template's
    /// ops are compiled once (`Fr` coefficients, template-local variables) and run
    /// against each call's frame into a dense witness of `n` slots. The same
    /// witness as `solve_witness_streamed_dense` over [`super::expand_w_visit`]:
    /// the ops run in the same order, and a plug's expression or a carried `Bit`
    /// input has the value the substituted op would read.
    pub fn solve_witness(
        defs: &[GDef],
        top: &[super::WItem],
        vars: &[Var],
        n: usize,
        modulus: &BigUint,
        inputs: &BTreeMap<u32, String>,
    ) -> Result<Witness, SolveError> {
        let mut w = Witness {
            vals: vec![Fr::zero(); n],
            set: vec![false; n],
        };
        for var in vars {
            if matches!(var.role, VarRole::PublicInput | VarRole::PrivateInput) {
                let decimal = inputs
                    .get(&var.id)
                    .ok_or(SolveError::MissingInput(var.id))?;
                let v = Fp::from_decimal(decimal, modulus);
                w.put(var.id, v.as_bn254_fr().expect("BN254 modulus"));
            }
        }
        // Compiling is per template and per top-level item, so it runs in
        // parallel; a chunk boundary only forgoes carrying a `Bit` input over.
        use rayon::prelude::*;
        let defs: Vec<Vec<WItem>> = defs
            .par_iter()
            .map(|d| w_items(&d.w_items, Some(d)))
            .collect();
        let top: Vec<WItem> = top
            .par_chunks(256)
            .map(|c| w_items(c, None))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect();
        let mut memo = vec![None; defs.len()];
        let escapes = (0..defs.len())
            .map(|d| escapes(&defs, d, &mut memo))
            .collect();
        let p = WProgram { defs, escapes, top };
        let top = WFrame {
            base: 0,
            plugs: Vec::new(),
            vals: Some(Vec::new()),
        };
        run(&p, &p.top, &top, &mut w, modulus, &mut Vec::new())?;
        Ok(w)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(a: u32, b: u32, c: u32) -> R1csRow {
        R1csRow {
            a: LinearCombination::var(a),
            b: LinearCombination::var(b),
            c: LinearCombination::var(c),
            note: None,
        }
    }

    /// A def referencing its plugs (`10`, `11`), its own internals (`>= base_var`),
    /// and a nested `Rolled` run — so a `Call` exercises plug subst and var shift.
    fn make_def() -> GDef {
        GDef {
            base_var: 100,
            plugs: vec![10, 11],
            outputs: vec![101],
            c_items: vec![
                CItem::Row(R1csRow {
                    a: LinearCombination::var(10),
                    b: LinearCombination::var(11),
                    c: LinearCombination::var(100),
                    note: None,
                }),
                CItem::Row(row(100, 100, 101)),
                CItem::Rolled(vec![row(101, 10, 102), row(102, 11, 103)]),
            ],
            w_items: vec![
                WItem::Row(WitnessGen::Product {
                    out: 100,
                    left: LinearCombination::var(10),
                    right: LinearCombination::var(11),
                }),
                WItem::Row(WitnessGen::Linear {
                    out: 101,
                    lc: LinearCombination::var(100),
                }),
                WItem::Rolled(vec![WitnessGen::Product {
                    out: 102,
                    left: LinearCombination::var(101),
                    right: LinearCombination::var(10),
                }]),
            ],
        }
    }

    /// A top-level stream with many independent items (rows, rolled runs, calls at
    /// distinct bases/plugs) — enough to span several rayon chunks.
    fn top_streams() -> (Vec<CItem>, Vec<WItem>) {
        let mut c = Vec::new();
        let mut w = Vec::new();
        for i in 0..200u32 {
            c.push(CItem::Row(row(i, i + 1, i + 2)));
            c.push(CItem::Rolled(vec![
                row(i, i, i + 5),
                row(i + 1, i + 1, i + 6),
            ]));
            // Fresh base per call, disjoint blocks (mirrors encoder's monotonic alloc).
            let base = 10_000 + i * 10;
            c.push(CItem::Call(
                0,
                base,
                vec![LinearCombination::var(i), LinearCombination::var(i + 3)],
            ));
            w.push(WItem::Row(WitnessGen::Linear {
                out: i,
                lc: LinearCombination::var(i + 1),
            }));
            w.push(WItem::Call(
                0,
                base,
                vec![LinearCombination::var(i), LinearCombination::var(i + 3)],
            ));
        }
        (c, w)
    }

    #[test]
    fn parallel_top_expand_is_byte_identical_to_serial() {
        let defs = vec![make_def()];
        let (top_c, top_w) = top_streams();

        let c_par = expand_c_top(&defs, &top_c, true);
        let c_ser = expand_c_top(&defs, &top_c, false);
        assert_eq!(c_par, c_ser, "constraint expansion diverged");

        let w_par = expand_w_top(&defs, &top_w, true);
        let w_ser = expand_w_top(&defs, &top_w, false);
        assert_eq!(w_par, w_ser, "witness expansion diverged");

        // Determinism: a second parallel run matches the first exactly.
        assert_eq!(c_par, expand_c_top(&defs, &top_c, true));
        assert_eq!(w_par, expand_w_top(&defs, &top_w, true));

        // Sanity: the streams actually produced output (calls expanded).
        assert!(c_par.len() > top_c.len());
        assert!(w_par.len() > top_w.len());
    }

    /// The compiled BN254 classification (`eval::classify`) and the generic one (rows
    /// built through the substitution) give every variable the same flags and the
    /// same satisfaction verdict, on a stream of rows, rolled rows and template calls
    /// whose plugs are expressions.
    #[test]
    fn compiled_classification_matches_generic() {
        use std::sync::atomic::Ordering;
        let m = bn254_modulus();
        let defs = vec![make_def()];
        let (top_c, _) = top_streams();
        let n = 12_100usize;
        let assign: Vec<Option<Fp>> = (0..n)
            .map(|i| {
                Some(Fp::from_decimal(
                    &((i * 7919 % 1000) as i64 - 500).to_string(),
                    &m,
                ))
            })
            .collect();
        let flags = |f: &[std::sync::atomic::AtomicU8]| -> Vec<u8> {
            f.iter().map(|a| a.load(Ordering::Relaxed)).collect()
        };
        let (gf, gok, gq) = classify_and_check(&defs, &top_c, &assign, &m, n, true, None);
        let compiled = eval::compile(&defs, &top_c);
        let (cf, cok, _) = classify_and_check(&defs, &top_c, &assign, &m, n, true, Some(&compiled));
        assert_eq!((flags(&gf), gok), (flags(&cf), cok));
        assert!(flags(&gf).iter().any(|&f| f & F_PINNED != 0));
        // Pass 2 over the same kept rows (`gq`: which row lands first varies between
        // runs), every var a suspect: the compiled rows reject the same candidates.
        assert!(gq.iter().filter(|q| q.get().is_some()).count() > 100);
        let all: std::collections::BTreeSet<u32> = (0..n as u32).collect();
        let generic = two_valued_satisfied(&defs, &top_c, &assign, &m, &all, &gq, None);
        let compiled = two_valued_satisfied(&defs, &top_c, &assign, &m, &all, &gq, Some(&compiled));
        assert_eq!(generic, compiled);
    }

    // ---- streaming under-constraint analyzer equivalence ----

    use crate::solver::Fp;

    /// Drive the streaming analyzer's shared core (the same `apply_row_flags` /
    /// `select_suspects` / `two_valued_from_polys` / `assemble_underconstrained`
    /// the real streaming path uses) over an explicit row list — so a test can
    /// feed a deliberately under-constrained circuit that `tiny` can't express.
    fn analyze_rows(
        rows: &[R1csRow],
        vars: &[Var],
        keep_extra: &std::collections::BTreeSet<u32>,
        assign: &std::collections::BTreeMap<u32, Fp>,
        modulus: &num_bigint::BigUint,
    ) -> Vec<crate::solver::UnderConstrained> {
        use std::sync::atomic::AtomicU8;
        let assign: Vec<Option<Fp>> = (0..vars.len() as u32)
            .map(|id| assign.get(&id).cloned())
            .collect();
        let assign = &assign[..];
        let flags: Vec<AtomicU8> = (0..vars.len()).map(|_| AtomicU8::new(0)).collect();
        let quadratic: Vec<Quadratic> = (0..vars.len()).map(|_| Quadratic::new()).collect();
        for r in rows {
            apply_row_flags(r, assign, modulus, &flags, &quadratic);
        }
        let suspects = select_suspects(&flags, vars);
        let mut polys: std::collections::BTreeMap<u32, Vec<(Fp, Fp, Fp)>> =
            suspects.iter().map(|&v| (v, Vec::new())).collect();
        for r in rows {
            for (v, poly) in crate::solver::univariate_r1cs_row(r, assign, modulus) {
                if let Some(ps) = polys.get_mut(&v) {
                    ps.push(poly);
                }
            }
        }
        let two_valued = two_valued_from_polys(&polys, assign, modulus);
        // A satisfied witness takes the one-candidate pass: same verdicts.
        if rows
            .iter()
            .all(|r| crate::solver::row_satisfied(&r.a, &r.b, &r.c, assign, modulus))
        {
            let roots = SecondRoots::new(assign, modulus, &suspects, &quadratic);
            for r in rows {
                roots.check(r, assign, modulus);
            }
            assert_eq!(
                roots.survivors(),
                two_valued,
                "one-candidate pass disagrees"
            );
        }
        assemble_underconstrained(&flags, vars, keep_extra, &two_valued)
    }

    fn bn254_modulus() -> num_bigint::BigUint {
        num_bigint::BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap()
    }

    fn dvar(id: u32, name: &str, role: VarRole) -> Var {
        Var {
            id,
            name: name.into(),
            role,
        }
    }

    /// The streaming core must reproduce `analyze_underconstrained_cp` exactly on
    /// a circuit with all three verdicts: a linearly-pinned product (fine), a
    /// booleanity-only bit (two-valued — forgeable), and a dangling advice var
    /// (unreferenced). `tiny` only exercises the pinned case, so this is the real
    /// soundness-equivalence test. Two more rows guard the one-pass row reduction:
    /// `q`'s two terms in `a` cancel, so it is free only if duplicate coefficients
    /// are summed; `r·2r = 2r` with `r = 1` is two-valued only if each var's own
    /// share, with its own LC's coefficient, is subtracted from the full row value.
    #[test]
    fn streaming_core_matches_flat_on_underconstrained() {
        let m = bn254_modulus();
        let fp = |n: i64| Fp::from_decimal(&n.to_string(), &m);

        // vars: 0,1 public inputs; 2 = a·b (pinned); 3 = booleanity bit
        // (two-valued); 4 = dangling advice (unreferenced, advice-kept).
        let vars = vec![
            dvar(0, "a", VarRole::PublicInput),
            dvar(1, "b", VarRole::PublicInput),
            dvar(2, "p", VarRole::Derived),
            dvar(3, "bit", VarRole::Derived),
            dvar(4, "dangling", VarRole::Derived),
            dvar(5, "q", VarRole::Derived),
            dvar(6, "r", VarRole::Derived),
        ];
        // r0: a·b = p ; r1: bit·(bit−1) = 0 ; r2: (q − q + a)·1 = a ; r3: r·2r = 2r
        let term = |coeff: i64, var: u32| Term {
            coeff: FieldConst::from_i64(coeff),
            var,
        };
        let bit_minus_one = LinearCombination {
            constant: FieldConst::from_i64(-1),
            terms: vec![Term {
                coeff: FieldConst::from_i64(1),
                var: 3,
            }],
        };
        let zero = LinearCombination {
            constant: FieldConst::from_i64(0),
            terms: vec![],
        };
        let rows = vec![
            R1csRow {
                a: LinearCombination::var(0),
                b: LinearCombination::var(1),
                c: LinearCombination::var(2),
                note: None,
            },
            R1csRow {
                a: LinearCombination::var(3),
                b: bit_minus_one,
                c: zero,
                note: None,
            },
            R1csRow {
                a: LinearCombination {
                    constant: FieldConst::from_i64(0),
                    terms: vec![term(1, 5), term(-1, 5), term(1, 0)],
                },
                b: LinearCombination::constant("1"),
                c: LinearCombination::var(0),
                note: None,
            },
            R1csRow {
                a: LinearCombination::var(6),
                b: LinearCombination {
                    constant: FieldConst::from_i64(0),
                    terms: vec![term(2, 6)],
                },
                c: LinearCombination {
                    constant: FieldConst::from_i64(0),
                    terms: vec![term(2, 6)],
                },
                note: None,
            },
        ];
        // Satisfying witness: 3·4 = 12, bit = 0, dangling = 0.
        let assign: std::collections::BTreeMap<u32, Fp> = [
            (0u32, fp(3)),
            (1, fp(4)),
            (2, fp(12)),
            (3, fp(0)),
            (4, fp(0)),
            (5, fp(12)),
            (6, fp(1)),
        ]
        .into_iter()
        .collect();
        let keep_extra: std::collections::BTreeSet<u32> = [4].into_iter().collect();

        let cp = CircuitProgram {
            field: FieldSpec {
                name: "bn254".into(),
                modulus_decimal:
                    "21888242871839275222246405745257275088548364400416034343698204186575808495617"
                        .into(),
            },
            vars: vars.clone(),
            constraints: rows.clone(),
            witness_gen: vec![],
        };

        let key = |u: &crate::solver::UnderConstrained| (u.var, u.reason.clone());
        let mut flat: Vec<_> = crate::solver::analyze_underconstrained_cp(&cp, &assign)
            .iter()
            .map(key)
            .collect();
        let mut stream: Vec<_> = analyze_rows(&rows, &vars, &keep_extra, &assign, &m)
            .iter()
            .map(key)
            .collect();
        flat.sort();
        stream.sort();
        assert_eq!(stream, flat, "streaming core must match the flat analyzer");
        // And it must actually flag the two forgeable vars.
        assert!(
            stream
                .iter()
                .any(|(v, r)| *v == 3 && r.contains("two-valued"))
        );
        assert!(
            stream
                .iter()
                .any(|(v, r)| *v == 4 && r.contains("no constraint"))
        );
        assert!(stream.iter().any(|(v, r)| *v == 5 && r.contains("free")));
        assert!(
            stream
                .iter()
                .any(|(v, r)| *v == 6 && r.contains("two-valued"))
        );
        assert!(
            !stream.iter().any(|(v, _)| *v == 2),
            "pinned var must be clean"
        );
    }

    /// Random small satisfied systems: the one-candidate pass a satisfied witness
    /// takes (checked inside `analyze_rows`) and the streaming core both match
    /// the flat analyzer, with two-valued vars among the cases.
    #[test]
    fn one_candidate_pass_matches_on_random_satisfied_systems() {
        let m = bn254_modulus();
        let fp = |n: i64| Fp::from_decimal(&n.to_string(), &m);
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move |n: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % n
        };
        let num_vars = 6u32;
        let vars: Vec<Var> = (0..num_vars)
            .map(|id| {
                let role = if id == 0 {
                    VarRole::PublicInput
                } else {
                    VarRole::Derived
                };
                dvar(id, &format!("v{id}"), role)
            })
            .collect();
        let mut two_valued = 0;
        for _ in 0..3000 {
            let assign: std::collections::BTreeMap<u32, Fp> =
                (0..num_vars).map(|v| (v, fp(next(4) as i64 - 1))).collect();
            let value = |lc: &LinearCombination| {
                lc.terms
                    .iter()
                    .fold(Fp::from_const(&lc.constant, &m), |acc, t| {
                        acc.add(&Fp::from_const(&t.coeff, &m).mul(&assign[&t.var]))
                    })
            };
            let row_count = 1 + next(4);
            let mut lc = |max_terms: u64| LinearCombination {
                constant: FieldConst::from_i64(next(5) as i64 - 2),
                terms: (0..next(max_terms + 1))
                    .map(|_| Term {
                        coeff: FieldConst::from_i64(next(5) as i64 - 2),
                        var: next(num_vars as u64) as u32,
                    })
                    .collect(),
            };
            let rows: Vec<R1csRow> = (0..row_count)
                .map(|_| {
                    let (a, b, mut c) = (lc(2), lc(2), lc(1));
                    // Satisfy the row through c's constant.
                    let rest = value(&a).mul(&value(&b)).sub(&value(&LinearCombination {
                        constant: FieldConst::from_i64(0),
                        terms: c.terms.clone(),
                    }));
                    c.constant = LinearCombination::constant(rest.to_decimal()).constant;
                    R1csRow {
                        a,
                        b,
                        c,
                        note: None,
                    }
                })
                .collect();
            let cp = CircuitProgram {
                field: FieldSpec {
                    name: "bn254".into(),
                    modulus_decimal: m.to_string(),
                },
                vars: vars.clone(),
                constraints: rows.clone(),
                witness_gen: vec![],
            };
            let key = |u: &crate::solver::UnderConstrained| (u.var, u.reason.clone());
            let mut flat: Vec<_> = crate::solver::analyze_underconstrained_cp(&cp, &assign)
                .iter()
                .map(key)
                .collect();
            let mut stream: Vec<_> =
                analyze_rows(&rows, &vars, &(0..num_vars).collect(), &assign, &m)
                    .iter()
                    .map(key)
                    .collect();
            flat.sort();
            stream.sort();
            assert_eq!(stream, flat, "rows {rows:?}");
            two_valued += stream
                .iter()
                .filter(|(_, r)| r.contains("two-valued"))
                .count();
        }
        assert!(two_valued > 100, "only {two_valued} two-valued cases");
    }
}
