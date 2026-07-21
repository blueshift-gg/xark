//! Decoder for the DAG-compact `XBC` (version 1) circuit artifact.
//!
//! The encoder lives in the compiler (`lower_mir::build_function_blob`, which has
//! the lowering `env`); this is the decode half, kept in `xark-ir` so both the
//! `xark` CLI and the compiler can reach it. It parses the container — function
//! defs (each with its var-kinds and two item streams) + top-level streams — and
//! expands it to a full [`CircuitProgram`] (constraints + witness program +
//! variable table), the same shape a flat `circuit.xbc` yields. The wire format
//! is defined jointly with the encoder; both must move together.

use crate::circuit::{CircuitProgram, R1csRow};
use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, Term, VarId};
use crate::primitive::{FieldSpec, Var, VarRole, WitnessGen};
use std::collections::BTreeMap;

// --- low-level readers (mirror the encoder's `put_*`) ------------------------
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
fn get_fc(b: &[u8], p: &mut usize) -> FieldConst {
    if b[*p] == 0 {
        *p += 1;
        FieldConst::from_i64(get_iv(b, p))
    } else {
        *p += 1;
        let n = get_uv(b, p) as usize;
        let s = std::str::from_utf8(&b[*p..*p + n]).unwrap();
        *p += n;
        FieldConst::from_decimal(s).unwrap()
    }
}
fn get_lc(b: &[u8], p: &mut usize) -> LinearCombination {
    let constant = get_fc(b, p);
    let n = get_uv(b, p) as usize;
    let mut terms = Vec::with_capacity(n);
    for _ in 0..n {
        let coeff = get_fc(b, p);
        let var = get_uv(b, p) as u32;
        terms.push(Term { coeff, var });
    }
    LinearCombination { constant, terms }
}
fn get_ids(b: &[u8], p: &mut usize) -> Vec<VarId> {
    let n = get_uv(b, p) as usize;
    (0..n).map(|_| get_uv(b, p) as u32).collect()
}
fn get_lcs(b: &[u8], p: &mut usize) -> Vec<LinearCombination> {
    let n = get_uv(b, p) as usize;
    (0..n).map(|_| get_lc(b, p)).collect()
}
fn get_str(b: &[u8], p: &mut usize) -> String {
    let n = get_uv(b, p) as usize;
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
    let tag = b[*p];
    *p += 1;
    match tag {
        0 => WitnessGen::Product {
            out: get_uv(b, p) as u32,
            left: get_lc(b, p),
            right: get_lc(b, p),
        },
        1 => WitnessGen::Linear {
            out: get_uv(b, p) as u32,
            lc: get_lc(b, p),
        },
        2 => WitnessGen::Xor {
            out: get_uv(b, p) as u32,
            a: get_lc(b, p),
            b: get_lc(b, p),
        },
        3 => WitnessGen::Or {
            out: get_uv(b, p) as u32,
            a: get_lc(b, p),
            b: get_lc(b, p),
        },
        4 => WitnessGen::Inverse {
            out: get_uv(b, p) as u32,
            input: get_lc(b, p),
        },
        5 => WitnessGen::InverseOrZero {
            out: get_uv(b, p) as u32,
            input: get_lc(b, p),
        },
        6 => WitnessGen::Bit {
            out: get_uv(b, p) as u32,
            input: get_lc(b, p),
            index: get_uv(b, p) as u32,
        },
        7 => WitnessGen::Bits {
            outs: get_ids(b, p),
            input: get_lc(b, p),
        },
        8 => WitnessGen::DivRem {
            q: get_uv(b, p) as u32,
            r: get_uv(b, p) as u32,
            num: get_lc(b, p),
            den: get_lc(b, p),
        },
        9 => WitnessGen::MulModDivMod {
            q: get_ids(b, p),
            r: get_ids(b, p),
            a: get_lcs(b, p),
            b: get_lcs(b, p),
            modulus: get_lcs(b, p),
            limb_bits: get_uv(b, p) as u32,
        },
        10 => WitnessGen::ModInverse {
            out: get_ids(b, p),
            a: get_lcs(b, p),
            modulus: get_lcs(b, p),
            limb_bits: get_uv(b, p) as u32,
        },
        11 => WitnessGen::Sub2 {
            qabs: get_uv(b, p) as u32,
            r: get_ids(b, p),
            a: get_lcs(b, p),
            b: get_lcs(b, p),
            c: get_lcs(b, p),
            modulus: get_lcs(b, p),
            limb_bits: get_uv(b, p) as u32,
        },
        _ => unreachable!("bad witness tag {tag}"),
    }
}

/// The primary output var of a witness op (mirrors `lower_mir::witness_gen_out`) —
/// used to decide whether the op survives the var prune.
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
        WitnessGen::ModInverse { out, .. } => *out.first().unwrap_or(&0),
        WitnessGen::Sub2 { qabs, .. } => *qabs,
    }
}

// --- substitution (internals shift base+offset; plug vars → plug LCs) --------
/// Substitute an LC under `s`: each term `coeff·var` becomes `coeff · s(var)`
/// (`s` maps an internal var to a shifted single var, and a plug var to the
/// caller's plug LC). Mirrors `lower_mir::replay_function`'s `subst_lc`, so a
/// bytecode CALL expands byte-identically to a walked replay.
fn subst_lc(lc: &LinearCombination, s: &dyn Fn(u32) -> LinearCombination) -> LinearCombination {
    let mut constant = lc.constant.clone();
    let mut terms: Vec<Term> = Vec::new();
    for t in &lc.terms {
        let piece = s(t.var).scale(&t.coeff);
        constant = constant.add(&piece.constant);
        terms.extend(piece.terms);
    }
    LinearCombination { constant, terms }.simplified()
}
/// The single var an out/id witness field maps to. Out/id fields are always fresh
/// internals, so `s` yields a bare `1·v` LC.
fn subst_out(v: u32, s: &dyn Fn(u32) -> LinearCombination) -> u32 {
    s(v).terms[0].var
}
fn subst_witness(w: &mut WitnessGen, s: &dyn Fn(u32) -> LinearCombination) {
    let ids = |v: &mut [VarId]| {
        for x in v {
            *x = subst_out(*x, s);
        }
    };
    let lcs = |v: &mut [LinearCombination]| {
        for l in v {
            *l = subst_lc(l, s);
        }
    };
    match w {
        WitnessGen::Product { out, left, right } => {
            *out = subst_out(*out, s);
            *left = subst_lc(left, s);
            *right = subst_lc(right, s);
        }
        WitnessGen::Linear { out, lc: l } => {
            *out = subst_out(*out, s);
            *l = subst_lc(l, s);
        }
        WitnessGen::Xor { out, a, b } | WitnessGen::Or { out, a, b } => {
            *out = subst_out(*out, s);
            *a = subst_lc(a, s);
            *b = subst_lc(b, s);
        }
        WitnessGen::Inverse { out, input } | WitnessGen::InverseOrZero { out, input } => {
            *out = subst_out(*out, s);
            *input = subst_lc(input, s);
        }
        WitnessGen::Bit { out, input, .. } => {
            *out = subst_out(*out, s);
            *input = subst_lc(input, s);
        }
        WitnessGen::Bits { outs, input } => {
            ids(outs);
            *input = subst_lc(input, s);
        }
        WitnessGen::DivRem { q, r, num, den } => {
            *q = subst_out(*q, s);
            *r = subst_out(*r, s);
            *num = subst_lc(num, s);
            *den = subst_lc(den, s);
        }
        WitnessGen::MulModDivMod {
            q,
            r,
            a,
            b,
            modulus,
            ..
        } => {
            ids(q);
            ids(r);
            lcs(a);
            lcs(b);
            lcs(modulus);
        }
        WitnessGen::ModInverse {
            out, a, modulus, ..
        } => {
            ids(out);
            lcs(a);
            lcs(modulus);
        }
        WitnessGen::Sub2 {
            qabs,
            r,
            a,
            b,
            c,
            modulus,
            ..
        } => {
            *qabs = subst_out(*qabs, s);
            ids(r);
            lcs(a);
            lcs(b);
            lcs(c);
            lcs(modulus);
        }
    }
}

/// Build the substitution for a CALL: plug var → the caller's (already
/// outer-substituted) plug LC; internal var (`>= def.base_var`) → shifted single
/// var at `base`; anything else → itself.
fn call_subst(
    def: &GDef,
    base: u32,
    plugs: Vec<LinearCombination>,
) -> impl Fn(u32) -> LinearCombination {
    let dbase = def.base_var;
    let plug_map: BTreeMap<u32, LinearCombination> = def.plugs.iter().copied().zip(plugs).collect();
    move |v: u32| -> LinearCombination {
        if v >= dbase {
            LinearCombination::var(base + (v - dbase))
        } else if let Some(p) = plug_map.get(&v) {
            p.clone()
        } else {
            LinearCombination::var(v)
        }
    }
}

// --- parsed items ------------------------------------------------------------
enum CItem {
    Row(R1csRow),
    /// A CALL: `(def index, fresh var base, plug LCs)`. The plug LCs are in the
    /// enclosing scope's coords and are substituted into the def body on expand.
    Call(u32, u32, Vec<LinearCombination>),
    /// A rolled run of ≥2 inline rows, already expanded to flat rows (in the
    /// def's own coords; remapped at expansion like an inline `Row`).
    Rolled(Vec<R1csRow>),
}
enum WItem {
    Row(WitnessGen),
    Call(u32, u32, Vec<LinearCombination>),
    /// A rolled run of ≥2 witness ops, already expanded.
    Rolled(Vec<WitnessGen>),
}
struct GDef {
    base_var: u32,
    plugs: Vec<u32>,
    outputs: Vec<u32>,
    c_items: Vec<CItem>,
    w_items: Vec<WItem>,
}
/// Parse a rolled-CALL block (tag `3`, Stage 3 loop fusion) and expand it to the
/// `count · period` individual CALLs it stands for. Iteration `k` of template `j`
/// gets `base = base0 + k·base_step` and each plug-LC term var `var0 + k·var_step`
/// (coeffs/constants loop-invariant). Expanding at parse time means the rest of the
/// decoder (`expand_c`/`expand_w`/`minimize_items`) sees ordinary `Call`s — so the
/// rolled form is BYTE-IDENTICAL to the unrolled CALL tokens by construction.
/// Mirrors `lower_mir::put_rolled_call`.
fn parse_rolled_calls(b: &[u8], p: &mut usize) -> Vec<(u32, u32, Vec<LinearCombination>)> {
    let count = get_uv(b, p) as i64;
    let period = get_uv(b, p) as usize;
    struct Tmpl {
        def: u32,
        base0: i64,
        base_step: i64,
        #[allow(clippy::type_complexity)]
        plugs: Vec<(FieldConst, Vec<(FieldConst, i64, i64)>)>,
    }
    let mut body = Vec::with_capacity(period);
    for _ in 0..period {
        let def = get_uv(b, p) as u32;
        let base0 = get_uv(b, p) as i64;
        let base_step = get_iv(b, p);
        let nplugs = get_uv(b, p) as usize;
        let mut plugs = Vec::with_capacity(nplugs);
        for _ in 0..nplugs {
            let constant = get_fc(b, p);
            let nterms = get_uv(b, p) as usize;
            let mut terms = Vec::with_capacity(nterms);
            for _ in 0..nterms {
                let coeff = get_fc(b, p);
                let var0 = get_uv(b, p) as i64;
                let step = get_iv(b, p);
                terms.push((coeff, var0, step));
            }
            plugs.push((constant, terms));
        }
        body.push(Tmpl {
            def,
            base0,
            base_step,
            plugs,
        });
    }
    let mut out = Vec::with_capacity(count.max(0) as usize * period);
    for k in 0..count {
        for t in &body {
            let base = (t.base0 + k * t.base_step) as u32;
            let lcs: Vec<LinearCombination> = t
                .plugs
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
            out.push((t.def, base, lcs));
        }
    }
    out
}
fn parse_c_items(b: &[u8], p: &mut usize) -> Vec<CItem> {
    let n = get_uv(b, p) as usize;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let tag = b[*p];
        *p += 1;
        match tag {
            0 => out.push(CItem::Row(R1csRow {
                a: get_lc(b, p),
                b: get_lc(b, p),
                c: get_lc(b, p),
                note: None,
            })),
            1 => {
                let d = get_uv(b, p) as u32;
                let base = get_uv(b, p) as u32;
                out.push(CItem::Call(d, base, get_lcs(b, p)));
            }
            3 => {
                for (d, base, plugs) in parse_rolled_calls(b, p) {
                    out.push(CItem::Call(d, base, plugs));
                }
            }
            _ => {
                let len = get_uv(b, p) as usize;
                let blob = &b[*p..*p + len];
                *p += len;
                let (rows, _) = crate::bytecode::decode_and_expand_ops(blob).unwrap_or_default();
                out.push(CItem::Rolled(rows));
            }
        }
    }
    out
}
fn parse_w_items(b: &[u8], p: &mut usize) -> Vec<WItem> {
    let n = get_uv(b, p) as usize;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let tag = b[*p];
        *p += 1;
        match tag {
            0 => out.push(WItem::Row(get_witness(b, p))),
            1 => {
                let d = get_uv(b, p) as u32;
                let base = get_uv(b, p) as u32;
                out.push(WItem::Call(d, base, get_lcs(b, p)));
            }
            3 => {
                for (d, base, plugs) in parse_rolled_calls(b, p) {
                    out.push(WItem::Call(d, base, plugs));
                }
            }
            _ => {
                let len = get_uv(b, p) as usize;
                let blob = &b[*p..*p + len];
                *p += len;
                let (_, wits) = crate::bytecode::decode_and_expand_ops(blob).unwrap_or_default();
                out.push(WItem::Rolled(wits));
            }
        }
    }
    out
}

/// The top-level (identity) substitution: every var maps to itself. Kept as a
/// named `fn` (not a capturing closure) so it is `Send + Sync + Copy` and can be
/// handed to rayon workers during parallel expansion.
fn identity_lc(v: u32) -> LinearCombination {
    LinearCombination::var(v)
}

/// Expand the **top-level** constraint stream, optionally in parallel.
///
/// At the top level the substitution is the identity, and every top-level item's
/// var ids (a `Row`'s term vars, a `Call`'s fresh `base`, its plug-LC term vars)
/// are already **absolute** — baked into the bytecode by the encoder's monotonic
/// walk. So each top-level item expands to a fixed, self-contained slice of rows
/// that depends only on `defs` and the item itself; there is **no shared running
/// counter** between items. That makes the items independent: expanding each into
/// a local buffer and concatenating them *in item order* is byte-for-byte the
/// same sequence the serial `for it in items` loop produces. We exploit that to
/// fan the per-item expansion across rayon while keeping the result identical.
fn expand_c_top(defs: &[GDef], items: &[CItem], parallel: bool) -> Vec<R1csRow> {
    if parallel {
        use rayon::prelude::*;
        let chunks: Vec<Vec<R1csRow>> = items
            .par_iter()
            .map(|it| {
                let mut buf = Vec::new();
                expand_c(defs, std::slice::from_ref(it), &identity_lc, &mut buf);
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
        expand_c(defs, items, &identity_lc, &mut out);
        out
    }
}

/// Witness-stream counterpart of [`expand_c_top`] — same independence argument
/// (top-level witness ops carry absolute out/id vars and identity-substituted
/// input LCs), so per-item parallel expansion concatenated in order is identical
/// to the serial walk.
fn expand_w_top(defs: &[GDef], items: &[WItem], parallel: bool) -> Vec<WitnessGen> {
    if parallel {
        use rayon::prelude::*;
        let chunks: Vec<Vec<WitnessGen>> = items
            .par_iter()
            .map(|it| {
                let mut buf = Vec::new();
                expand_w(defs, std::slice::from_ref(it), &identity_lc, &mut buf);
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
        expand_w(defs, items, &identity_lc, &mut out);
        out
    }
}

fn expand_c(
    defs: &[GDef],
    items: &[CItem],
    subst: &dyn Fn(u32) -> LinearCombination,
    out: &mut Vec<R1csRow>,
) {
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
                // The call's base var and plug LCs are in the enclosing coords;
                // pull them into global coords via the outer substitution first.
                let base = subst_out(*base, subst);
                let sub_plugs: Vec<LinearCombination> =
                    plugs.iter().map(|lc| subst_lc(lc, subst)).collect();
                let sub = call_subst(def, base, sub_plugs);
                expand_c(defs, &def.c_items, &sub, out);
            }
        }
    }
}
fn expand_w(
    defs: &[GDef],
    items: &[WItem],
    subst: &dyn Fn(u32) -> LinearCombination,
    out: &mut Vec<WitnessGen>,
) {
    for it in items {
        match it {
            WItem::Row(w) => {
                let mut w = w.clone();
                subst_witness(&mut w, subst);
                out.push(w);
            }
            WItem::Rolled(wits) => {
                for w in wits {
                    let mut w = w.clone();
                    subst_witness(&mut w, subst);
                    out.push(w);
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

/// Parse an `XBC` (version 1) container and expand it to the full
/// `CircuitProgram`. The 6-byte header (`XBC` + `0x0001`) is assumed already
/// dispatched on.
///
/// **Total.** A `circuit.xbc` may have been produced on another machine or
/// corrupted on disk, so this must never crash the process: it catches the
/// bounds/utf8/tag panics of the inner parser and returns them as a clean `Err`.
/// (Fuzzed by `gadgets/tests/tests/fuzz.rs` — arbitrary/mutated bytes never panic.)
pub fn expand_function_blob(b: &[u8]) -> Result<CircuitProgram, String> {
    expand_function_blob_impl(b)
}

fn expand_function_blob_impl(b: &[u8]) -> Result<CircuitProgram, String> {
    // Silence the default panic printer for the expected-on-malformed-input inner
    // panics, then restore it — so a bad artifact yields one clean error line, not
    // a spurious backtrace. Decode is sequential in setup/prove, so swapping the
    // process-global hook here is safe. Panics inside the rayon fan-out propagate
    // to this thread and are caught here too, so totality still holds.
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        expand_function_blob_inner(b)
    }));
    std::panic::set_hook(prev);
    out.map_err(|_| "malformed function artifact (XBC decode failed)".to_string())
}

fn expand_function_blob_inner(b: &[u8]) -> CircuitProgram {
    let mut p = 6usize; // MAGIC(4) + version(2)
    let name = get_str(b, &mut p);
    let modulus_decimal = get_str(b, &mut p);
    let num_vars = get_uv(b, &mut p) as usize;
    // The first `num_inputs` vars are the signature inputs (role + name); every
    // other var is `Derived` (mul outputs AND hint/advice — all witness-computed).
    let num_inputs = get_uv(b, &mut p) as usize;
    let mut roles = vec![VarRole::Derived; num_vars];
    let mut names: Vec<Option<String>> = vec![None; num_vars];
    for id in 0..num_inputs {
        roles[id] = byte_role(b[p]);
        p += 1;
        names[id] = Some(get_str(b, &mut p));
    }
    let n_defs = get_uv(b, &mut p) as usize;
    let mut defs = Vec::with_capacity(n_defs);
    for _ in 0..n_defs {
        let base_var = get_uv(b, &mut p) as u32;
        let plugs = get_ids(b, &mut p);
        let outputs = get_ids(b, &mut p);
        let c_items = parse_c_items(b, &mut p);
        let w_items = parse_w_items(b, &mut p);
        defs.push(GDef {
            base_var,
            plugs,
            outputs,
            c_items,
            w_items,
        });
    }
    let top_c = parse_c_items(b, &mut p);
    let top_w = parse_w_items(b, &mut p);
    let keep_extra: std::collections::BTreeSet<u32> = get_ids(b, &mut p).into_iter().collect();

    // Constraints and witness are independent of each other; expand them across a
    // rayon `join` (each internally fanned over its top-level items). The result is
    // byte-identical to the serial monotonic walk — see `expand_c_top`.
    let (constraints, mut witness_gen) = rayon::join(
        || expand_c_top(&defs, &top_c, true),
        || expand_w_top(&defs, &top_w, true),
    );

    // Prune exactly like `finish`: drop every unreferenced var that isn't an input
    // or an advice exception (`keep_extra`), then drop witness ops producing a
    // dropped var. Keeps the reconstructed circuit byte-identical to the flat one.
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
    let vars = (0..num_vars)
        .filter(|&id| keep(id))
        .map(|id| Var {
            id: id as u32,
            name: names[id].take().unwrap_or_else(|| format!("v{id}")),
            role: roles[id].clone(),
        })
        .collect();
    CircuitProgram {
        field: FieldSpec {
            name,
            modulus_decimal,
        },
        vars,
        constraints,
        witness_gen,
    }
}

/// Minimize one item stream's OWN constraints (its `Row`s) in isolation, pinning
/// the def interface (`base_pins` = plugs + outputs) plus every nested `Call`'s
/// plug vars — everything else is eliminated. Returns the reduced `Row`s followed
/// by the (unchanged) `Call`s. This is the per-template R1CS reduction that avoids
/// materializing and pruning the full flat R1CS: each template's internal
/// redundancy (identical across all its instances) is removed once, here.
fn minimize_items(
    items: &[CItem],
    base_pins: &BTreeMap<u32, ()>,
    name: &str,
    modulus: &str,
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
                // A CALL's plug LCs reference vars in THIS body; pin every one so
                // the per-template minimizer keeps the call interface intact.
                for lc in plugs {
                    pins.extend(lc.terms.iter().map(|t| t.var));
                }
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
    // Per-template bodies are small, so the fill-in guard is unnecessary here and
    // only leaves reductions on the table — minimize each template fully.
    let reduced = crate::minimize::minimize_with_fill(&prog, usize::MAX);
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

/// Like [`expand_function_blob`] but produces the **minimized** R1CS directly:
/// minimize each template body once (per-template, cheap) and expand the reduced
/// templates, instead of expanding the full flat R1CS and minimizing that. The
/// witness program is left empty — this is the Groth16 (R1CS) view; the solver
/// loads the full circuit separately.
pub fn expand_function_blob_reduced(b: &[u8]) -> Result<CircuitProgram, String> {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| expand_reduced_inner(b)));
    std::panic::set_hook(prev);
    out.map_err(|_| "malformed function artifact (XBC reduced decode failed)".to_string())
}

fn expand_reduced_inner(b: &[u8]) -> CircuitProgram {
    let mut p = 6usize;
    let name = get_str(b, &mut p);
    let modulus_decimal = get_str(b, &mut p);
    let num_vars = get_uv(b, &mut p) as usize;
    let num_inputs = get_uv(b, &mut p) as usize;
    let mut roles = vec![VarRole::Derived; num_vars];
    let mut names: Vec<Option<String>> = vec![None; num_vars];
    for id in 0..num_inputs {
        roles[id] = byte_role(b[p]);
        p += 1;
        names[id] = Some(get_str(b, &mut p));
    }
    let n_defs = get_uv(b, &mut p) as usize;
    let mut defs: Vec<GDef> = Vec::with_capacity(n_defs);
    for _ in 0..n_defs {
        let base_var = get_uv(b, &mut p) as u32;
        let plugs = get_ids(b, &mut p);
        let outputs = get_ids(b, &mut p);
        let c_items = parse_c_items(b, &mut p);
        let w_items = parse_w_items(b, &mut p);
        defs.push(GDef {
            base_var,
            plugs,
            outputs,
            c_items,
            w_items,
        });
    }
    let top_c = parse_c_items(b, &mut p);
    let _top_w = parse_w_items(b, &mut p);
    let keep_extra: std::collections::BTreeSet<u32> = get_ids(b, &mut p).into_iter().collect();

    // Reduce each template body once (plugs + outputs pinned), and the top stream
    // (inputs pinned). `expand_c` on the reduced defs yields the minimized R1CS.
    for def in &mut defs {
        let base_pins: BTreeMap<u32, ()> = def
            .plugs
            .iter()
            .chain(def.outputs.iter())
            .map(|&v| (v, ()))
            .collect();
        def.c_items = minimize_items(&def.c_items, &base_pins, &name, &modulus_decimal);
    }
    let input_pins: BTreeMap<u32, ()> = (0..num_inputs as u32).map(|v| (v, ())).collect();
    let top_reduced = minimize_items(&top_c, &input_pins, &name, &modulus_decimal);

    let mut constraints = Vec::new();
    expand_c(
        &defs,
        &top_reduced,
        &|v| LinearCombination::var(v),
        &mut constraints,
    );
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
    let keep = |id: usize| -> bool {
        id < num_inputs || referenced.contains(&(id as u32)) || keep_extra.contains(&(id as u32))
    };
    let vars = (0..num_vars)
        .filter(|&id| keep(id))
        .map(|id| Var {
            id: id as u32,
            name: names[id].take().unwrap_or_else(|| format!("v{id}")),
            role: roles[id].clone(),
        })
        .collect();
    CircuitProgram {
        field: FieldSpec {
            name,
            modulus_decimal,
        },
        vars,
        constraints,
        witness_gen: Vec::new(),
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

    /// A def whose body references its two plugs (`10`, `11`) and its own internal
    /// vars (`>= base_var`), plus a nested `Rolled` run — so expanding a `Call`
    /// exercises the plug substitution and internal-var shift.
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

    /// Build a top-level stream with many independent items (plain rows, rolled
    /// runs, and calls to the def at distinct absolute bases with distinct plug
    /// LCs) — enough items to span several rayon chunks.
    fn top_streams() -> (Vec<CItem>, Vec<WItem>) {
        let mut c = Vec::new();
        let mut w = Vec::new();
        for i in 0..200u32 {
            c.push(CItem::Row(row(i, i + 1, i + 2)));
            c.push(CItem::Rolled(vec![
                row(i, i, i + 5),
                row(i + 1, i + 1, i + 6),
            ]));
            // Fresh base per call, disjoint blocks (mirrors the encoder's monotonic
            // allocation); plug LCs reference distinct caller vars.
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
}
