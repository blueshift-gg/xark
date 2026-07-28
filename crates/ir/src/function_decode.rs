//! Decoder for the DAG-compact `XBC` (version 1) circuit artifact.
//!
//! Decode half of `lower_mir::build_function_blob`; lives in `xark-ir` so both the
//! `xark` CLI and the compiler can reach it. Parses the container (function defs +
//! top-level streams) and expands it to a full [`CircuitProgram`], the same shape a
//! flat `circuit.xbc` yields. Wire format is defined jointly with the encoder; both
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

/// Primary output var of a witness op (mirrors `lower_mir::witness_gen_out`);
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
        WitnessGen::ModInverse { out, .. } => *out.first().unwrap_or(&0),
        WitnessGen::Sub2 { qabs, .. } => *qabs,
    }
}

// Substitution: internals shift base+offset; plug vars map to plug LCs.
/// Substitute an LC under `s`: each term `coeff·var` becomes `coeff · s(var)`.
/// Mirrors `lower_mir::replay_function`'s `subst_lc`, so a bytecode CALL expands
/// byte-identically to a walked replay.
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
/// internals, so `s` yields a bare `1·v` LC. (Invariant relied on here.)
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

/// Build the substitution for a CALL: plug var → caller's (already
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
/// Parse a rolled-CALL block (tag `3`, loop fusion) and expand it to the
/// `count · period` individual CALLs it stands for. Iteration `k` of template `j`
/// gets `base = base0 + k·base_step` and each plug-LC term var `var0 + k·var_step`
/// (coeffs/constants loop-invariant). Expanding at parse time keeps the rolled form
/// BYTE-IDENTICAL to the unrolled CALL tokens. Mirrors `lower_mir::put_rolled_call`.
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

/// Top-level (identity) substitution. Kept as a named `fn` (not a closure) so it is
/// `Send + Sync + Copy` and can be handed to rayon workers during parallel expansion.
fn identity_lc(v: u32) -> LinearCombination {
    LinearCombination::var(v)
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
/// (absolute out/id vars, identity-substituted input LCs), so parallel expansion
/// concatenated in order equals the serial walk.
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

/// Streaming twin of [`expand_c`]: emits each expanded R1CS row to `emit`
/// instead of collecting into a `Vec`, so a consumer never materializes the flat
/// system.
fn expand_c_visit(
    defs: &[GDef],
    items: &[CItem],
    subst: &dyn Fn(u32) -> LinearCombination,
    emit: &mut dyn FnMut(R1csRow),
) {
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

fn decode_compact(b: &[u8]) -> CompactDecoded {
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
    let vars = (0..num_vars)
        .map(|id| Var {
            id: id as u32,
            name: names[id].take().unwrap_or_else(|| format!("v{id}")),
            role: roles[id].clone(),
        })
        .collect();
    (
        FieldSpec {
            name,
            modulus_decimal,
        },
        vars,
        defs,
        top_c,
        top_w,
        keep_extra,
        num_inputs,
    )
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
    let assign = solve_streamed(&vars, &defs, &top_w, &modulus, inputs)?;
    // Each top-level item is an independent constraint shard (absolute var ids),
    // so evaluate them in parallel against the shared read-only assignment,
    // streaming+dropping rows within each shard. Short-circuits on first failure.
    use rayon::prelude::*;
    let ok = top_c.par_iter().all(|item| {
        let mut shard_ok = true;
        expand_c_visit(
            &defs,
            std::slice::from_ref(item),
            &identity_lc,
            &mut |row: R1csRow| {
                if shard_ok
                    && !crate::solver::row_satisfied(&row.a, &row.b, &row.c, &assign, &modulus)
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

/// Decode just the variable table (roles + names) from a function blob, without
/// expanding any constraints — cheap input resolution for a streaming check.
pub fn decode_vars(b: &[u8]) -> Vec<Var> {
    decode_compact(b).1
}

/// Stream the constraints and total the **distinct-variable references** across
/// all rows — the volume a single-pass streaming analyzer (per-var univariate
/// accumulation) would have to store (~3 field elements each). Returns
/// `(rows, total_refs)`. Diagnostic: tells us whether streaming the analyzer can
/// beat materializing the flat constraints, before building it.
pub fn stream_ref_count(b: &[u8]) -> (usize, usize) {
    use rayon::prelude::*;
    let (_field, _vars, defs, top_c, _top_w, _keep, _num_inputs) = decode_compact(b);
    top_c
        .par_iter()
        .map(|item| {
            let (mut rows, mut refs) = (0usize, 0usize);
            expand_c_visit(
                &defs,
                std::slice::from_ref(item),
                &identity_lc,
                &mut |row: R1csRow| {
                    rows += 1;
                    let mut seen = std::collections::BTreeSet::new();
                    for lc in [&row.a, &row.b, &row.c] {
                        for t in &lc.terms {
                            seen.insert(t.var);
                        }
                    }
                    refs += seen.len();
                },
            );
            (rows, refs)
        })
        .reduce(|| (0, 0), |a, b| (a.0 + b.0, a.1 + b.1))
}

// Per-variable classification flags accumulated by the streaming pass 1.
const F_SEEN: u8 = 1; // some constraint references this var
const F_RESTRICTED: u8 = 2; // some referencing row has a≠0 or b≠0 (var not free)
const F_PINNED: u8 = 4; // some referencing row is linear in the var (a=0, b≠0)

/// Fold one row's contribution into the per-variable classification flags. For
/// each distinct variable the row references, reduce the row to its univariate
/// `A·v² + B·v + C` (fixing all other vars to the witness) and OR in: `SEEN`
/// always; `RESTRICTED` if `A≠0 ∨ B≠0`; `PINNED` if the row is linear in the var
/// (`A=0 ∧ B≠0`). `fetch_or` is commutative, so this is safe to call from
/// parallel shards in any order.
fn apply_row_flags(
    row: &R1csRow,
    assign: &std::collections::BTreeMap<u32, crate::solver::Fp>,
    modulus: &num_bigint::BigUint,
    flags: &[std::sync::atomic::AtomicU8],
) {
    use std::sync::atomic::Ordering;
    // Distinct vars in this row (a var in several LCs reduces once).
    let mut seen = std::collections::BTreeSet::new();
    for lc in [&row.a, &row.b, &row.c] {
        for t in &lc.terms {
            seen.insert(t.var);
        }
    }
    for v in seen {
        let (a, b, _c) = crate::solver::univariate_r1cs(row, v, assign, modulus);
        let mut bits = F_SEEN;
        if !(a.is_zero() && b.is_zero()) {
            bits |= F_RESTRICTED;
            if a.is_zero() {
                bits |= F_PINNED;
            }
        }
        flags[v as usize].fetch_or(bits, Ordering::Relaxed);
    }
}

/// Streaming pass 1: classify every variable with a **dense flag byte** while
/// (optionally) checking satisfiability, in a single parallel sweep of the
/// compact constraint stream. Returns the flag array (indexed by var id) and
/// whether every row `a·b = c` held.
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
    assign: &std::collections::BTreeMap<u32, crate::solver::Fp>,
    modulus: &num_bigint::BigUint,
    num_vars: usize,
    check_sat: bool,
) -> (Vec<std::sync::atomic::AtomicU8>, bool) {
    use rayon::prelude::*;
    use std::sync::atomic::AtomicU8;
    let flags: Vec<AtomicU8> = (0..num_vars).map(|_| AtomicU8::new(0)).collect();
    let sat_ok = top_c
        .par_iter()
        .map(|item| {
            let mut shard_ok = true;
            expand_c_visit(
                defs,
                std::slice::from_ref(item),
                &identity_lc,
                &mut |row: R1csRow| {
                    if check_sat
                        && shard_ok
                        && !crate::solver::row_satisfied(&row.a, &row.b, &row.c, assign, modulus)
                    {
                        shard_ok = false;
                    }
                    apply_row_flags(&row, assign, modulus, &flags);
                },
            );
            shard_ok
        })
        .reduce(|| true, |x, y| x && y);
    (flags, sat_ok)
}

/// Streaming pass 2 (rare path): re-stream the constraints, gathering each
/// *suspect* var's univariate `(a,b,c)` reductions, then run the exact flat
/// two-valued test on that small set. Suspects are vars that survived pass 1
/// restricted-but-unpinned — for a well-constrained circuit this set is empty
/// and pass 2 never runs. Returns the subset that is genuinely two-valued.
fn two_valued_suspects(
    defs: &[GDef],
    top_c: &[CItem],
    assign: &std::collections::BTreeMap<u32, crate::solver::Fp>,
    modulus: &num_bigint::BigUint,
    suspects: &std::collections::BTreeSet<u32>,
) -> std::collections::BTreeSet<u32> {
    use crate::solver::Fp;
    // Gather every suspect's referencing rows (small: |suspects| is tiny).
    let mut polys: std::collections::BTreeMap<u32, Vec<(Fp, Fp, Fp)>> =
        suspects.iter().map(|&v| (v, Vec::new())).collect();
    expand_c_visit(defs, top_c, &identity_lc, &mut |row: R1csRow| {
        let mut seen = std::collections::BTreeSet::new();
        for lc in [&row.a, &row.b, &row.c] {
            for t in &lc.terms {
                if suspects.contains(&t.var) {
                    seen.insert(t.var);
                }
            }
        }
        for v in seen {
            polys
                .get_mut(&v)
                .unwrap()
                .push(crate::solver::univariate_r1cs(&row, v, assign, modulus));
        }
    });
    two_valued_from_polys(&polys, assign, modulus)
}

/// The exact flat two-valued test over already-gathered per-suspect univariate
/// reductions: a suspect is under-constrained iff some second root `β≠α`
/// satisfies *all* of its rows. Mirrors `analyze_*_cp`'s candidate loop. Runs in
/// parallel over the (tiny) suspect set.
fn two_valued_from_polys(
    polys: &std::collections::BTreeMap<
        u32,
        Vec<(crate::solver::Fp, crate::solver::Fp, crate::solver::Fp)>,
    >,
    assign: &std::collections::BTreeMap<u32, crate::solver::Fp>,
    modulus: &num_bigint::BigUint,
) -> std::collections::BTreeSet<u32> {
    use crate::solver::Fp;
    use rayon::prelude::*;
    polys
        .par_iter()
        .filter_map(|(&v, ps)| {
            let alpha = assign.get(&v).cloned().unwrap_or_else(|| Fp::zero(modulus));
            let mut candidates: Vec<Fp> = Vec::new();
            for (a, b, _c) in ps {
                if a.is_zero() {
                    continue;
                }
                let inv_a = a.inverse().expect("a != 0 in quadratic branch");
                candidates.push(b.neg().mul(&inv_a).sub(&alpha));
            }
            for beta in &candidates {
                if *beta == alpha {
                    continue;
                }
                let satisfies_all = ps
                    .iter()
                    .all(|(a, b, c)| a.mul(beta).mul(beta).add(&b.mul(beta)).add(c).is_zero());
                if satisfies_all {
                    return Some(v);
                }
            }
            None
        })
        .collect()
}

/// Core streaming soundness pass shared by [`stream_analyze`] and
/// [`stream_verify`]: classify (pass 1) + optional satisfiability check, then
/// resolve the rare suspects (pass 2), and assemble the under-constraint list in
/// var-id order. Peak extra memory over the witness is one flag byte per var (a
/// few MB) plus the tiny suspect set — never the flat constraint system.
#[allow(clippy::too_many_arguments)]
fn stream_underconstrained(
    defs: &[GDef],
    top_c: &[CItem],
    vars: &[Var],
    keep_extra: &std::collections::BTreeSet<u32>,
    assign: &std::collections::BTreeMap<u32, crate::solver::Fp>,
    modulus: &num_bigint::BigUint,
    check_sat: bool,
) -> (bool, Vec<crate::solver::UnderConstrained>) {
    let (flags, sat_ok) = classify_and_check(defs, top_c, assign, modulus, vars.len(), check_sat);
    let suspects = select_suspects(&flags, vars);
    let two_valued = if suspects.is_empty() {
        std::collections::BTreeSet::new()
    } else {
        two_valued_suspects(defs, top_c, assign, modulus, &suspects)
    };
    let out = assemble_underconstrained(&flags, vars, keep_extra, &two_valued);
    (sat_ok, out)
}

/// Vars that survived pass-1 classification restricted-but-never-pinned — the
/// only ones that need the (expensive, rare) pass-2 two-valued test.
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
    let assign = solve_streamed(&vars, &defs, &top_w, &modulus, inputs)?;
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
    let assign = solve_streamed(&vars, &defs, &top_w, &modulus, inputs)?;
    let (sat_ok, out) =
        stream_underconstrained(&defs, &top_c, &vars, &keep_extra, &assign, &modulus, true);
    if !sat_ok {
        return Err("a constraint is unsatisfied".to_string());
    }
    Ok((assign, out))
}

/// Count the R1CS constraints by **streaming** them out of the compact bytecode
/// (never materializing the flat `Vec`). Same count as
/// `expand_function_blob(b).constraints.len()`, but at a tiny fraction of the
/// resident set — the memory-win measurement point. Parallel over shards.
pub fn stream_count_constraints(b: &[u8]) -> usize {
    use rayon::prelude::*;
    let (_field, _vars, defs, top_c, _top_w, _keep, _num_inputs) = decode_compact(b);
    top_c
        .par_iter()
        .map(|item| {
            let mut n = 0usize;
            expand_c_visit(
                &defs,
                std::slice::from_ref(item),
                &identity_lc,
                &mut |_row| n += 1,
            );
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
    let (_field, _vars, defs, top_c, _top_w, _keep, _num_inputs) = decode_compact(b);
    top_c
        .par_iter()
        .map(|item| {
            let mut n = 0usize;
            expand_c_visit(
                &defs,
                std::slice::from_ref(item),
                &identity_lc,
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
    let (_field, _vars, defs, _top_c, top_w, _keep, _num_inputs) = decode_compact(b);
    let mut n = 0usize;
    expand_w_visit(&defs, &top_w, &identity_lc, &mut |_op| n += 1);
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
    let (_field, _vars, defs, top_c, _top_w, _keep, _num_inputs) = decode_compact(b);
    // FNV-1a 128-bit offset basis.
    let mut acc: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
    expand_c_visit(&defs, &top_c, &identity_lc, &mut |row: R1csRow| {
        digest_lc(&mut acc, &row.a);
        digest_lc(&mut acc, &row.b);
        digest_lc(&mut acc, &row.c);
        fnv1a_128(&mut acc, b"\n");
    });
    acc
}

/// **Build-time faithfulness gate, streamed.** Verify that the just-built compact
/// artifact `blob` expands byte-identically to the flat lowering (`r1cs` +
/// `prim`) — same R1CS rows, same (pruned) witness ops, same (pruned) var table —
/// WITHOUT materializing a second `CircuitProgram` on either side. The artifact's
/// rows/ops are streamed out of the bytecode and compared in place against the
/// already-held flat structures; only a dense referenced-var bitset (for the
/// prune) is allocated. Returns `(constraints, witness_ops, vars)` on success, or
/// a precise diff `Err`. Replaces the ~2 GB `from_lowered` + `expand_function_blob`
/// pair the driver's `XARK_VERIFY` used to build.
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
    expand_c_visit(&defs, &top_c, &identity_lc, &mut |row: R1csRow| {
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
    expand_w_visit(&defs, &top_w, &identity_lc, &mut |op: WitnessGen| {
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

/// Streaming twin of [`expand_w`]: emits each witness-gen op to `emit` in the
/// same topological order (dependencies before uses) instead of collecting the
/// whole `Vec<WitnessGen>`. Lets the solver consume ops in bounded batches so the
/// fully-expanded hint program (the dominant footprint on heavy non-native EC
/// circuits — GBs of substituted `LinearCombination`s) is never materialized.
fn expand_w_visit(
    defs: &[GDef],
    items: &[WItem],
    subst: &dyn Fn(u32) -> LinearCombination,
    emit: &mut dyn FnMut(WitnessGen),
) {
    for it in items {
        match it {
            WItem::Row(w) => {
                let mut w = w.clone();
                subst_witness(&mut w, subst);
                emit(w);
            }
            WItem::Rolled(wits) => {
                for w in wits {
                    let mut w = w.clone();
                    subst_witness(&mut w, subst);
                    emit(w);
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

/// Solve the witness by **streaming** the hint program: expand the top-level
/// witness items op-by-op (topological order) and feed them to the batched
/// solver, which never holds more than one batch of ops at a time. Produces the
/// identical assignment to `expand_w_top` + `solve`, at a fraction of the peak
/// (the full expanded `Vec<WitnessGen>` is the bulk of a heavy EC circuit's RSS).
fn solve_streamed(
    vars: &[Var],
    defs: &[GDef],
    top_w: &[WItem],
    modulus: &num_bigint::BigUint,
    inputs: &BTreeMap<u32, String>,
) -> Result<BTreeMap<u32, crate::solver::Fp>, String> {
    crate::solver::solve_witness_streamed(vars, modulus, inputs, |sink| {
        expand_w_visit(defs, top_w, &identity_lc, &mut |op| sink(op));
    })
    .map_err(|e| format!("solve: {e:?}"))
}

/// Parse an `XBC` (version 1) container and expand it to a full `CircuitProgram`.
/// The 6-byte header (`XBC` + `0x0001`) is assumed already dispatched on.
///
/// Total: a `circuit.xbc` may be foreign or corrupted, so this must never crash the
/// process — it catches the inner parser's bounds/utf8/tag panics and returns a clean
/// `Err`. (Fuzzed by `gadgets/tests/tests/fuzz.rs`.)
pub fn expand_function_blob(b: &[u8]) -> Result<CircuitProgram, String> {
    expand_function_blob_impl(b)
}

fn expand_function_blob_impl(b: &[u8]) -> Result<CircuitProgram, String> {
    // Silence the panic printer for the expected-on-malformed-input inner panics,
    // then restore it, so a bad artifact yields one clean error line. Decode is
    // sequential in setup/prove, so swapping the process-global hook is safe; rayon
    // fan-out panics propagate to this thread and are caught here too.
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
    // First `num_inputs` vars are signature inputs (role + name); all others `Derived`.
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

/// Minimize one item stream's own `Row`s in isolation, pinning the def interface
/// (`base_pins` = plugs + outputs) plus every nested `Call`'s plug vars; everything
/// else is eliminated. Returns reduced `Row`s then the unchanged `Call`s. Per-template
/// reduction: each template's internal redundancy is removed once, here, avoiding
/// materializing and pruning the full flat R1CS.
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
                // Plug LCs reference vars in this body; pin them so the minimizer
                // keeps the call interface intact.
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
    // Per-template bodies are small; skip the fill-in guard and minimize fully.
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

/// Like [`expand_function_blob`] but produces the minimized R1CS directly: minimize
/// each template body once and expand the reduced templates, instead of expanding the
/// full flat R1CS and minimizing that. Witness program left empty — this is the
/// Groth16 (R1CS) view; the solver loads the full circuit separately.
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

    // Reduce each template body (plugs + outputs pinned) and the top stream (inputs
    // pinned); `expand_c` on the reduced defs then yields the minimized R1CS.
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
        let flags: Vec<AtomicU8> = (0..vars.len()).map(|_| AtomicU8::new(0)).collect();
        for r in rows {
            apply_row_flags(r, assign, modulus, &flags);
        }
        let suspects = select_suspects(&flags, vars);
        let mut polys: std::collections::BTreeMap<u32, Vec<(Fp, Fp, Fp)>> =
            suspects.iter().map(|&v| (v, Vec::new())).collect();
        for r in rows {
            let mut seen = std::collections::BTreeSet::new();
            for lc in [&r.a, &r.b, &r.c] {
                for t in &lc.terms {
                    if suspects.contains(&t.var) {
                        seen.insert(t.var);
                    }
                }
            }
            for v in seen {
                polys
                    .get_mut(&v)
                    .unwrap()
                    .push(crate::solver::univariate_r1cs(r, v, assign, modulus));
            }
        }
        let two_valued = two_valued_from_polys(&polys, assign, modulus);
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
    /// soundness-equivalence test.
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
        ];
        // r0: a·b = p ; r1: bit·(bit−1) = 0
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
        ];
        // Satisfying witness: 3·4 = 12, bit = 0, dangling = 0.
        let assign: std::collections::BTreeMap<u32, Fp> = [
            (0u32, fp(3)),
            (1, fp(4)),
            (2, fp(12)),
            (3, fp(0)),
            (4, fp(0)),
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
        assert!(
            !stream.iter().any(|(v, _)| *v == 2),
            "pinned var must be clean"
        );
    }
}
