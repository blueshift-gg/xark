//! Finishing a lowered circuit: dead-code pruning, the flat R1CS + primitive views,
//! the pinning gate, and the compact `circuit.xbc` container.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use xark_ir::primitive::{self, PrimitiveProgram, WitnessGen};
use xark_ir::{
    ConstraintKind, ConstraintProfile, FieldSpec, LinearCombination, R1csConstraint, R1csProgram,
    VarId, Variable, Visibility,
};

use crate::builder::Builder;
use crate::error::{CompileError, CompileResult};

pub struct LowerOutput {
    /// Fully-lowered R1CS (a·b=c) — kept for the DOT graph and debugging.
    pub r1cs: R1csProgram,
    /// Primitive IR (AssertZero expressions + witness-gen hint program) — the
    /// artifact the backend lowering consumes.
    pub primitive: PrimitiveProgram,
    /// Per-constraint profiling attribution, index-aligned with
    /// `r1cs.constraints`. Empty unless profiling was requested (`--profile`).
    /// Emitted to a **separate** `profile.json`; never mixed into the R1CS.
    pub profile: Vec<ConstraintProfile>,
    /// `circuit.xbc`: the DAG-compact `VERSION_FUNCTION` container (see
    /// `build_function_blob`), written verbatim.
    pub xbc: Vec<u8>,
    /// Vars allocated inside a `witness_only` region — exempt from `check_pinning`
    /// (pure witness-gen scratch feeding a downstream, separately-pinned result).
    pub witness_only_vars: BTreeSet<VarId>,
}

/// A template def: the rows `c0..c1` and witness ops `w0..w1` of its first call,
/// in that call's coordinates — internals from `base_var`, everything from outside
/// through `plug_vars`. Repeated sub-calls inside it are nested [`FunctionCall`]s.
pub(crate) struct FunctionTemplate {
    pub(crate) c0: usize,
    pub(crate) c1: usize,
    pub(crate) w0: usize,
    pub(crate) w1: usize,
    pub(crate) base_var: VarId,
    pub(crate) plug_vars: Vec<VarId>,
    /// Internal vars something outside a call reads (template coordinates).
    pub(crate) outputs: Vec<VarId>,
}

/// One call of a template def: at the top level, or inside the body of `parent`
/// (then in that def's coordinates — its first call's).
#[derive(Clone)]
pub(crate) struct FunctionCall {
    pub(crate) def: u32,
    pub(crate) parent: Option<u32>,
    pub(crate) c0: usize,
    pub(crate) c1: usize,
    pub(crate) w0: usize,
    pub(crate) w1: usize,
    pub(crate) base: VarId,
    pub(crate) plugs: Vec<LinearCombination>,
}

/// Like [`remap_witness_vars`], but *substitutes* linear combinations for the LC
/// input fields (plug vars → caller plug LCs) while var-remapping the `out`/id
/// fields (always fresh internals). `f` shifts internal out/id vars; `s`
/// substitutes an LC input. Used by symbolic function replay so witness ops read the
/// caller's argument LCs directly, with no plug materialization.
pub(crate) fn subst_witness_vars(
    w: &mut WitnessGen,
    f: &dyn Fn(VarId) -> VarId,
    s: &dyn Fn(&LinearCombination) -> LinearCombination,
) {
    let ids = |v: &mut [VarId]| {
        for x in v {
            *x = f(*x);
        }
    };
    let subst = |v: &mut [LinearCombination]| {
        for l in v {
            *l = s(l);
        }
    };
    match w {
        WitnessGen::Product { out, left, right } => {
            *out = f(*out);
            *left = s(left);
            *right = s(right);
        }
        WitnessGen::Linear { out, lc: l } => {
            *out = f(*out);
            *l = s(l);
        }
        WitnessGen::Xor { out, a, b } | WitnessGen::Or { out, a, b } => {
            *out = f(*out);
            *a = s(a);
            *b = s(b);
        }
        WitnessGen::Inverse { out, input } | WitnessGen::InverseOrZero { out, input } => {
            *out = f(*out);
            *input = s(input);
        }
        WitnessGen::Bit { out, input, .. } => {
            *out = f(*out);
            *input = s(input);
        }
        WitnessGen::Bits { outs, input } => {
            ids(outs);
            *input = s(input);
        }
        WitnessGen::DivRem { q, r, num, den } => {
            *q = f(*q);
            *r = f(*r);
            *num = s(num);
            *den = s(den);
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
            subst(a);
            subst(b);
            subst(modulus);
        }
        WitnessGen::ModInverse {
            out, a, modulus, ..
        } => {
            ids(out);
            subst(a);
            subst(modulus);
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
            *qabs = f(*qabs);
            ids(r);
            subst(a);
            subst(b);
            subst(c);
            subst(modulus);
        }
    }
}

/// Compact (DAG/function) codegen — capture reusable functions, replay them, and
/// write the DAG-compact `circuit.xbc`. This is the primary codegen: it is
/// R1CS-neutral (the artifact expands byte-identically, so vks/proofs are
/// unchanged) while cutting build time and artifact size.
// stream byte-for-byte. Same varint density as the flat `.xbc`, so file sizes are
// directly comparable.
fn put_uv(buf: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            buf.push(b);
            break;
        }
        buf.push(b | 0x80);
    }
}
fn put_iv(buf: &mut Vec<u8>, v: i64) {
    put_uv(buf, ((v << 1) ^ (v >> 63)) as u64); // zigzag
}
thread_local! {
    /// The container's constant pool (value → index) while its body is written.
    static POOL: std::cell::RefCell<std::sync::Arc<BTreeMap<xark_ir::FieldConst, u32>>> =
        std::cell::RefCell::new(Default::default());
}
fn pool() -> std::sync::Arc<BTreeMap<xark_ir::FieldConst, u32>> {
    POOL.with(|p| p.borrow().clone())
}
fn put_fc(buf: &mut Vec<u8>, fc: &xark_ir::FieldConst) {
    if fc.as_i64().is_none()
        && let Some(i) = POOL.with(|p| p.borrow().get(fc).copied())
    {
        buf.push(3);
        put_uv(buf, u64::from(i));
        return;
    }
    match fc.as_i64() {
        // A power of two ≥ 2^7 (a bit-sum coefficient) as its exponent.
        Some(v) if v.unsigned_abs() >= 128 && v.unsigned_abs().is_power_of_two() => {
            buf.push(if v < 0 { 5 } else { 4 });
            put_uv(buf, u64::from(v.unsigned_abs().trailing_zeros()));
        }
        Some(v) => {
            buf.push(0);
            put_iv(buf, v);
        }
        None => {
            // Sign + length + little-endian magnitude (version 2; 32 bytes for a
            // full field element instead of ~77 decimal digits).
            let (sign, mag) = fc.big().to_bytes_le();
            buf.push(2);
            buf.push(if sign == num_bigint::Sign::Minus {
                2
            } else {
                1
            });
            put_uv(buf, mag.len() as u64);
            buf.extend_from_slice(&mag);
        }
    }
}
/// An LC: constant, term count, then each term's coefficient and its var as a
/// zigzag delta from the previous term's (version 2).
fn put_lc_g(buf: &mut Vec<u8>, lc: &LinearCombination) {
    put_fc(buf, &lc.constant);
    put_uv(buf, lc.terms.len() as u64);
    let mut prev = 0i64;
    for t in &lc.terms {
        put_fc(buf, &t.coeff);
        put_iv(buf, i64::from(t.var) - prev);
        prev = i64::from(t.var);
    }
}
pub(crate) fn put_row_g(buf: &mut Vec<u8>, c: &R1csConstraint) {
    put_lc_g(buf, &c.a);
    put_lc_g(buf, &c.b);
    put_lc_g(buf, &c.c);
}
/// A var list, each as a zigzag delta from the previous one (version 2).
fn put_ids_g(buf: &mut Vec<u8>, ids: &[VarId]) {
    put_uv(buf, ids.len() as u64);
    let mut prev = 0i64;
    for &v in ids {
        put_iv(buf, i64::from(v) - prev);
        prev = i64::from(v);
    }
}
/// Serialize one `WitnessGen` op with the same local primitives the function
/// encoder uses for constraints (`put_fc`/`put_lc_g`/`put_uv`), so the compact
/// blob is self-contained and decodable by [`get_witness_g`].
pub(crate) fn put_witness_g(buf: &mut Vec<u8>, w: &WitnessGen) {
    put_witness_with(buf, w, &mut |buf, l| put_lc_g(buf, l));
}
/// [`put_witness_g`] with every LC written by `lc` (a back-reference writer for
/// tag `8` ops).
fn put_witness_with(
    buf: &mut Vec<u8>,
    w: &WitnessGen,
    put: &mut dyn FnMut(&mut Vec<u8>, &LinearCombination),
) {
    let lcs = |buf: &mut Vec<u8>,
               v: &[LinearCombination],
               put: &mut dyn FnMut(&mut Vec<u8>, &LinearCombination)| {
        put_uv(buf, v.len() as u64);
        for l in v {
            put(buf, l);
        }
    };
    match w {
        WitnessGen::Product { out, left, right } => {
            buf.push(0);
            put_uv(buf, u64::from(*out));
            put(buf, left);
            put(buf, right);
        }
        WitnessGen::Linear { out, lc } => {
            buf.push(1);
            put_uv(buf, u64::from(*out));
            put(buf, lc);
        }
        WitnessGen::Xor { out, a, b } => {
            buf.push(2);
            put_uv(buf, u64::from(*out));
            put(buf, a);
            put(buf, b);
        }
        WitnessGen::Or { out, a, b } => {
            buf.push(3);
            put_uv(buf, u64::from(*out));
            put(buf, a);
            put(buf, b);
        }
        WitnessGen::Inverse { out, input } => {
            buf.push(4);
            put_uv(buf, u64::from(*out));
            put(buf, input);
        }
        WitnessGen::InverseOrZero { out, input } => {
            buf.push(5);
            put_uv(buf, u64::from(*out));
            put(buf, input);
        }
        WitnessGen::Bit { out, input, index } => {
            buf.push(6);
            put_uv(buf, u64::from(*out));
            put(buf, input);
            put_uv(buf, u64::from(*index));
        }
        WitnessGen::Bits { outs, input } => {
            buf.push(7);
            put_ids_g(buf, outs);
            put(buf, input);
        }
        WitnessGen::DivRem { q, r, num, den } => {
            buf.push(8);
            put_uv(buf, u64::from(*q));
            put_uv(buf, u64::from(*r));
            put(buf, num);
            put(buf, den);
        }
        WitnessGen::MulModDivMod {
            q,
            r,
            a,
            b,
            modulus,
            limb_bits,
        } => {
            buf.push(9);
            put_ids_g(buf, q);
            put_ids_g(buf, r);
            lcs(buf, a, put);
            lcs(buf, b, put);
            lcs(buf, modulus, put);
            put_uv(buf, u64::from(*limb_bits));
        }
        WitnessGen::ModInverse {
            out,
            a,
            modulus,
            limb_bits,
        } => {
            buf.push(10);
            put_ids_g(buf, out);
            lcs(buf, a, put);
            lcs(buf, modulus, put);
            put_uv(buf, u64::from(*limb_bits));
        }
        WitnessGen::Sub2 {
            qabs,
            r,
            a,
            b,
            c,
            modulus,
            limb_bits,
        } => {
            buf.push(11);
            put_uv(buf, u64::from(*qabs));
            put_ids_g(buf, r);
            lcs(buf, a, put);
            lcs(buf, b, put);
            lcs(buf, c, put);
            lcs(buf, modulus, put);
            put_uv(buf, u64::from(*limb_bits));
        }
    }
}

/// One item in a function body / top-level stream: a flat constraint, or a nested
/// CALL to another function def (its base/plugs in the *enclosing* def's coords).
enum GItem {
    Row(usize), // index into the flat constraint stream
    Call(u32, VarId, Vec<LinearCombination>),
}

// --- rolled CALL blocks (Stage 3: loop fusion for calls) ---------------------
// A loop that invokes cached function(s) each iteration emits one CALL item per
// invocation. With symbolic plugs those calls are AFFINE in the loop-carried vars
// (fixed per-iteration var stride), so a periodic run of CALL items compresses to
// a single rolled-CALL-block token — the CALL analogue of the flat-opcode roll
// (`bytecode::roll_and_encode_ops`), which only compresses runs of inline rows.
//
// A block has a `period` of `p` call templates (the loop body's calls, in order)
// repeated `count` times. Iteration `k` of template `j` reconstructs a plain CALL
// whose `base_var` and whose every plug-LC term var advance by that operand's
// constant step: `operand0 + k·step`. Coeffs and constants are loop-invariant
// (identical every iteration) so they are stored once. Expansion is BYTE-IDENTICAL
// to the unrolled CALLs — the encoder only rolls after verifying, iteration by
// iteration, that every operand reproduces exactly under the affine rule.
const MAX_CALL_PERIOD: usize = 1024;

/// One affine plug-LC template inside a rolled call: the loop-invariant constant
/// and, per term, its loop-invariant coeff plus the term var's `(var0, step)`.
struct PlugTemplate {
    constant: xark_ir::FieldConst,
    terms: Vec<(xark_ir::FieldConst, u32, i64)>, // (coeff, var0, var_step)
}
/// One call template in a rolled block (one call of the loop body).
struct CallTemplate {
    def: u32,
    base0: u32,
    base_step: i64,
    plugs: Vec<PlugTemplate>,
}
/// A rolled run of `count` repetitions of a `period`-length body of call templates.
struct RolledCall {
    count: u32,
    body: Vec<CallTemplate>,
}
/// The result of rolling a maximal run of consecutive CALL items: either a single
/// call (index into the enclosing item slice) or a rolled block.
enum CallTok {
    Single(usize),
    Rolled(RolledCall),
}

/// A call's structural signature (loop-invariant part): `def` + per-plug
/// `(constant, coeffs)`, serialized to bytes for fast exact comparison. Two calls
/// can share a rolled template iff their signatures are byte-equal.
fn call_sig(it: &GItem) -> Vec<u8> {
    let mut b = Vec::new();
    if let GItem::Call(d, _, plugs) = it {
        put_uv(&mut b, u64::from(*d));
        put_uv(&mut b, plugs.len() as u64);
        for lc in plugs {
            put_fc(&mut b, &lc.constant);
            put_uv(&mut b, lc.terms.len() as u64);
            for t in &lc.terms {
                put_fc(&mut b, &t.coeff);
            }
        }
    }
    b
}
/// A call's affine operands, in a fixed order: `base_var` then every plug-LC term
/// var (plug order, term order). These are the values that step per iteration.
fn call_operands(it: &GItem) -> Vec<i64> {
    let mut v = Vec::new();
    if let GItem::Call(_, base, plugs) = it {
        v.push(i64::from(*base));
        for lc in plugs {
            for t in &lc.terms {
                v.push(i64::from(t.var));
            }
        }
    }
    v
}

/// Try to roll the period-`p` block at `start` (in `sigs`/`ops`, the precomputed
/// signatures/operands of a maximal call run). Returns the maximal repeat count
/// (`≥ 2`) whose every operand reproduces `operand0 + k·step` exactly with matching
/// signatures, or `None`.
fn try_call_repeat(sigs: &[Vec<u8>], ops: &[Vec<i64>], start: usize, p: usize) -> Option<usize> {
    let n = sigs.len();
    if p == 0 || start + 2 * p > n {
        return None;
    }
    // Blocks 0 and 1 must be signature-identical, position by position.
    for j in 0..p {
        if sigs[start + p + j] != sigs[start + j]
            || ops[start + p + j].len() != ops[start + j].len()
        {
            return None;
        }
    }
    // Per-position, per-operand step from iteration 0 → 1.
    let steps: Vec<Vec<i64>> = (0..p)
        .map(|j| {
            ops[start + j]
                .iter()
                .zip(&ops[start + p + j])
                .map(|(a, b)| b - a)
                .collect()
        })
        .collect();
    // Extend while each further block reproduces exactly under the affine rule.
    let mut count = 2usize;
    while start + (count + 1) * p <= n {
        let base = start + count * p;
        let k = count as i64;
        let mut ok = true;
        for j in 0..p {
            if sigs[base + j] != sigs[start + j] || ops[base + j].len() != ops[start + j].len() {
                ok = false;
                break;
            }
            let matches = ops[start + j]
                .iter()
                .zip(&steps[j])
                .zip(&ops[base + j])
                .all(|((o0, s), actual)| o0 + k * s == *actual);
            if !matches {
                ok = false;
                break;
            }
        }
        if !ok {
            break;
        }
        count += 1;
    }
    Some(count)
}

/// Build a [`RolledCall`] for the period-`p`, `count`-repetition block at `start`
/// of `calls` (references to the run's consecutive CALL items). Iteration 0 gives
/// the loop-invariant coeffs/constants and the `var0`s; the per-operand step is the
/// iteration-0→1 delta.
fn build_rolled_call(calls: &[&GItem], start: usize, p: usize) -> RolledCall {
    let mut body = Vec::with_capacity(p);
    for j in 0..p {
        let GItem::Call(def, base0, plugs0) = calls[start + j] else {
            unreachable!("call run holds only Call items")
        };
        let o0 = call_operands(calls[start + j]);
        let o1 = call_operands(calls[start + p + j]);
        let steps: Vec<i64> = o0.iter().zip(&o1).map(|(a, b)| b - a).collect();
        // Operand index 0 is base; the rest map, in order, to plug term vars.
        let base_step = steps[0];
        let mut oi = 1usize;
        let plug_templates: Vec<PlugTemplate> = plugs0
            .iter()
            .map(|lc| {
                let terms = lc
                    .terms
                    .iter()
                    .map(|t| {
                        let step = steps[oi];
                        oi += 1;
                        (t.coeff.clone(), t.var, step)
                    })
                    .collect();
                PlugTemplate {
                    constant: lc.constant.clone(),
                    terms,
                }
            })
            .collect();
        body.push(CallTemplate {
            def: *def,
            base0: *base0,
            base_step,
            plugs: plug_templates,
        });
    }
    // count is recovered by the caller; store it there.
    RolledCall { count: 0, body }
}

/// Roll a maximal run of consecutive CALL items into `CallTok`s: greedily grab, at
/// each position, the block whose rolled span (`period · count`) is largest (ties
/// → smallest period), leaving un-rollable calls as singles. Correctness is
/// intrinsic: a block is only rolled after `try_call_repeat` proves every operand
/// reproduces exactly, so expansion is byte-identical to the flat calls.
fn roll_call_run(calls: &[&GItem]) -> Vec<CallTok> {
    let n = calls.len();
    let sigs: Vec<Vec<u8>> = calls.iter().map(|c| call_sig(c)).collect();
    let ops: Vec<Vec<i64>> = calls.iter().map(|c| call_operands(c)).collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < n {
        let maxp = ((n - i) / 2).min(MAX_CALL_PERIOD);
        let mut best: Option<(usize, usize)> = None; // (span, period)
        for p in 1..=maxp {
            if let Some(count) = try_call_repeat(&sigs, &ops, i, p) {
                let span = p * count;
                match best {
                    Some((bs, _)) if bs >= span => {}
                    _ => best = Some((span, p)),
                }
            }
        }
        if let Some((span, p)) = best {
            let count = span / p;
            let mut rolled = build_rolled_call(calls, i, p);
            rolled.count = count as u32;
            out.push(CallTok::Rolled(rolled));
            i += span;
        } else {
            out.push(CallTok::Single(i));
            i += 1;
        }
    }
    out
}

/// A plug that is a bare variable (`1·v`, no constant).
fn bare_var(lc: &LinearCombination) -> Option<VarId> {
    (lc.constant.is_zero() && lc.terms.len() == 1 && lc.terms[0].coeff.is_one())
        .then(|| lc.terms[0].var)
}
/// A CALL's plugs, version-2 form (mirrors `function_decode::get_plugs_compact`):
/// a bare variable is a delta from the previous one (initially `base`), anything
/// else a full LC.
fn put_plugs_compact(buf: &mut Vec<u8>, plugs: &[LinearCombination], base: VarId) {
    put_uv(buf, plugs.len() as u64);
    let mut prev = i64::from(base);
    for lc in plugs {
        match bare_var(lc) {
            Some(v) => {
                let d = i64::from(v) - prev;
                put_uv(buf, (((d << 1) ^ (d >> 63)) as u64) << 1);
                prev = i64::from(v);
            }
            None => {
                put_uv(buf, 1);
                put_lc_g(buf, lc);
            }
        }
    }
}
/// [`put_rolled_call`] with bare-variable plugs delta-coded (tag `6`; mirrors
/// `function_decode::parse_rolled_calls_compact`).
fn put_rolled_call_compact(buf: &mut Vec<u8>, r: &RolledCall) {
    put_uv(buf, u64::from(r.count));
    put_uv(buf, r.body.len() as u64);
    for t in &r.body {
        put_uv(buf, u64::from(t.def));
        put_uv(buf, u64::from(t.base0));
        put_iv(buf, t.base_step);
        put_uv(buf, t.plugs.len() as u64);
        let mut prev = i64::from(t.base0);
        for pt in &t.plugs {
            if pt.constant.is_zero() && pt.terms.len() == 1 && pt.terms[0].0.is_one() {
                let (_, var0, step) = &pt.terms[0];
                let d = i64::from(*var0) - prev;
                put_uv(buf, (((d << 1) ^ (d >> 63)) as u64) << 1);
                put_iv(buf, *step);
                prev = i64::from(*var0);
            } else {
                put_uv(buf, 1);
                put_fc(buf, &pt.constant);
                put_uv(buf, pt.terms.len() as u64);
                for (coeff, var0, step) in &pt.terms {
                    put_fc(buf, coeff);
                    put_uv(buf, u64::from(*var0));
                    put_iv(buf, *step);
                }
            }
        }
    }
}

// --- Complete DAG-compact circuit artifact ------------------------------------
// A self-contained container that expands to a full `CircuitProgram` (constraints
// + witness program + variable table): the sole `circuit.xbc` format.
// Header `MAGIC + 2u16`; the payload is a constant pool, function defs (whose
// bodies may call other defs) + top-level item streams (rows, function calls, and
// rolled periodic runs — see below).

/// The circuit-artifact container version. Version 2 is version 1 (the original
/// DAG-function container) encoded more densely — the same items, so
/// the same expansion: a constant pool after the inputs; big constants as binary
/// (or a pool index) and powers of two as exponents; var lists delta-coded; CALL
/// plugs delta-coded; the witness stream's CALLs referring to the constraint
/// stream's; rolled runs with varint counts/steps; and rows / witness ops that
/// refer back to an earlier row's LC instead of repeating it. Decoded by
/// `xark_ir::function_decode`, which reads both versions.
const VERSION_FUNCTION: u16 = 2;

fn vis_byte(v: &Visibility) -> u8 {
    match v {
        Visibility::Public => 0,
        Visibility::Private => 1,
        Visibility::Internal => 2,
    }
}
fn put_str(buf: &mut Vec<u8>, s: &str) {
    put_uv(buf, s.len() as u64);
    buf.extend_from_slice(s.as_bytes());
}
/// The row LCs (of ≥ 2 terms) of one scope's constraint stream, in stream order:
/// what a tag-`8` row or witness op refers back to instead of repeating an LC
/// (a witness op reads exactly the LCs of the row it solves; a big LC is often
/// used by several rows). Mirrors `function_decode`'s table.
struct LcTable<'a> {
    lcs: Vec<&'a LinearCombination>,
    /// The most recent earlier entry equal to entry `i`.
    prev_same: Vec<Option<u32>>,
    last: HashMap<u64, Vec<u32>>,
}

fn lc_hash(l: &LinearCombination) -> u64 {
    let mut h = std::hash::DefaultHasher::new();
    use std::hash::{Hash, Hasher};
    for t in &l.terms {
        t.var.hash(&mut h);
        match t.coeff.as_i64() {
            Some(v) => v.hash(&mut h),
            None => t.coeff.big().hash(&mut h),
        }
    }
    match l.constant.as_i64() {
        Some(v) => v.hash(&mut h),
        None => l.constant.big().hash(&mut h),
    }
    h.finish()
}

/// Whether an LC goes in the table (decided identically by the decoder).
fn tabled(l: &LinearCombination) -> bool {
    l.terms.len() >= 2
}

impl<'a> LcTable<'a> {
    fn new(items: &[GItem], flat: &'a [R1csConstraint]) -> Self {
        let mut t = LcTable {
            lcs: Vec::new(),
            prev_same: Vec::new(),
            last: HashMap::new(),
        };
        for it in items {
            if let GItem::Row(i) = it {
                let r = &flat[*i];
                for l in [&r.a, &r.b, &r.c] {
                    if tabled(l) {
                        let i = t.lcs.len() as u32;
                        let e = t.last.entry(lc_hash(l)).or_default();
                        let prev = e.iter().rev().copied().find(|&j| t.lcs[j as usize] == l);
                        e.push(i);
                        t.prev_same.push(prev);
                        t.lcs.push(l);
                    }
                }
            }
        }
        t
    }
    /// The most recent entry equal to `l` (any position).
    fn find(&self, l: &LinearCombination) -> Option<u32> {
        if !tabled(l) {
            return None;
        }
        self.last
            .get(&lc_hash(l))?
            .iter()
            .rev()
            .copied()
            .find(|&j| self.lcs[j as usize] == l)
    }
}

/// Worth a back-reference (tag `6` + index) instead of the LC itself.
fn worth_ref(l: &LinearCombination) -> bool {
    let mut b = Vec::new();
    put_lc_g(&mut b, l);
    b.len() >= 10
}
fn put_lc_ref(buf: &mut Vec<u8>, l: &LinearCombination, r: Option<u32>) {
    match r {
        Some(i) => {
            buf.push(6);
            put_uv(buf, u64::from(i));
        }
        None => put_lc_g(buf, l),
    }
}

/// Rows as one token without back-references: tag `0` (one row) or `7` (a rolled
/// run).
fn put_rows_plain(buf: &mut Vec<u8>, rows: &[usize], flat: &[R1csConstraint]) {
    if rows.len() == 1 {
        buf.push(0);
        put_row_g(buf, &flat[rows[0]]);
        return;
    }
    let ops: Vec<xark_ir::bytecode::Opcode> = rows
        .iter()
        .map(|&i| {
            // Rows drop debug notes (the decoder sets `note: None`), so the rolled
            // form matches the inline form exactly.
            let r = &flat[i];
            xark_ir::bytecode::Opcode::Constraint(xark_ir::R1csRow {
                a: r.a.clone(),
                b: r.b.clone(),
                c: r.c.clone(),
                note: None,
            })
        })
        .collect();
    let blob = xark_ir::bytecode::roll_and_encode_ops_compact(ops, &pool());
    buf.push(7);
    put_uv(buf, blob.len() as u64);
    buf.extend_from_slice(&blob);
}

/// A run of consecutive rows: plain (rolled), or — when that is smaller — with
/// every row that repeats an earlier big LC as a tag-`8` row of back-references
/// (and the rest rolled in between). `pos` is the run's first table entry.
/// Returns the number of tokens written.
fn put_row_run(
    buf: &mut Vec<u8>,
    rows: &[usize],
    flat: &[R1csConstraint],
    table: &LcTable,
    pos: &mut usize,
) -> usize {
    let mut refs: Vec<[Option<u32>; 3]> = Vec::with_capacity(rows.len());
    let mut any = false;
    for &i in rows {
        let r = &flat[i];
        let mut rr = [None; 3];
        for (k, l) in [&r.a, &r.b, &r.c].into_iter().enumerate() {
            if tabled(l) {
                rr[k] = table.prev_same[*pos].filter(|_| worth_ref(l));
                *pos += 1;
            }
        }
        any |= rr.iter().any(Option::is_some);
        refs.push(rr);
    }
    let mut plain = Vec::new();
    put_rows_plain(&mut plain, rows, flat);
    if !any {
        buf.extend_from_slice(&plain);
        return 1;
    }
    let mut alt = Vec::new();
    let mut ntok = 0;
    let mut seg: Vec<usize> = Vec::new();
    for (&i, rr) in rows.iter().zip(&refs) {
        if rr.iter().all(Option::is_none) {
            seg.push(i);
            continue;
        }
        if !seg.is_empty() {
            put_rows_plain(&mut alt, &seg, flat);
            ntok += 1;
            seg.clear();
        }
        let r = &flat[i];
        alt.push(8);
        put_lc_ref(&mut alt, &r.a, rr[0]);
        put_lc_ref(&mut alt, &r.b, rr[1]);
        put_lc_ref(&mut alt, &r.c, rr[2]);
        ntok += 1;
    }
    if !seg.is_empty() {
        put_rows_plain(&mut alt, &seg, flat);
        ntok += 1;
    }
    if alt.len() < plain.len() {
        buf.extend_from_slice(&alt);
        ntok
    } else {
        buf.extend_from_slice(&plain);
        1
    }
}

/// Serialize a constraint item stream. Item tags: `0` = a single inline row,
/// `5` = a function call (plugs delta-coded), `6` = a rolled block of calls, `7` =
/// a rolled run of ≥2 consecutive rows (periodic loops of primitives compress
/// here; varint-coded), `8` = a row whose LCs may refer back to earlier ones.
/// Returns the stream's calls in order and its LC table, which the same scope's
/// witness stream refers back to.
fn ser_c_items<'a>(
    buf: &mut Vec<u8>,
    items: &'a [GItem],
    flat: &'a [R1csConstraint],
) -> (Vec<&'a GItem>, LcTable<'a>) {
    let table = LcTable::new(items, flat);
    let mut pos = 0usize;
    let mut out: Vec<u8> = Vec::new();
    let mut ntok = 0usize;
    let mut i = 0;
    while i < items.len() {
        match &items[i] {
            GItem::Row(_) => {
                let start = i;
                while matches!(items.get(i), Some(GItem::Row(_))) {
                    i += 1;
                }
                let rows: Vec<usize> = items[start..i]
                    .iter()
                    .map(|it| match it {
                        GItem::Row(r) => *r,
                        GItem::Call(..) => unreachable!(),
                    })
                    .collect();
                ntok += put_row_run(&mut out, &rows, flat, &table, &mut pos);
            }
            GItem::Call(..) => {
                // A maximal run of calls, rolled into `CallTok`s.
                let start = i;
                while matches!(items.get(i), Some(GItem::Call(..))) {
                    i += 1;
                }
                let calls: Vec<&GItem> = items[start..i].iter().collect();
                for tok in roll_call_run(&calls) {
                    ntok += 1;
                    match tok {
                        CallTok::Single(k) => {
                            let GItem::Call(d, base, plugs) = calls[k] else {
                                unreachable!()
                            };
                            out.push(5);
                            put_uv(&mut out, u64::from(*d));
                            put_uv(&mut out, u64::from(*base));
                            put_plugs_compact(&mut out, plugs, *base);
                        }
                        CallTok::Rolled(r) => {
                            out.push(6);
                            put_rolled_call_compact(&mut out, &r);
                        }
                    }
                }
            }
        }
    }
    put_uv(buf, ntok as u64);
    buf.extend_from_slice(&out);
    (
        items
            .iter()
            .filter(|it| matches!(it, GItem::Call(..)))
            .collect(),
        table,
    )
}

/// Witness ops as one token without back-references: tag `0` (one op) or `7` (a
/// rolled run).
fn put_wits_plain(buf: &mut Vec<u8>, ops: &[&WitnessGen]) {
    if ops.len() == 1 {
        buf.push(0);
        put_witness_g(buf, ops[0]);
        return;
    }
    let ops: Vec<xark_ir::bytecode::Opcode> = ops
        .iter()
        .map(|w| xark_ir::bytecode::Opcode::Witness((*w).clone()))
        .collect();
    let blob = xark_ir::bytecode::roll_and_encode_ops_compact(ops, &pool());
    buf.push(7);
    put_uv(buf, blob.len() as u64);
    buf.extend_from_slice(&blob);
}

/// A run of consecutive witness ops: plain (rolled), or — when smaller — with every
/// op that reads a big LC of the scope's rows as a tag-`8` op referring to it.
/// Returns the number of tokens written.
fn put_wit_run(buf: &mut Vec<u8>, ops: &[&WitnessGen], table: &LcTable) -> usize {
    let hit = |w: &WitnessGen| {
        let mut h = false;
        for_each_lc(w, &mut |l| h |= table.find(l).is_some() && worth_ref(l));
        h
    };
    let hits: Vec<bool> = ops.iter().map(|w| hit(w)).collect();
    let mut plain = Vec::new();
    put_wits_plain(&mut plain, ops);
    if !hits.iter().any(|&h| h) {
        buf.extend_from_slice(&plain);
        return 1;
    }
    let mut alt = Vec::new();
    let mut ntok = 0;
    let mut seg: Vec<&WitnessGen> = Vec::new();
    for (&w, &h) in ops.iter().zip(&hits) {
        if !h {
            seg.push(w);
            continue;
        }
        if !seg.is_empty() {
            put_wits_plain(&mut alt, &seg);
            ntok += 1;
            seg.clear();
        }
        alt.push(8);
        put_witness_with(&mut alt, w, &mut |buf, l| {
            put_lc_ref(buf, l, table.find(l).filter(|_| worth_ref(l)))
        });
        ntok += 1;
    }
    if !seg.is_empty() {
        put_wits_plain(&mut alt, &seg);
        ntok += 1;
    }
    if alt.len() < plain.len() {
        buf.extend_from_slice(&alt);
        ntok
    } else {
        buf.extend_from_slice(&plain);
        1
    }
}

fn same_call(a: &GItem, b: &GItem) -> bool {
    matches!((a, b), (GItem::Call(d1, b1, p1), GItem::Call(d2, b2, p2)) if d1 == d2 && b1 == b2 && p1 == p2)
}

/// Serialize a witness item stream. Item tags: `0` = one witness op, `7` = a
/// rolled run of ≥2 witness ops, `8` = one op whose LCs may refer to the scope's
/// row LCs (`table`), `4` = `(skip, n)`: the next `n` calls of the scope's
/// constraint stream (`c_calls`) after skipping `skip` of them — every call
/// normally, since both streams make the same calls in the same order — and `5` =
/// a call spelled out (one the constraint stream doesn't make in order). `Row`s
/// with no witness-gen are holes (skipped, transparent to a run).
fn ser_w_items_std(
    buf: &mut Vec<u8>,
    items: &[GItem],
    flat_w: &[Option<WitnessGen>],
    c_calls: &[&GItem],
    table: &LcTable,
) {
    let mut out: Vec<u8> = Vec::new();
    let mut ntok = 0usize;
    let mut run: Vec<&WitnessGen> = Vec::new();
    let mut refs: Option<(usize, usize)> = None; // pending (skip, n)
    let flush_refs = |out: &mut Vec<u8>, ntok: &mut usize, refs: &mut Option<(usize, usize)>| {
        if let Some((skip, n)) = refs.take() {
            out.push(4);
            put_uv(out, skip as u64);
            put_uv(out, n as u64);
            *ntok += 1;
        }
    };
    let mut cur = 0usize; // next unreferenced constraint-stream call
    for it in items {
        match it {
            GItem::Row(idx) => {
                if let Some(w) = &flat_w[*idx] {
                    flush_refs(&mut out, &mut ntok, &mut refs);
                    run.push(w);
                }
            }
            GItem::Call(d, base, plugs) => {
                if !run.is_empty() {
                    ntok += put_wit_run(&mut out, &run, table);
                    run.clear();
                }
                let skip = (0..8)
                    .take_while(|s| cur + s < c_calls.len())
                    .find(|&s| same_call(c_calls[cur + s], it));
                match (skip, refs.as_mut()) {
                    (Some(0), Some((_, n))) => *n += 1,
                    (Some(s), _) => {
                        flush_refs(&mut out, &mut ntok, &mut refs);
                        refs = Some((s, 1));
                    }
                    (None, _) => {
                        flush_refs(&mut out, &mut ntok, &mut refs);
                        out.push(5);
                        put_uv(&mut out, u64::from(*d));
                        put_uv(&mut out, u64::from(*base));
                        put_plugs_compact(&mut out, plugs, *base);
                        ntok += 1;
                        continue;
                    }
                }
                cur += skip.unwrap_or(0) + 1;
            }
        }
    }
    flush_refs(&mut out, &mut ntok, &mut refs);
    if !run.is_empty() {
        ntok += put_wit_run(&mut out, &run, table);
    }
    put_uv(buf, ntok as u64);
    buf.extend_from_slice(&out);
}

/// Build the complete VERSION_FUNCTION artifact from a finished lowering: header +
/// field + signature inputs + constant pool + function defs (each its first call's
/// rows and witness ops, with nested calls) + top-level streams. Expands via
/// `expand_function_blob` to a byte-identical `CircuitProgram`.
// `FieldConst` keys: its only interior mutability is a lazily filled cache that
// doesn't take part in ordering.
#[allow(clippy::mutable_key_type)]
fn build_function_blob(env: &Builder, field: &FieldSpec, num_inputs: usize) -> Vec<u8> {
    let flat = &env.constraints;
    let flat_w = &env.witness_gen;
    // Calls per scope (top level = `None`, else the enclosing def), in row order.
    // Calls within one scope are disjoint.
    let n_defs = env.function_templates.len();
    let mut scoped: Vec<Vec<&FunctionCall>> = vec![Vec::new(); n_defs + 1];
    for c in &env.function_calls {
        scoped[c.parent.map_or(n_defs, |d| d as usize)].push(c);
    }
    for s in &mut scoped {
        s.sort_by(|a, b| a.c0.cmp(&b.c0).then(a.c1.cmp(&b.c1)));
    }
    // A scope's item streams: its rows / witness ops in `c0..c1` / `w0..w1`, with
    // each call's range replaced by one CALL item.
    let scope_items = |calls: &[&FunctionCall], c0: usize, c1: usize, w0: usize, w1: usize| {
        let mut c_items: Vec<GItem> = Vec::new();
        let (mut i, mut k) = (c0, 0usize);
        while i < c1 {
            if k < calls.len() && calls[k].c0 == i {
                let r = calls[k];
                c_items.push(GItem::Call(r.def, r.base, r.plugs.clone()));
                i = r.c1;
                k += 1;
            } else {
                c_items.push(GItem::Row(i));
                i += 1;
            }
        }
        let mut w_items: Vec<GItem> = Vec::new();
        let (mut i, mut k) = (w0, 0usize);
        while i < w1 {
            if k < calls.len() && calls[k].w0 == i {
                let r = calls[k];
                w_items.push(GItem::Call(r.def, r.base, r.plugs.clone()));
                i = r.w1;
                k += 1;
            } else {
                w_items.push(GItem::Row(i));
                i += 1;
            }
        }
        (c_items, w_items)
    };

    let mut b = Vec::new();
    b.extend_from_slice(&xark_ir::bytecode::MAGIC);
    b.extend_from_slice(&VERSION_FUNCTION.to_le_bytes());
    put_str(&mut b, &field.name);
    put_str(&mut b, field.modulus_decimal.as_deref().unwrap_or(""));
    put_uv(&mut b, env.variables.len() as u64);
    // The var *table* is trivial to reconstruct: the first `num_inputs` vars are
    // the signature inputs (Public/Private, matched by name at prove time), and
    // EVERY other var is `Derived` — including hint/advice vars, which carry
    // `Visibility::Private` but are computed by the witness program, not supplied.
    // So we store only the inputs (role + name); the rest are `v{id}` / Derived.
    put_uv(&mut b, num_inputs as u64);
    for id in 0..num_inputs {
        b.push(vis_byte(&env.variables[id].visibility));
        put_str(&mut b, &env.variables[id].name);
    }
    // Every scope's item streams: each def's body, then the top level.
    let mut scopes: Vec<(Vec<GItem>, Vec<GItem>)> = env
        .function_templates
        .iter()
        .enumerate()
        .map(|(d, t)| scope_items(&scoped[d], t.c0, t.c1, t.w0, t.w1))
        .collect();
    scopes.push(scope_items(&scoped[n_defs], 0, flat.len(), 0, flat_w.len()));

    // --- constant pool: every big constant written more than once, most used
    // first (so the common ones get one-byte indices); referenced by index.
    let mut uses: BTreeMap<xark_ir::FieldConst, u32> = BTreeMap::new();
    {
        let mut count = |l: &LinearCombination| {
            for c in std::iter::once(&l.constant).chain(l.terms.iter().map(|t| &t.coeff)) {
                if c.as_i64().is_none() {
                    match uses.get_mut(c) {
                        Some(n) => *n += 1,
                        None => {
                            uses.insert(c.clone(), 1);
                        }
                    }
                }
            }
        };
        for (c_items, w_items) in &scopes {
            for it in c_items {
                match it {
                    GItem::Row(i) => {
                        let r = &flat[*i];
                        count(&r.a);
                        count(&r.b);
                        count(&r.c);
                    }
                    GItem::Call(_, _, plugs) => plugs.iter().for_each(&mut count),
                }
            }
            for it in w_items {
                if let GItem::Row(i) = it
                    && let Some(w) = &flat_w[*i]
                {
                    for_each_lc(w, &mut count);
                }
            }
        }
    }
    let mut pooled: Vec<(xark_ir::FieldConst, u32)> =
        uses.into_iter().filter(|(_, n)| *n >= 2).collect();
    pooled.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    put_uv(&mut b, pooled.len() as u64);
    for (c, _) in &pooled {
        put_fc(&mut b, c);
    }
    let index: BTreeMap<xark_ir::FieldConst, u32> = pooled
        .into_iter()
        .zip(0..)
        .map(|((c, _), i)| (c, i))
        .collect();
    POOL.with(|p| *p.borrow_mut() = std::sync::Arc::new(index));
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            POOL.with(|p| *p.borrow_mut() = Default::default());
        }
    }
    let _reset = Reset;

    // --- function defs: one canonical template body each ------------------------
    put_uv(&mut b, n_defs as u64);
    let top = scopes.pop().expect("top scope");
    for (t, (c_items, w_items)) in env.function_templates.iter().zip(&scopes) {
        put_uv(&mut b, u64::from(t.base_var));
        put_ids_g(&mut b, &t.plug_vars);
        // Output vars — the internal vars a caller reads after the call. Recorded
        // so a per-template R1CS minimizer can PIN them (like plugs) as the def's
        // interface while eliminating the rest; the expansion itself does not
        // consume this field.
        put_ids_g(&mut b, &t.outputs);
        // Body = the first call's rows / witness ops (they roll if periodic), with
        // its repeated sub-calls as nested CALLs.
        let (c_calls, table) = ser_c_items(&mut b, c_items, flat);
        ser_w_items_std(&mut b, w_items, flat_w, &c_calls, &table);
    }

    // --- top-level streams: rows interspersed with the disjoint CALLs ----------
    let (c_calls, table) = ser_c_items(&mut b, &top.0, flat);
    ser_w_items_std(&mut b, &top.1, flat_w, &c_calls, &table);
    // Keep-set exception for the decoder's prune. `finish` drops every UNREFERENCED
    // `Internal` var but retains `Private` (advice/hint outputs) even unreferenced.
    // The decoder drops all unreferenced non-input vars, so we hand it the only
    // exceptions — unreferenced advice — to keep. Almost always empty (a live hint
    // is pinned by a constraint, hence referenced), so this costs ~1 byte.
    let mut referenced = VarSet::default();
    for c in flat {
        for lc in [&c.a, &c.b, &c.c] {
            for t in &lc.terms {
                referenced.insert(t.var);
            }
        }
    }
    let keep_extra: Vec<VarId> = (num_inputs..env.variables.len())
        .filter(|&id| {
            !referenced.contains(&(id as u32))
                // unreferenced advice, or witness-only scratch (Internal but live
                // via the witness-gen program) — both retained by `finish`.
                && (env.variables[id].visibility == Visibility::Private
                    || env.witness_only_vars.contains(&(id as u32)))
        })
        .map(|id| id as u32)
        .collect();
    put_ids_g(&mut b, &keep_extra);
    b
}

/// Visit every linear combination a witness op reads.
fn for_each_lc(w: &WitnessGen, f: &mut dyn FnMut(&LinearCombination)) {
    match w {
        WitnessGen::Product { left, right, .. } => {
            f(left);
            f(right);
        }
        WitnessGen::Linear { lc, .. } => f(lc),
        WitnessGen::Xor { a, b, .. } | WitnessGen::Or { a, b, .. } => {
            f(a);
            f(b);
        }
        WitnessGen::Inverse { input, .. }
        | WitnessGen::InverseOrZero { input, .. }
        | WitnessGen::Bit { input, .. }
        | WitnessGen::Bits { input, .. } => f(input),
        WitnessGen::DivRem { num, den, .. } => {
            f(num);
            f(den);
        }
        WitnessGen::MulModDivMod { a, b, modulus, .. } => {
            a.iter().chain(b).chain(modulus).for_each(f);
        }
        WitnessGen::ModInverse { a, modulus, .. } => a.iter().chain(modulus).for_each(f),
        WitnessGen::Sub2 {
            a, b, c, modulus, ..
        } => {
            a.iter().chain(b).chain(c).chain(modulus).for_each(f);
        }
    }
}

/// Finalize: drop unreferenced internal variables and assemble both programs.
/// Make the inputs variables `0..n` (in binding order), keeping every other
/// variable's relative order. The compiler may schedule pure arithmetic on earlier
/// inputs before a later input is bound (only the intrinsic calls keep their
/// order), which interleaves variables; the prover requires inputs first.
fn renumber_inputs(env: &mut Builder) {
    let n_vars = env.variables.len();
    if env
        .input_ids
        .iter()
        .enumerate()
        .all(|(i, &v)| v as usize == i)
    {
        return;
    }
    let mut is_input = vec![false; n_vars];
    for &v in &env.input_ids {
        is_input[v as usize] = true;
    }
    let mut map = vec![0 as VarId; n_vars];
    for (i, &v) in env.input_ids.iter().enumerate() {
        map[v as usize] = i as VarId;
    }
    let mut next = env.input_ids.len() as VarId;
    for v in 0..n_vars {
        if !is_input[v] {
            map[v] = next;
            next += 1;
        }
    }
    let m = |v: VarId| map[v as usize];
    let map_lc = |l: &mut LinearCombination| {
        for t in &mut l.terms {
            t.var = m(t.var);
        }
        *l = std::mem::replace(l, LinearCombination::zero()).simplified();
    };
    for c in &mut env.constraints {
        map_lc(&mut c.a);
        map_lc(&mut c.b);
        map_lc(&mut c.c);
    }
    for w in env.witness_gen.iter_mut().flatten() {
        subst_witness_vars(w, &m, &|l| {
            let mut l = l.clone();
            for t in &mut l.terms {
                t.var = m(t.var);
            }
            l.simplified()
        });
    }
    let mut vars: Vec<Option<Variable>> = vec![None; n_vars];
    let mut names = vec![String::new(); n_vars];
    for (v, var) in std::mem::take(&mut env.variables).into_iter().enumerate() {
        let id = m(v as VarId);
        names[id as usize] = env.var_names.get(v).cloned().unwrap_or_default();
        vars[id as usize] = Some(Variable { id, ..var });
    }
    env.variables = vars.into_iter().map(|v| v.expect("permutation")).collect();
    env.var_names = names;
    env.merged = std::mem::take(&mut env.merged)
        .into_iter()
        .map(|(k, v)| (m(k), v))
        .collect();
    env.witness_only_vars = env.witness_only_vars.iter().map(|&v| m(v)).collect();
    // Call regions: shift; a region that binds an input is no template candidate.
    env.regions
        .retain(|r| (r.v0..r.v1).all(|v| !is_input[v as usize]));
    for r in &mut env.regions {
        if r.v1 > r.v0 {
            r.v0 = m(r.v0);
            r.v1 = m(r.v1 - 1) + 1;
        } else {
            let v = m(r.v0.min(n_vars as VarId - 1));
            r.v0 = v;
            r.v1 = v;
        }
    }
    env.input_ids = (0..env.input_ids.len() as VarId).collect();
}

pub(crate) fn finish(mut env: Builder, field: FieldSpec, n_inputs: usize) -> LowerOutput {
    env.fill_products();
    renumber_inputs(&mut env);
    // Developer diagnostic only (behind `XARK_BUILD_TIME`); a normal build stays
    // quiet on stderr rather than printing this on every compile.
    // Revive a merged mul output (its `a·b = out` folded into `require_eq`) if a
    // later constraint still references it, so the reuse stays bound to `a·b`.
    // Not-reused outputs are pruned below (fast path unchanged). This MUST run
    // before `build_function_blob` below — else the revived rows land in the flat
    // R1CS but not the artifact, leaving the artifact (what the prover proves)
    // under-constrained for a reused product (XARK_VERIFY caught exactly this).
    // Every variable a constraint references (kept up to date through the revival,
    // so it is also the final reference set below).
    let mut referenced = VarSet::default();
    for c in &env.constraints {
        for lc in [&c.a, &c.b, &c.c] {
            for term in &lc.terms {
                referenced.insert(term.var);
            }
        }
    }
    {
        let ref_now = &referenced;
        // The merged outputs to revive (referenced before any revival), by var.
        let mut merged: Vec<(VarId, (usize, usize))> = std::mem::take(&mut env.merged)
            .into_iter()
            .filter(|(out, _)| ref_now.contains(out))
            .collect();
        merged.sort_unstable_by_key(|e| e.0);
        for (out, (wg_idx, orig_idx)) in merged {
            {
                let a = env.constraints[orig_idx].a.clone();
                let b = env.constraints[orig_idx].b.clone();
                let id = env.fresh_constraint_id();
                // Inherit the original mul's attribution (source line + chain);
                // it is genuinely a `Mul`. Keeps `profile` index-aligned with
                // `constraints` for the appended revival.
                if env.profile_enabled {
                    let mut prof = env.profile[orig_idx].clone();
                    prof.id = id;
                    prof.kind = ConstraintKind::Mul;
                    env.profile.push(prof);
                }
                for t in a.terms.iter().chain(&b.terms) {
                    referenced.insert(t.var);
                }
                referenced.insert(out);
                env.constraints.push(R1csConstraint::mul(
                    id,
                    a.clone(),
                    b.clone(),
                    out,
                    "revived a*b = out (product reused after require_eq merge)",
                ));
                env.witness_gen[wg_idx] = Some(WitnessGen::Product {
                    out,
                    left: a,
                    right: b,
                });
            }
        }
    }
    // Witness-only dead-code elimination. A `witness_only` region emits value ops
    // (kept) alongside pin-only ops — range-check bit decompositions, carry hints —
    // whose only consumer, a constraint, was suppressed. Those are dead weight in
    // the witness program. Prune them by transitive liveness: a var is live if a
    // constraint references it, or a live op reads it; keep only live witness-only
    // ops/vars. (No-op for ordinary circuits — `check_pinning` guarantees every
    // non-witness-only hint output is constraint-referenced, hence already live.)
    // Runs BEFORE `build_function_blob` so the flat R1CS and the artifact prune
    // identically (XARK_VERIFY). Merged ops (`None`) are left untouched.
    if !env.witness_only_vars.is_empty() {
        let mut live = VarSet::default();
        for c in &env.constraints {
            for lc in [&c.a, &c.b, &c.c] {
                for t in &lc.terms {
                    live.insert(t.var);
                }
            }
        }
        // Witness-gen is in dependency order, so one reverse pass reaches fixpoint:
        // a live output pulls in the op's sibling outputs and its inputs.
        for op in env.witness_gen.iter().flatten().rev() {
            let outs = witness_gen_outs(op);
            if outs.iter().any(|o| live.contains(o)) {
                for o in outs {
                    live.insert(o);
                }
                for v in witness_gen_input_vars(op) {
                    live.insert(v);
                }
            }
        }
        let dead: Vec<usize> = (0..env.witness_gen.len())
            .filter(|&i| {
                env.witness_gen[i].as_ref().is_some_and(|op| {
                    let outs = witness_gen_outs(op);
                    outs.iter().any(|o| env.witness_only_vars.contains(o))
                        && outs.iter().all(|o| !live.contains(o))
                })
            })
            .collect();
        // Drop the dead ops (the witness-gen saving). The dead output vars stay
        // declared + pinning-exempt (in `witness_only_vars`) — harmless, unreferenced
        // scratch — so `finish` and `build_function_blob` keep the same var/exempt
        // sets and only the (now-`None`) ops differ, which both already skip.
        for i in dead {
            env.witness_gen[i] = None;
        }
    }
    // Complete DAG-compact artifact — built AFTER the revival above (so the
    // artifact == the flat R1CS: the reused-product binding is in both) and while
    // `env`/`field` are still intact. The single container rolls periodic runs of
    // inline rows (see `ser_c_items`), so it also compresses loops of primitives —
    // no functions required. Built for EVERY circuit (the sole on-disk format).
    let t = std::time::Instant::now();
    crate::templates::detect(&mut env);
    if std::env::var_os("XARK_FRONTEND_TIME").is_some() {
        eprintln!(
            "FRONTEND_TIME: templates = {:?} ({} defs, {} calls)",
            t.elapsed(),
            env.function_templates.len(),
            env.function_calls.len()
        );
    }
    let t = std::time::Instant::now();
    let xbc = build_function_blob(&env, &field, n_inputs);
    if std::env::var_os("XARK_FRONTEND_TIME").is_some() {
        eprintln!("FRONTEND_TIME: encode xbc = {:?}", t.elapsed());
    }

    // Witness-only vars carry no constraint but ARE live: they feed the witness-gen
    // of a downstream, pinned result (e.g. `x²` feeding `d = x²·x²`). Keeping them —
    // and their witness-gen — is required, or the derived value computes from an
    // uncomputed (zero) input.
    let wo = core::mem::take(&mut env.witness_only_vars);

    let variables: Vec<Variable> = env
        .variables
        .into_iter()
        .filter(|v| {
            v.visibility != Visibility::Internal || referenced.contains(&v.id) || wo.contains(&v.id)
        })
        .collect();
    let mut kept = VarSet::default();
    for v in &variables {
        kept.insert(v.id);
    }

    // --- primitive IR view -------------------------------------------------
    let pvars: Vec<primitive::Var> = variables
        .iter()
        .map(|v| primitive::Var {
            id: v.id,
            name: v.name.clone(),
            role: if (v.id as usize) < n_inputs {
                match v.visibility {
                    Visibility::Public => primitive::VarRole::PublicInput,
                    _ => primitive::VarRole::PrivateInput,
                }
            } else {
                primitive::VarRole::Derived
            },
        })
        .collect();

    // The expression view (each `a·b − c` expanded) is only for `circuit.json`; it
    // costs |a|·|b| per row, which dominates on circuits with large sums.
    let expressions: Vec<primitive::Expression> = env
        .constraints
        .iter()
        .filter(|_| env.notes)
        .map(|c| {
            xark_ir::expr_from_r1cs(
                &c.a,
                &c.b,
                &c.c,
                c.debug.as_ref().and_then(|d| d.note.clone()),
            )
        })
        .collect();

    let witness_gen: Vec<WitnessGen> = env
        .witness_gen
        .into_iter()
        .flatten()
        .filter(|op| kept.contains(&witness_gen_out(op)))
        .collect();

    let primitive = PrimitiveProgram {
        field: primitive_field(&field),
        vars: pvars,
        constraints: expressions,
        witness_gen,
    };

    let profile = env.profile;

    let r1cs = R1csProgram {
        field,
        variables,
        constraints: env.constraints,
    };

    LowerOutput {
        r1cs,
        primitive,
        profile,
        xbc,
        witness_only_vars: wo,
    }
}

/// All output variables of a witness-gen op (multi-output ops list every limb/bit).
fn witness_gen_outs(op: &WitnessGen) -> Vec<VarId> {
    match op {
        WitnessGen::Product { out, .. }
        | WitnessGen::Linear { out, .. }
        | WitnessGen::Xor { out, .. }
        | WitnessGen::Or { out, .. }
        | WitnessGen::Inverse { out, .. }
        | WitnessGen::InverseOrZero { out, .. }
        | WitnessGen::Bit { out, .. } => vec![*out],
        WitnessGen::Bits { outs, .. } => outs.clone(),
        WitnessGen::DivRem { q, r, .. } => vec![*q, *r],
        WitnessGen::MulModDivMod { q, r, .. } => q.iter().chain(r).copied().collect(),
        WitnessGen::ModInverse { out, .. } => out.clone(),
        WitnessGen::Sub2 { qabs, r, .. } => {
            let mut v = vec![*qabs];
            v.extend(r);
            v
        }
    }
}

/// All input variables a witness-gen op reads (from its input linear combinations).
fn witness_gen_input_vars(op: &WitnessGen) -> Vec<VarId> {
    fn add(lc: &LinearCombination, v: &mut Vec<VarId>) {
        v.extend(lc.terms.iter().map(|t| t.var));
    }
    let mut v = Vec::new();
    match op {
        WitnessGen::Product { left, right, .. } => {
            add(left, &mut v);
            add(right, &mut v);
        }
        WitnessGen::Linear { lc, .. } => add(lc, &mut v),
        WitnessGen::Xor { a, b, .. } | WitnessGen::Or { a, b, .. } => {
            add(a, &mut v);
            add(b, &mut v);
        }
        WitnessGen::Inverse { input, .. }
        | WitnessGen::InverseOrZero { input, .. }
        | WitnessGen::Bit { input, .. }
        | WitnessGen::Bits { input, .. } => add(input, &mut v),
        WitnessGen::DivRem { num, den, .. } => {
            add(num, &mut v);
            add(den, &mut v);
        }
        WitnessGen::MulModDivMod { a, b, modulus, .. } => {
            for l in a.iter().chain(b).chain(modulus) {
                add(l, &mut v);
            }
        }
        WitnessGen::ModInverse { a, modulus, .. } => {
            for l in a.iter().chain(modulus) {
                add(l, &mut v);
            }
        }
        WitnessGen::Sub2 {
            a, b, c, modulus, ..
        } => {
            for l in a.iter().chain(b).chain(c).chain(modulus) {
                add(l, &mut v);
            }
        }
    }
    v
}

/// The primary output variable of a witness-gen op.
fn witness_gen_out(op: &WitnessGen) -> VarId {
    match op {
        WitnessGen::Product { out, .. }
        | WitnessGen::Linear { out, .. }
        | WitnessGen::Xor { out, .. }
        | WitnessGen::Or { out, .. }
        | WitnessGen::Inverse { out, .. }
        | WitnessGen::InverseOrZero { out, .. }
        | WitnessGen::Bit { out, .. } => *out,
        // Multi-output; represented by its first bit for the "is any output still
        // referenced" filter (all bits of a decomposition are used together).
        WitnessGen::Bits { outs, .. } => *outs.first().unwrap_or(&0),
        WitnessGen::DivRem { q, .. } => *q,
        // Multi-output; represented by its first output for the "is any output
        // still referenced" filter (all limbs are used together in practice).
        WitnessGen::MulModDivMod { q, r, .. } => *q.first().or_else(|| r.first()).unwrap_or(&0),
        WitnessGen::ModInverse { out, .. } => *out.first().unwrap_or(&0),
        WitnessGen::Sub2 { qabs, .. } => *qabs,
    }
}

/// Convert the R1CS field spec to the primitive one (which needs a concrete
/// modulus; default to BN254 when unspecified, since that is the target field).
fn primitive_field(field: &FieldSpec) -> primitive::FieldSpec {
    match &field.modulus_decimal {
        Some(m) => primitive::FieldSpec {
            name: field.name.clone(),
            modulus_decimal: m.clone(),
        },
        None => primitive::FieldSpec::bn254(),
    }
}

pub(crate) fn check_pinning(out: &LowerOutput, n_inputs: usize) -> CompileResult<()> {
    let mut referenced = VarSet::default();
    for c in &out.r1cs.constraints {
        for lc in [&c.a, &c.b, &c.c] {
            for term in &lc.terms {
                referenced.insert(term.var);
            }
        }
    }
    for v in &out.r1cs.variables {
        if referenced.contains(&v.id) {
            continue;
        }
        // Witness-only scratch: intentionally unpinned. Safe to exempt — a var in
        // zero constraints cannot affect proof validity (its only use is in the
        // witness-gen program that computes a downstream, pinned result).
        if out.witness_only_vars.contains(&v.id) {
            continue;
        }
        let is_input = (v.id as usize) < n_inputs;
        match v.visibility {
            Visibility::Public => {
                return Err(CompileError::new(format!(
                    "public input `{}` is declared but no constraint references it — \
                     the verifier's value for it would be unconstrained",
                    v.name
                ))
                .with_note(
                    "bind every public input/output with an `require_eq` (or remove it \
                     from the signature)",
                ));
            }
            // A `Private` var allocated after the inputs is a hint/advice output.
            Visibility::Private if !is_input => {
                return Err(CompileError::new(format!(
                    "hint/advice output `{}` is not pinned by any constraint — \
                     a malicious prover could choose it freely",
                    v.name
                ))
                .with_note(
                    "constrain every hint output, e.g. `require_eq(x * hint_inverse(x), 1)`",
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

/// A set of variable ids (dense, so a bitmap — the circuit-wide scans in `finish`
/// insert every term of every row).
#[derive(Default)]
pub(crate) struct VarSet(Vec<bool>);

impl VarSet {
    #[inline]
    pub(crate) fn insert(&mut self, v: VarId) {
        let i = v as usize;
        if i >= self.0.len() {
            self.0.resize((i + 1).max(self.0.len() * 2), false);
        }
        self.0[i] = true;
    }
    #[inline]
    pub(crate) fn contains(&self, v: &VarId) -> bool {
        self.0.get(*v as usize).copied().unwrap_or(false)
    }
}
