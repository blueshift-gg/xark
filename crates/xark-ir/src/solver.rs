//! Reference witness solver + constraint checker for the [primitive IR].
//!
//! This is a *reference implementation* of what the backend's lowering must do:
//! given values for the input variables, run the witness-generation program to
//! fill every derived/hint variable, then check that all AssertZero constraints
//! evaluate to zero. It exists so functions can be validated end-to-end (e.g.
//! against a known SHA-256 test vector) purely from the emitted IR — no proving
//! system required.
//!
//! [primitive IR]: crate::primitive

use std::collections::BTreeMap;

use ark_bn254::Fr;
use ark_ff::{BigInteger, Field as ArkField, PrimeField};
use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::linear_combination::{LinearCombination, VarId};
use crate::primitive::{Expression, PrimitiveProgram, WitnessGen};

/// A field element — a fixed-width **BN254 scalar** (Montgomery `Fr`, no
/// allocation, no division) on the common path, or an arbitrary-modulus big
/// integer for programs over a different field. The reference solver runs
/// millions of field ops, so the BN254 fast path (native `Fr` arithmetic
/// instead of `num-bigint` modmul / `modpow` inversion) is the dominant
/// witness-gen and soundness-check speedup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fp {
    Bn254(Fr),
    Generic { value: BigUint, modulus: BigUint },
}

/// Is `modulus` the BN254 scalar-field prime (the field xark's `Field` is)?
fn is_bn254(modulus: &BigUint) -> bool {
    static M: std::sync::OnceLock<BigUint> = std::sync::OnceLock::new();
    modulus == M.get_or_init(|| BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le()))
}

impl Fp {
    fn new(value: BigUint, modulus: &BigUint) -> Self {
        if is_bn254(modulus) {
            Fp::Bn254(Fr::from_le_bytes_mod_order(&value.to_bytes_le()))
        } else {
            Fp::Generic {
                value: value % modulus,
                modulus: modulus.clone(),
            }
        }
    }

    fn zero(modulus: &BigUint) -> Self {
        if is_bn254(modulus) {
            Fp::Bn254(Fr::from(0u64))
        } else {
            Fp::Generic {
                value: BigUint::zero(),
                modulus: modulus.clone(),
            }
        }
    }

    /// Reduce a signed decimal string into the field.
    fn from_decimal(s: &str, modulus: &BigUint) -> Self {
        let trimmed = s.trim();
        // Fast path: the overwhelming majority of circuit coefficients are small
        // integers (`0`, `±1`, `±2`, small constants). Parsing as `i64` skips the
        // `BigUint` allocation + byte-reduction on the field's hottest inner loop
        // (`eval_lc` re-parses every coefficient on every evaluation).
        if let Ok(n) = trimmed.parse::<i64>() {
            return Fp::from_i64(n, modulus);
        }
        let (neg, mag) = match trimmed.strip_prefix('-') {
            Some(m) => (true, m),
            None => (false, trimmed),
        };
        let m = BigUint::parse_bytes(mag.as_bytes(), 10).unwrap_or_else(BigUint::zero);
        let v = Fp::new(m, modulus);
        if neg {
            v.neg()
        } else {
            v
        }
    }

    /// Allocation-free small-integer constructor (the `from_decimal` fast path).
    fn from_i64(n: i64, modulus: &BigUint) -> Self {
        if is_bn254(modulus) {
            let mag = Fr::from(n.unsigned_abs());
            Fp::Bn254(if n < 0 { -mag } else { mag })
        } else {
            let mag = Fp::new(BigUint::from(n.unsigned_abs()), modulus);
            if n < 0 {
                mag.neg()
            } else {
                mag
            }
        }
    }

    fn add(&self, other: &Fp) -> Fp {
        match (self, other) {
            (Fp::Bn254(a), Fp::Bn254(b)) => Fp::Bn254(*a + *b),
            (Fp::Generic { value: a, modulus }, Fp::Generic { value: b, .. }) => Fp::Generic {
                value: (a + b) % modulus,
                modulus: modulus.clone(),
            },
            _ => unreachable!("field element variants must match"),
        }
    }

    fn mul(&self, other: &Fp) -> Fp {
        match (self, other) {
            (Fp::Bn254(a), Fp::Bn254(b)) => Fp::Bn254(*a * *b),
            (Fp::Generic { value: a, modulus }, Fp::Generic { value: b, .. }) => Fp::Generic {
                value: (a * b) % modulus,
                modulus: modulus.clone(),
            },
            _ => unreachable!("field element variants must match"),
        }
    }

    fn sub(&self, other: &Fp) -> Fp {
        match (self, other) {
            (Fp::Bn254(a), Fp::Bn254(b)) => Fp::Bn254(*a - *b),
            _ => self.add(&other.neg()),
        }
    }

    fn neg(&self) -> Fp {
        match self {
            Fp::Bn254(a) => Fp::Bn254(-*a),
            Fp::Generic { value, modulus } => Fp::Generic {
                value: if value.is_zero() {
                    BigUint::zero()
                } else {
                    modulus - value
                },
                modulus: modulus.clone(),
            },
        }
    }

    /// Multiplicative inverse (`None` for zero). BN254 uses the field's own
    /// inversion; the generic path uses Fermat `a^(p-2)`.
    fn inverse(&self) -> Option<Fp> {
        match self {
            Fp::Bn254(a) => a.inverse().map(Fp::Bn254),
            Fp::Generic { value, modulus } => {
                if value.is_zero() {
                    None
                } else {
                    Some(Fp::Generic {
                        value: value.modpow(&(modulus - BigUint::from(2u32)), modulus),
                        modulus: modulus.clone(),
                    })
                }
            }
        }
    }

    fn is_zero(&self) -> bool {
        match self {
            Fp::Bn254(a) => *a == Fr::from(0u64),
            Fp::Generic { value, .. } => value.is_zero(),
        }
    }

    /// The `i`-th bit of the canonical representative, as a field `0`/`1`.
    fn bit(&self, i: usize) -> Fp {
        let set = match self {
            Fp::Bn254(a) => a.into_bigint().get_bit(i),
            Fp::Generic { value, .. } => (value >> i) & BigUint::one() == BigUint::one(),
        };
        match self {
            Fp::Bn254(_) => Fp::Bn254(Fr::from(u64::from(set))),
            Fp::Generic { modulus, .. } => Fp::Generic {
                value: if set { BigUint::one() } else { BigUint::zero() },
                modulus: modulus.clone(),
            },
        }
    }

    pub fn to_decimal(&self) -> String {
        self.to_biguint().to_str_radix(10)
    }

    /// The raw BN254 scalar, when this element lives in that field. Lets the
    /// Groth16 backend consume the solved witness directly — `Fp::Bn254` already
    /// holds the `Fr`, so this avoids a per-variable `Fr → decimal string → Fr`
    /// round-trip over the whole witness (millions of format+parse calls).
    pub fn as_bn254_fr(&self) -> Option<Fr> {
        match self {
            Fp::Bn254(a) => Some(*a),
            Fp::Generic { .. } => None,
        }
    }

    fn to_biguint(&self) -> BigUint {
        match self {
            Fp::Bn254(a) => BigUint::from_bytes_le(&a.into_bigint().to_bytes_le()),
            Fp::Generic { value, .. } => value.clone(),
        }
    }
}

/// Errors from solving or checking.
#[derive(Debug)]
pub enum SolveError {
    MissingInput(VarId),
    DivisionByZero,
    NonInvertible,
    /// Hint inputs out of range (would underflow) — rejected, not panicked.
    MalformedHint(&'static str),
    /// A constraint (by index) was not satisfied.
    ConstraintFailed(usize),
    /// Field modulus missing, unparseable, or `< 2`.
    MalformedModulus,
}

impl core::fmt::Display for SolveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SolveError::MissingInput(v) => write!(f, "missing input for variable {v}"),
            SolveError::DivisionByZero => write!(f, "division by zero"),
            SolveError::NonInvertible => write!(f, "value is not invertible"),
            SolveError::MalformedHint(m) => write!(f, "malformed hint: {m}"),
            SolveError::ConstraintFailed(i) => write!(f, "constraint {i} is not satisfied"),
            SolveError::MalformedModulus => {
                write!(f, "field modulus is missing, unparseable, or < 2")
            }
        }
    }
}

impl std::error::Error for SolveError {}

/// Cap on a hint's limb_bits (real limbs are 86-bit).
const MAX_LIMB_BITS: u32 = 128;

fn modulus_of(program: &PrimitiveProgram) -> Result<BigUint, SolveError> {
    modulus_of_field(&program.field)
}

fn modulus_of_field(field: &crate::primitive::FieldSpec) -> Result<BigUint, SolveError> {
    let m = BigUint::parse_bytes(field.modulus_decimal.as_bytes(), 10)
        .ok_or(SolveError::MalformedModulus)?;
    if m < BigUint::from(2u32) {
        return Err(SolveError::MalformedModulus);
    }
    Ok(m)
}

/// Read access to a variable assignment. The witness solve uses the dense
/// [`DenseAssign`] (O(1) indexed lookups for its millions of `eval_lc` term
/// reads); the constraint check/analysis keeps the sparse `BTreeMap` it is
/// handed. Both flow through the same generic `eval_*` code.
trait Assignment {
    fn get_fp(&self, var: VarId) -> Option<&Fp>;
}

impl Assignment for BTreeMap<VarId, Fp> {
    #[inline]
    fn get_fp(&self, var: VarId) -> Option<&Fp> {
        self.get(&var)
    }
}

/// A witness assignment stored densely by `VarId`. Var ids are allocated
/// contiguously during lowering, so this is a flat `Vec` — turning each of the
/// solve loop's per-term lookups from a `BTreeMap` tree descent (O(log n)) into
/// a single index.
struct DenseAssign {
    slots: Vec<Option<Fp>>,
}

impl DenseAssign {
    fn with_len(n: usize) -> Self {
        DenseAssign {
            slots: vec![None; n],
        }
    }

    #[inline]
    fn set(&mut self, var: VarId, val: Fp) {
        let i = var as usize;
        if i >= self.slots.len() {
            self.slots.resize(i + 1, None);
        }
        self.slots[i] = Some(val);
    }

    /// The public solve API hands back a `BTreeMap` (what check/analyze and the
    /// backend consume); convert once at the boundary.
    fn into_btreemap(self) -> BTreeMap<VarId, Fp> {
        self.slots
            .into_iter()
            .enumerate()
            .filter_map(|(i, o)| o.map(|v| (i as VarId, v)))
            .collect()
    }
}

impl Assignment for DenseAssign {
    #[inline]
    fn get_fp(&self, var: VarId) -> Option<&Fp> {
        self.slots.get(var as usize).and_then(|o| o.as_ref())
    }
}

fn eval_lc(lc: &LinearCombination, assign: &impl Assignment, modulus: &BigUint) -> Fp {
    let mut acc = Fp::from_decimal(&lc.constant.decimal(), modulus);
    for term in &lc.terms {
        let coeff = Fp::from_decimal(&term.coeff.decimal(), modulus);
        let var = assign
            .get_fp(term.var)
            .cloned()
            .unwrap_or_else(|| Fp::zero(modulus));
        acc = acc.add(&coeff.mul(&var));
    }
    acc
}

fn eval_expression(expr: &Expression, assign: &impl Assignment, modulus: &BigUint) -> Fp {
    let mut acc = Fp::from_decimal(&expr.constant.decimal(), modulus);
    for lt in &expr.linear_terms {
        let coeff = Fp::from_decimal(&lt.coeff.decimal(), modulus);
        let v = assign
            .get_fp(lt.var)
            .cloned()
            .unwrap_or_else(|| Fp::zero(modulus));
        acc = acc.add(&coeff.mul(&v));
    }
    for mt in &expr.mul_terms {
        let coeff = Fp::from_decimal(&mt.coeff.decimal(), modulus);
        let l = assign
            .get_fp(mt.left)
            .cloned()
            .unwrap_or_else(|| Fp::zero(modulus));
        let r = assign
            .get_fp(mt.right)
            .cloned()
            .unwrap_or_else(|| Fp::zero(modulus));
        acc = acc.add(&coeff.mul(&l).mul(&r));
    }
    acc
}

/// Run the witness-generation program, returning the full variable assignment.
pub fn solve(
    program: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>, SolveError> {
    solve_witness(
        &program.vars,
        &program.witness_gen,
        modulus_of(program)?,
        inputs,
    )
}

/// Run the witness-generation program (independent of the constraint form) so
/// the `PrimitiveProgram` and `CircuitProgram` entry points share it.
fn solve_witness(
    vars: &[crate::primitive::Var],
    witness_gen: &[WitnessGen],
    modulus: BigUint,
    inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>, SolveError> {
    // Dense assignment sized to the highest var id (ids are contiguous, so this
    // is tight); `Option` handles any gap and the not-yet-produced slots.
    let n = vars
        .iter()
        .map(|v| v.id as usize)
        .max()
        .map_or(0, |m| m + 1);
    let mut assign = DenseAssign::with_len(n);

    // Seed inputs.
    for var in vars {
        if matches!(
            var.role,
            crate::primitive::VarRole::PublicInput | crate::primitive::VarRole::PrivateInput
        ) {
            let decimal = inputs
                .get(&var.id)
                .ok_or(SolveError::MissingInput(var.id))?;
            assign.set(var.id, Fp::from_decimal(decimal, &modulus));
        }
    }

    // Run the hint program. Large programs exploit the witness DAG (independent
    // ops at the same dependency level run in parallel); small ones stay
    // sequential to avoid the level-analysis overhead.
    const PAR_THRESHOLD: usize = 4096;
    if witness_gen.len() >= PAR_THRESHOLD {
        solve_witness_parallel(witness_gen, &modulus, &mut assign)?;
    } else {
        // Collect each op's outputs into a scratch buffer (so the op reads the
        // shared assignment while `emit` doesn't alias it), then apply them.
        let mut outs: Vec<(VarId, Fp)> = Vec::new();
        for op in witness_gen {
            outs.clear();
            exec_witness_op(op, &assign, &modulus, &mut |v, val| outs.push((v, val)))?;
            for (v, val) in outs.drain(..) {
                assign.set(v, val);
            }
        }
    }

    Ok(assign.into_btreemap())
}

/// Execute one witness-gen op against the current (immutable) assignment,
/// reporting each output via `emit`. Pure over its inputs, so the parallel
/// solver can run independent ops concurrently.
fn exec_witness_op(
    op: &WitnessGen,
    assign: &impl Assignment,
    modulus: &BigUint,
    emit: &mut impl FnMut(VarId, Fp),
) -> Result<(), SolveError> {
    match op {
        WitnessGen::Product { out, left, right } => {
            let l = eval_lc(left, assign, modulus);
            let r = eval_lc(right, assign, modulus);
            emit(*out, l.mul(&r));
        }
        WitnessGen::Linear { out, lc } => {
            let v = eval_lc(lc, assign, modulus);
            emit(*out, v);
        }
        WitnessGen::Xor { out, a, b } => {
            let av = eval_lc(a, assign, modulus);
            let bv = eval_lc(b, assign, modulus);
            let ab = av.mul(&bv);
            // a + b - 2ab
            let v = av.add(&bv).add(&ab.mul(&Fp::from_decimal("-2", modulus)));
            emit(*out, v);
        }
        WitnessGen::Or { out, a, b } => {
            let av = eval_lc(a, assign, modulus);
            let bv = eval_lc(b, assign, modulus);
            let ab = av.mul(&bv);
            // a + b - ab
            let v = av.add(&bv).add(&ab.mul(&Fp::from_decimal("-1", modulus)));
            emit(*out, v);
        }
        WitnessGen::Inverse { out, input } => {
            let v = eval_lc(input, assign, modulus);
            // Inverse-or-zero: 0 maps to 0 (the is_zero convention).
            let inv = v.inverse().unwrap_or_else(|| Fp::zero(modulus));
            emit(*out, inv);
        }
        WitnessGen::InverseOrZero { out, input } => {
            // `x⁻¹` when `x ≠ 0`, else `0` (unconstrained at 0)
            let v = eval_lc(input, assign, modulus);
            let inv = v.inverse().unwrap_or_else(|| Fp::zero(modulus));
            emit(*out, inv);
        }
        WitnessGen::Bit { out, input, index } => {
            let v = eval_lc(input, assign, modulus);
            emit(*out, v.bit(*index as usize));
        }
        WitnessGen::Bits { outs, input } => {
            // Batched form of `Bit`: `outs[i]` is bit `i` of the input.
            let v = eval_lc(input, assign, modulus);
            for (i, out) in outs.iter().enumerate() {
                emit(*out, v.bit(i));
            }
        }
        WitnessGen::DivRem { q, r, num, den } => {
            let n = eval_lc(num, assign, modulus);
            let d = eval_lc(den, assign, modulus);
            if d.is_zero() {
                return Err(SolveError::DivisionByZero);
            }
            // Integer (not field) division: use the canonical representatives.
            let (nb, db) = (n.to_biguint(), d.to_biguint());
            let quotient = &nb / &db;
            let remainder = &nb % &db;
            emit(*q, Fp::new(quotient, modulus));
            emit(*r, Fp::new(remainder, modulus));
        }
        WitnessGen::MulModDivMod {
            q,
            r,
            a,
            b,
            modulus: m,
            limb_bits,
        } => {
            if *limb_bits > MAX_LIMB_BITS {
                return Err(SolveError::MalformedHint("limb_bits exceeds MAX_LIMB_BITS"));
            }
            let recompose = |limbs: &[LinearCombination]| -> BigUint {
                let mut acc = BigUint::zero();
                for (i, lc) in limbs.iter().enumerate() {
                    let v = eval_lc(lc, assign, modulus).to_biguint();
                    acc += v << (*limb_bits as usize * i);
                }
                acc
            };
            let a_big = recompose(a);
            let b_big = recompose(b);
            let m_big = recompose(m);
            if m_big.is_zero() {
                return Err(SolveError::DivisionByZero);
            }
            let p = &a_big * &b_big;
            let quotient = &p / &m_big;
            let remainder = &p % &m_big;
            let mask = (BigUint::one() << *limb_bits as usize) - BigUint::one();
            for (i, &out) in q.iter().enumerate() {
                let limb = (&quotient >> (*limb_bits as usize * i)) & &mask;
                emit(out, Fp::new(limb, modulus));
            }
            for (i, &out) in r.iter().enumerate() {
                let limb = (&remainder >> (*limb_bits as usize * i)) & &mask;
                emit(out, Fp::new(limb, modulus));
            }
        }
        WitnessGen::ModInverse {
            out,
            a,
            modulus: m,
            limb_bits,
        } => {
            if *limb_bits > MAX_LIMB_BITS {
                return Err(SolveError::MalformedHint("limb_bits exceeds MAX_LIMB_BITS"));
            }
            let recompose = |limbs: &[LinearCombination]| -> BigUint {
                let mut acc = BigUint::zero();
                for (i, lc) in limbs.iter().enumerate() {
                    let v = eval_lc(lc, assign, modulus).to_biguint();
                    acc += v << (*limb_bits as usize * i);
                }
                acc
            };
            let m_big = recompose(m);
            // modulus >= 2 (÷0 / M-2 guard)
            if m_big < BigUint::from(2u32) {
                return Err(SolveError::MalformedHint("mod_inverse: modulus < 2"));
            }
            let a_big = recompose(a) % &m_big;
            if a_big.is_zero() {
                return Err(SolveError::DivisionByZero);
            }
            // Fermat inverse A^(M-2) mod M (M prime — holds for the secp256k1
            // base/scalar fields this hint targets).
            let w = a_big.modpow(&(&m_big - BigUint::from(2u32)), &m_big);
            let mask = (BigUint::one() << *limb_bits as usize) - BigUint::one();
            for (i, &o) in out.iter().enumerate() {
                let limb = (&w >> (*limb_bits as usize * i)) & &mask;
                emit(o, Fp::new(limb, modulus));
            }
        }
        WitnessGen::Sub2 {
            qabs,
            r,
            a,
            b,
            c,
            modulus: m,
            limb_bits,
        } => {
            if *limb_bits > MAX_LIMB_BITS {
                return Err(SolveError::MalformedHint("limb_bits exceeds MAX_LIMB_BITS"));
            }
            let recompose = |limbs: &[LinearCombination]| -> BigUint {
                let mut acc = BigUint::zero();
                for (i, lc) in limbs.iter().enumerate() {
                    let v = eval_lc(lc, assign, modulus).to_biguint();
                    acc += v << (*limb_bits as usize * i);
                }
                acc
            };
            let a_big = recompose(a);
            let b_big = recompose(b);
            let c_big = recompose(c);
            let m_big = recompose(m);
            if m_big.is_zero() {
                return Err(SolveError::DivisionByZero);
            }
            // s = a + 2m - b - c; r = s mod m; qabs = 2 - s/m ∈ {0,1,2}.
            // guard subtractions (adversarial limbs could underflow)
            let lhs = &a_big + &m_big + &m_big;
            let rhs = &b_big + &c_big;
            if lhs < rhs {
                return Err(SolveError::MalformedHint("sub2: a + 2m < b + c"));
            }
            let s = lhs - rhs;
            let remainder = &s % &m_big;
            let q_s = &s / &m_big;
            if q_s > BigUint::from(2u32) {
                return Err(SolveError::MalformedHint(
                    "sub2: quotient out of range (inputs >= modulus)",
                ));
            }
            let q_abs = BigUint::from(2u32) - &q_s;
            emit(*qabs, Fp::new(q_abs, modulus));
            let mask = (BigUint::one() << *limb_bits as usize) - BigUint::one();
            for (i, &out) in r.iter().enumerate() {
                let limb = (&remainder >> (*limb_bits as usize * i)) & &mask;
                emit(out, Fp::new(limb, modulus));
            }
        }
    }
    Ok(())
}

/// Solve the witness in parallel by exploiting the op DAG: ops at the same
/// dependency level (none reading another's output) are independent, so each
/// level runs across rayon. Ops are emitted in a valid topological order, so a
/// single forward pass assigns levels. Produces the identical assignment to the
/// sequential path (all outputs of a variable come from one op; a level never
/// reads a same-level output).
fn solve_witness_parallel(
    witness_gen: &[WitnessGen],
    modulus: &BigUint,
    assign: &mut DenseAssign,
) -> Result<(), SolveError> {
    use rayon::prelude::*;
    let mut producer: BTreeMap<VarId, usize> = BTreeMap::new();
    for (idx, op) in witness_gen.iter().enumerate() {
        op_output_vars(op, |o| {
            producer.insert(o, idx);
        });
    }
    let mut level = vec![0usize; witness_gen.len()];
    let mut max_level = 0usize;
    for (idx, op) in witness_gen.iter().enumerate() {
        let mut lv = 0usize;
        op_read_vars(op, |rv| {
            if let Some(&p) = producer.get(&rv) {
                lv = lv.max(level[p] + 1);
            }
        });
        level[idx] = lv;
        max_level = max_level.max(lv);
    }
    let mut levels: Vec<Vec<usize>> = vec![Vec::new(); max_level + 1];
    for (idx, &lv) in level.iter().enumerate() {
        levels[lv].push(idx);
    }
    for level_ops in &levels {
        let snapshot: &DenseAssign = assign;
        let produced: Vec<Vec<(VarId, Fp)>> = level_ops
            .par_iter()
            .map(|&idx| {
                let mut out = Vec::new();
                exec_witness_op(&witness_gen[idx], snapshot, modulus, &mut |v, val| {
                    out.push((v, val))
                })?;
                Ok::<_, SolveError>(out)
            })
            .collect::<Result<Vec<_>, _>>()?;
        for out in produced {
            for (v, val) in out {
                assign.set(v, val);
            }
        }
    }
    Ok(())
}

/// Visit each output `VarId` a witness-gen op writes.
fn op_output_vars(op: &WitnessGen, mut f: impl FnMut(VarId)) {
    match op {
        WitnessGen::Product { out, .. }
        | WitnessGen::Linear { out, .. }
        | WitnessGen::Xor { out, .. }
        | WitnessGen::Or { out, .. }
        | WitnessGen::Inverse { out, .. }
        | WitnessGen::InverseOrZero { out, .. }
        | WitnessGen::Bit { out, .. } => f(*out),
        WitnessGen::Bits { outs, .. } => outs.iter().for_each(|o| f(*o)),
        WitnessGen::DivRem { q, r, .. } => {
            f(*q);
            f(*r);
        }
        WitnessGen::MulModDivMod { q, r, .. } => {
            q.iter().chain(r).for_each(|o| f(*o));
        }
        WitnessGen::ModInverse { out, .. } => out.iter().for_each(|o| f(*o)),
        WitnessGen::Sub2 { qabs, r, .. } => {
            f(*qabs);
            r.iter().for_each(|o| f(*o));
        }
    }
}

/// Visit each input `VarId` a witness-gen op reads (the vars referenced by its
/// input linear combinations).
fn op_read_vars(op: &WitnessGen, mut f: impl FnMut(VarId)) {
    fn add(lc: &LinearCombination, f: &mut impl FnMut(VarId)) {
        lc.terms.iter().for_each(|t| f(t.var));
    }
    let each = |lcs: &[LinearCombination], f: &mut dyn FnMut(VarId)| {
        for lc in lcs {
            lc.terms.iter().for_each(|t| f(t.var));
        }
    };
    match op {
        WitnessGen::Product { left, right, .. } => {
            add(left, &mut f);
            add(right, &mut f);
        }
        WitnessGen::Linear { lc, .. } => add(lc, &mut f),
        WitnessGen::Xor { a, b, .. } | WitnessGen::Or { a, b, .. } => {
            add(a, &mut f);
            add(b, &mut f);
        }
        WitnessGen::Inverse { input, .. }
        | WitnessGen::InverseOrZero { input, .. }
        | WitnessGen::Bit { input, .. }
        | WitnessGen::Bits { input, .. } => add(input, &mut f),
        WitnessGen::DivRem { num, den, .. } => {
            add(num, &mut f);
            add(den, &mut f);
        }
        WitnessGen::MulModDivMod { a, b, modulus, .. } => {
            each(a, &mut f);
            each(b, &mut f);
            each(modulus, &mut f);
        }
        WitnessGen::ModInverse { a, modulus, .. } => {
            each(a, &mut f);
            each(modulus, &mut f);
        }
        WitnessGen::Sub2 {
            a, b, c, modulus, ..
        } => {
            each(a, &mut f);
            each(b, &mut f);
            each(c, &mut f);
            each(modulus, &mut f);
        }
    }
}

/// Construct a field element from a decimal string against a program's field
/// (for tests / tooling that need to inject specific witness values).
pub fn fp_from_decimal(s: &str, program: &PrimitiveProgram) -> Fp {
    Fp::from_decimal(s, &modulus_of(program).expect("valid field modulus"))
}

/// Check that every constraint evaluates to zero under `assign`.
pub fn check(program: &PrimitiveProgram, assign: &BTreeMap<VarId, Fp>) -> Result<(), SolveError> {
    let modulus = modulus_of(program)?;
    for (i, c) in program.constraints.iter().enumerate() {
        if !eval_expression(c, assign, &modulus).is_zero() {
            return Err(SolveError::ConstraintFailed(i));
        }
    }
    Ok(())
}

/// Convenience: solve the witness from inputs and check all constraints hold.
pub fn solve_and_check(
    program: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>, SolveError> {
    let assign = solve(program, inputs)?;
    check(program, &assign)?;
    Ok(assign)
}

// ===========================================================================
// Under-constraint (soundness smoke-test) analyzer.
// ===========================================================================

/// A derived variable the analyzer could not prove is uniquely pinned by the
/// constraints (holding every other variable at the honest witness). This is a
/// potential under-constraint — a value a malicious prover might be able to
/// change without violating any constraint.
#[derive(Debug, Clone)]
pub struct UnderConstrained {
    pub var: VarId,
    pub name: String,
    pub reason: String,
}

/// Reduce a constraint to the univariate polynomial `a·v² + b·v + c` obtained by
/// fixing every variable except `v` at the honest assignment.
fn univariate(
    expr: &Expression,
    v: VarId,
    assign: &BTreeMap<VarId, Fp>,
    modulus: &BigUint,
) -> (Fp, Fp, Fp) {
    let zero = || Fp::zero(modulus);
    let get = |id: VarId| assign.get(&id).cloned().unwrap_or_else(zero);
    let (mut a, mut b, mut c) = (zero(), zero(), zero());
    for mt in &expr.mul_terms {
        let coeff = Fp::from_decimal(&mt.coeff.decimal(), modulus);
        match (mt.left == v, mt.right == v) {
            (true, true) => a = a.add(&coeff),
            (true, false) => b = b.add(&coeff.mul(&get(mt.right))),
            (false, true) => b = b.add(&coeff.mul(&get(mt.left))),
            (false, false) => c = c.add(&coeff.mul(&get(mt.left)).mul(&get(mt.right))),
        }
    }
    for lt in &expr.linear_terms {
        let coeff = Fp::from_decimal(&lt.coeff.decimal(), modulus);
        if lt.var == v {
            b = b.add(&coeff);
        } else {
            c = c.add(&coeff.mul(&get(lt.var)));
        }
    }
    c = c.add(&Fp::from_decimal(&expr.constant.decimal(), modulus));
    (a, b, c)
}

/// Check every `Derived` variable is uniquely determined by the constraints,
/// given the honest witness `assign` (which must satisfy the program).
///
/// This is a *necessary* soundness check, not a full proof: it catches free /
/// two-valued variables (the dominant under-constraint bug class) by testing,
/// for each variable, whether any value other than the honest one also
/// satisfies every constraint that references it (all other variables fixed). A
/// variable pinned by a linear constraint is uniquely determined; one pinned
/// only by quadratics is checked against the quadratics' second roots (Vieta).
pub fn analyze_underconstrained(
    program: &PrimitiveProgram,
    assign: &BTreeMap<VarId, Fp>,
) -> Vec<UnderConstrained> {
    use crate::primitive::VarRole;
    let modulus = modulus_of(program).expect("valid field modulus");

    // Index: variable -> indices of constraints that reference it.
    let mut refs: BTreeMap<VarId, Vec<usize>> = BTreeMap::new();
    for (i, expr) in program.constraints.iter().enumerate() {
        let mut seen = std::collections::BTreeSet::new();
        for mt in &expr.mul_terms {
            seen.insert(mt.left);
            seen.insert(mt.right);
        }
        for lt in &expr.linear_terms {
            seen.insert(lt.var);
        }
        for v in seen {
            refs.entry(v).or_default().push(i);
        }
    }

    let mut out = Vec::new();
    for var in &program.vars {
        if !matches!(var.role, VarRole::Derived) {
            continue;
        }
        let v = var.id;
        let alpha = assign
            .get(&v)
            .cloned()
            .unwrap_or_else(|| Fp::zero(&modulus));
        let Some(cons) = refs.get(&v) else {
            out.push(UnderConstrained {
                var: v,
                name: var.name.clone(),
                reason: "no constraint references this variable".into(),
            });
            continue;
        };

        let mut pinned_linear = false;
        let mut restricted = false;
        let mut candidates: Vec<Fp> = Vec::new();
        for &ci in cons {
            let (a, b, c) = univariate(&program.constraints[ci], v, assign, &modulus);
            let _ = &c;
            if a.is_zero() && b.is_zero() {
                continue; // this constraint does not restrict v
            }
            restricted = true;
            if a.is_zero() {
                pinned_linear = true; // linear (b != 0): unique root
                break;
            }
            // Quadratic: the other root is (-b/a) - alpha (Vieta).
            let inv_a = a.inverse().expect("a != 0 in quadratic branch");
            candidates.push(b.neg().mul(&inv_a).sub(&alpha));
        }
        if pinned_linear {
            continue;
        }
        if !restricted {
            out.push(UnderConstrained {
                var: v,
                name: var.name.clone(),
                reason: "variable's coefficient is zero in every referencing constraint (free)"
                    .into(),
            });
            continue;
        }
        // Only quadratic pins: does any second root satisfy ALL referencing
        // constraints? If so, v is two-valued (under-constrained).
        for beta in &candidates {
            if *beta == alpha {
                continue;
            }
            let satisfies_all = cons.iter().all(|&ci| {
                let (a, b, c) = univariate(&program.constraints[ci], v, assign, &modulus);
                a.mul(beta).mul(beta).add(&b.mul(beta)).add(&c).is_zero()
            });
            if satisfies_all {
                out.push(UnderConstrained {
                    var: v,
                    name: var.name.clone(),
                    reason: "a different value also satisfies all its constraints (two-valued)"
                        .into(),
                });
                break;
            }
        }
    }
    out
}

// ===========================================================================
// CircuitProgram entry points — operate on R1CS rows (`a·b = c`) directly,
// avoiding the `to_primitive` flattening. `xark prove`/`check` use these so a
// loaded `circuit.xbc` is never materialized into `Expression`s. Equivalence
// with the `Expression`-based path is asserted in the tests below.
// ===========================================================================

/// Run the witness-generation program of a [`CircuitProgram`].
pub fn solve_cp(
    program: &crate::circuit::CircuitProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>, SolveError> {
    solve_witness(
        &program.vars,
        &program.witness_gen,
        modulus_of_field(&program.field)?,
        inputs,
    )
}

/// Check every R1CS row `a·b == c` holds under `assign`.
pub fn check_cp(
    program: &crate::circuit::CircuitProgram,
    assign: &BTreeMap<VarId, Fp>,
) -> Result<(), SolveError> {
    let modulus = modulus_of_field(&program.field)?;
    for (i, row) in program.constraints.iter().enumerate() {
        let a = eval_lc(&row.a, assign, &modulus);
        let b = eval_lc(&row.b, assign, &modulus);
        let c = eval_lc(&row.c, assign, &modulus);
        if !a.mul(&b).sub(&c).is_zero() {
            return Err(SolveError::ConstraintFailed(i));
        }
    }
    Ok(())
}

/// Solve the witness from inputs and check all rows hold.
pub fn solve_and_check_cp(
    program: &crate::circuit::CircuitProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>, SolveError> {
    let assign = solve_cp(program, inputs)?;
    check_cp(program, &assign)?;
    Ok(assign)
}

/// Reduce an R1CS row `a·b − c` to the univariate `A·v² + B·v + C` obtained by
/// fixing every variable except `v`. Splitting each of `a`, `b`, `c` into its
/// `v`-coefficient and the rest gives, for `a = aᵥ·v + a₀` etc.:
/// `A = aᵥ·bᵥ`, `B = aᵥ·b₀ + a₀·bᵥ − cᵥ`, `C = a₀·b₀ − c₀`.
fn univariate_r1cs(
    row: &crate::circuit::R1csRow,
    v: VarId,
    assign: &BTreeMap<VarId, Fp>,
    modulus: &BigUint,
) -> (Fp, Fp, Fp) {
    let split = |lc: &LinearCombination| -> (Fp, Fp) {
        let mut coeff_v = Fp::zero(modulus);
        let mut rest = Fp::from_decimal(&lc.constant.decimal(), modulus);
        for t in &lc.terms {
            let coeff = Fp::from_decimal(&t.coeff.decimal(), modulus);
            if t.var == v {
                coeff_v = coeff_v.add(&coeff);
            } else {
                let val = assign
                    .get(&t.var)
                    .cloned()
                    .unwrap_or_else(|| Fp::zero(modulus));
                rest = rest.add(&coeff.mul(&val));
            }
        }
        (coeff_v, rest)
    };
    let (av, a0) = split(&row.a);
    let (bv, b0) = split(&row.b);
    let (cv, c0) = split(&row.c);
    let a = av.mul(&bv);
    let b = av.mul(&b0).add(&a0.mul(&bv)).sub(&cv);
    let c = a0.mul(&b0).sub(&c0);
    (a, b, c)
}

/// [`analyze_underconstrained`] over R1CS rows (`a·b = c`) directly.
pub fn analyze_underconstrained_cp(
    program: &crate::circuit::CircuitProgram,
    assign: &BTreeMap<VarId, Fp>,
) -> Vec<UnderConstrained> {
    use crate::primitive::VarRole;
    use rayon::prelude::*;
    let modulus = modulus_of_field(&program.field).expect("valid field modulus");

    // Index: variable -> indices of rows that reference it (any of a, b, c).
    let mut refs: BTreeMap<VarId, Vec<usize>> = BTreeMap::new();
    for (i, row) in program.constraints.iter().enumerate() {
        let mut seen = std::collections::BTreeSet::new();
        for lc in [&row.a, &row.b, &row.c] {
            for t in &lc.terms {
                seen.insert(t.var);
            }
        }
        for v in seen {
            refs.entry(v).or_default().push(i);
        }
    }

    // Each derived variable's verdict is independent (reads only the shared
    // immutable index/constraints/assignment), so check them across rayon's
    // thread pool. `collect` preserves the source order, keeping the output
    // deterministic.
    program
        .vars
        .par_iter()
        .filter(|var| matches!(var.role, VarRole::Derived))
        .filter_map(|var| check_one_var_cp(var, &refs, &program.constraints, assign, &modulus))
        .collect()
}

/// The per-variable under-constraint verdict (`None` = uniquely pinned). Pure
/// over shared immutable inputs, so [`analyze_underconstrained_cp`] runs it in
/// parallel.
fn check_one_var_cp(
    var: &crate::primitive::Var,
    refs: &BTreeMap<VarId, Vec<usize>>,
    constraints: &[crate::circuit::R1csRow],
    assign: &BTreeMap<VarId, Fp>,
    modulus: &BigUint,
) -> Option<UnderConstrained> {
    let v = var.id;
    let alpha = assign.get(&v).cloned().unwrap_or_else(|| Fp::zero(modulus));
    let Some(cons) = refs.get(&v) else {
        return Some(UnderConstrained {
            var: v,
            name: var.name.clone(),
            reason: "no constraint references this variable".into(),
        });
    };

    let mut pinned_linear = false;
    let mut restricted = false;
    let mut candidates: Vec<Fp> = Vec::new();
    for &ci in cons {
        let (a, b, _c) = univariate_r1cs(&constraints[ci], v, assign, modulus);
        if a.is_zero() && b.is_zero() {
            continue;
        }
        restricted = true;
        if a.is_zero() {
            pinned_linear = true;
            break;
        }
        let inv_a = a.inverse().expect("a != 0 in quadratic branch");
        candidates.push(b.neg().mul(&inv_a).sub(&alpha));
    }
    if pinned_linear {
        return None;
    }
    if !restricted {
        return Some(UnderConstrained {
            var: v,
            name: var.name.clone(),
            reason: "variable's coefficient is zero in every referencing constraint (free)".into(),
        });
    }
    for beta in &candidates {
        if *beta == alpha {
            continue;
        }
        let satisfies_all = cons.iter().all(|&ci| {
            let (a, b, c) = univariate_r1cs(&constraints[ci], v, assign, modulus);
            a.mul(beta).mul(beta).add(&b.mul(beta)).add(&c).is_zero()
        });
        if satisfies_all {
            return Some(UnderConstrained {
                var: v,
                name: var.name.clone(),
                reason: "a different value also satisfies all its constraints (two-valued)".into(),
            });
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitive::{FieldSpec, PrimitiveProgram};

    /// The `CircuitProgram` (R1CS-row) solver path must agree exactly with the
    /// `PrimitiveProgram` (Expression) path — same witness, same constraint
    /// pass/fail, same under-constraint verdicts (`_cp` derives its `Expression`
    /// view via `to_primitive`, so this pins `solve_cp`/`check_cp`/`analyze…_cp`
    /// against the reference). Covers a sound mul-gate, a dangling advice var
    /// (free path), and a booleanity-only bit (two-valued quadratic path).
    #[test]
    fn cp_solver_matches_primitive_path() {
        use crate::circuit::{CircuitProgram, R1csRow};
        use crate::primitive::{Var, VarRole, WitnessGen};
        let lc = LinearCombination::var;
        let cst = LinearCombination::constant;

        let row = |a, b, c| R1csRow {
            a,
            b,
            c,
            note: None,
        };
        let cp = CircuitProgram {
            field: crate::primitive::FieldSpec::bn254(),
            vars: vec![
                Var {
                    id: 0,
                    name: "a".into(),
                    role: VarRole::PrivateInput,
                },
                Var {
                    id: 1,
                    name: "b".into(),
                    role: VarRole::PrivateInput,
                },
                Var {
                    id: 2,
                    name: "t".into(),
                    role: VarRole::Derived,
                },
                Var {
                    id: 3,
                    name: "w".into(),
                    role: VarRole::Derived,
                }, // dangling advice
                Var {
                    id: 4,
                    name: "bit".into(),
                    role: VarRole::Derived,
                }, // booleanity-only
            ],
            constraints: vec![
                row(lc(0), lc(1), lc(2)), // a * b = t   (sound)
                row(lc(4), lc(4), lc(4)), // bit*bit = bit (two-valued)
            ],
            witness_gen: vec![
                WitnessGen::Product {
                    out: 2,
                    left: lc(0),
                    right: lc(1),
                },
                WitnessGen::Inverse {
                    out: 3,
                    input: lc(0),
                }, // w unpinned
                WitnessGen::Bit {
                    out: 4,
                    input: cst("1"),
                    index: 0,
                },
            ],
        };
        let prim = cp.to_primitive();
        let inputs = BTreeMap::from([(0u32, "3".to_string()), (1u32, "4".to_string())]);

        let a_cp = solve_cp(&cp, &inputs).expect("solve_cp");
        let a_pr = solve(&prim, &inputs).expect("solve");
        assert_eq!(a_cp, a_pr, "witness assignment must match");

        assert_eq!(
            check_cp(&cp, &a_cp).is_ok(),
            check(&prim, &a_pr).is_ok(),
            "constraint check verdict must match"
        );
        check_cp(&cp, &a_cp).expect("valid witness passes check_cp");

        let holes_cp: Vec<VarId> = analyze_underconstrained_cp(&cp, &a_cp)
            .iter()
            .map(|h| h.var)
            .collect();
        let holes_pr: Vec<VarId> = analyze_underconstrained(&prim, &a_pr)
            .iter()
            .map(|h| h.var)
            .collect();
        assert_eq!(holes_cp, holes_pr, "under-constraint verdicts must match");
        assert!(holes_cp.contains(&3), "dangling advice `w` must be flagged");
        assert!(holes_cp.contains(&4), "two-valued `bit` must be flagged");
    }

    /// Exercise the parallel witness solver (>`PAR_THRESHOLD` ops) over a
    /// two-level DAG — `t_i = x_i²`, then `u_i = t_i²` — verifying every output.
    /// A level-ordering bug (reading a same-level output) or a lost write would
    /// give the wrong `u_i`, and a var only lands via one op so parallel writes
    /// never race.
    #[test]
    fn parallel_solve_large_dag_is_correct() {
        use crate::primitive::{FieldSpec, PrimitiveProgram, Var, VarRole, WitnessGen};
        let n = 5000u32; // > PAR_THRESHOLD, so `solve` takes the parallel path
        let mut vars = Vec::new();
        for i in 0..n {
            vars.push(Var {
                id: i,
                name: format!("x{i}"),
                role: VarRole::PrivateInput,
            });
        }
        for i in n..3 * n {
            vars.push(Var {
                id: i,
                name: format!("d{i}"),
                role: VarRole::Derived,
            });
        }
        let mut witness_gen = Vec::new();
        // level 1: t_i = x_i * x_i
        for i in 0..n {
            witness_gen.push(WitnessGen::Product {
                out: n + i,
                left: LinearCombination::var(i),
                right: LinearCombination::var(i),
            });
        }
        // level 2: u_i = t_i * t_i  (depends on level 1)
        for i in 0..n {
            witness_gen.push(WitnessGen::Product {
                out: 2 * n + i,
                left: LinearCombination::var(n + i),
                right: LinearCombination::var(n + i),
            });
        }
        let program = PrimitiveProgram {
            field: FieldSpec::bn254(),
            vars,
            constraints: vec![],
            witness_gen,
        };
        let inputs: BTreeMap<VarId, String> =
            (0..n).map(|i| (i, ((i % 7) + 1).to_string())).collect();
        let assign = solve(&program, &inputs).expect("parallel solve");
        for i in 0..n {
            let x = u64::from((i % 7) + 1);
            assert_eq!(assign[&(n + i)].to_decimal(), (x * x).to_string(), "t{i}");
            assert_eq!(
                assign[&(2 * n + i)].to_decimal(),
                (x * x * x * x).to_string(),
                "u{i}"
            );
        }
    }

    fn program_with_modulus(modulus_decimal: &str) -> PrimitiveProgram {
        PrimitiveProgram {
            field: FieldSpec {
                name: "test".into(),
                modulus_decimal: modulus_decimal.into(),
            },
            vars: vec![],
            constraints: vec![],
            witness_gen: vec![],
        }
    }

    /// A malformed field modulus is rejected cleanly, not panicked.
    #[test]
    fn malformed_modulus_is_rejected_not_panicked() {
        for m in ["0", "1", "", "not-a-number"] {
            let program = program_with_modulus(m);
            assert!(
                matches!(
                    solve(&program, &BTreeMap::new()),
                    Err(SolveError::MalformedModulus)
                ),
                "modulus {m:?} must be rejected"
            );
        }
        // A valid modulus still solves the (trivial) program.
        let ok = program_with_modulus(
            "21888242871839275222246405745257275088548364400416034343698204186575808495617",
        );
        assert!(solve(&ok, &BTreeMap::new()).is_ok());
    }
}
