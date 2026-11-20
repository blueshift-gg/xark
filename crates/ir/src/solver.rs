//! Reference witness solver + constraint checker for the [primitive IR].
//!
//! Given values for the input variables, runs the witness-generation program to
//! fill every derived/hint variable, then checks that all AssertZero constraints
//! evaluate to zero — validating functions end-to-end from the emitted IR alone,
//! no proving system required.
//!
//! [primitive IR]: crate::primitive

use std::collections::BTreeMap;

use ark_bn254::Fr;
use ark_ff::{BigInteger, Field as ArkField, PrimeField};
use num_bigint::BigUint;
use num_traits::{One, Signed, Zero};

use crate::linear_combination::{LinearCombination, VarId};
use crate::primitive::{Expression, PrimitiveProgram, WitnessGen};

/// A field element: a BN254 scalar (Montgomery `Fr`) on the common path, or an
/// arbitrary-modulus big integer for other fields. The BN254 fast path uses
/// native `Fr` arithmetic instead of `num-bigint` modmul/`modpow` inversion,
/// which dominates witness-gen and soundness-check cost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fp {
    Bn254(Fr),
    Generic { value: BigUint, modulus: BigUint },
}

/// Is `modulus` the BN254 scalar-field prime (the field xark's `Field` is)?
pub(crate) fn is_bn254(modulus: &BigUint) -> bool {
    static M: std::sync::OnceLock<BigUint> = std::sync::OnceLock::new();
    modulus == M.get_or_init(|| BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le()))
}

impl Fp {
    pub(crate) fn new(value: BigUint, modulus: &BigUint) -> Self {
        if is_bn254(modulus) {
            Fp::Bn254(Fr::from_le_bytes_mod_order(&value.to_bytes_le()))
        } else {
            Fp::Generic {
                value: value % modulus,
                modulus: modulus.clone(),
            }
        }
    }

    pub(crate) fn zero(modulus: &BigUint) -> Self {
        if is_bn254(modulus) {
            Fp::Bn254(Fr::from(0u64))
        } else {
            Fp::Generic {
                value: BigUint::zero(),
                modulus: modulus.clone(),
            }
        }
    }

    /// A field constant reduced into the field, without a decimal round trip.
    pub(crate) fn from_const(c: &crate::field::FieldConst, modulus: &BigUint) -> Self {
        if let Some(n) = c.as_i64() {
            Fp::from_i64(n, modulus)
        } else if is_bn254(modulus) {
            Fp::Bn254(c.to_bn254_fr())
        } else {
            Fp::from_bigint(&c.big(), modulus)
        }
    }

    /// Reduce a signed decimal string into the field.
    pub(crate) fn from_decimal(s: &str, modulus: &BigUint) -> Self {
        let trimmed = s.trim();
        // Fast path: most coefficients are small integers; parsing as `i64` skips
        // the `BigUint` alloc + byte-reduction on `eval_lc`'s hot loop, which
        // re-parses every coefficient on every evaluation.
        if let Ok(n) = trimmed.parse::<i64>() {
            return Fp::from_i64(n, modulus);
        }
        let (neg, mag) = match trimmed.strip_prefix('-') {
            Some(m) => (true, m),
            None => (false, trimmed),
        };
        let m = BigUint::parse_bytes(mag.as_bytes(), 10).unwrap_or_else(BigUint::zero);
        let v = Fp::new(m, modulus);
        if neg { v.neg() } else { v }
    }

    /// Reduce a signed `BigInt` into the field without a decimal round-trip.
    pub(crate) fn from_bigint(v: &num_bigint::BigInt, modulus: &BigUint) -> Self {
        let (sign, mag) = v.to_bytes_le();
        let f = Fp::new(BigUint::from_bytes_le(&mag), modulus);
        if sign == num_bigint::Sign::Minus {
            f.neg()
        } else {
            f
        }
    }

    /// Allocation-free small-integer constructor (the `from_decimal` fast path).
    pub(crate) fn from_i64(n: i64, modulus: &BigUint) -> Self {
        if is_bn254(modulus) {
            let mag = Fr::from(n.unsigned_abs());
            Fp::Bn254(if n < 0 { -mag } else { mag })
        } else {
            let mag = Fp::new(BigUint::from(n.unsigned_abs()), modulus);
            if n < 0 { mag.neg() } else { mag }
        }
    }

    pub(crate) fn add(&self, other: &Fp) -> Fp {
        match (self, other) {
            (Fp::Bn254(a), Fp::Bn254(b)) => Fp::Bn254(*a + *b),
            (Fp::Generic { value: a, modulus }, Fp::Generic { value: b, .. }) => Fp::Generic {
                value: (a + b) % modulus,
                modulus: modulus.clone(),
            },
            _ => unreachable!("field element variants must match"),
        }
    }

    pub(crate) fn mul(&self, other: &Fp) -> Fp {
        match (self, other) {
            (Fp::Bn254(a), Fp::Bn254(b)) => Fp::Bn254(*a * *b),
            (Fp::Generic { value: a, modulus }, Fp::Generic { value: b, .. }) => Fp::Generic {
                value: (a * b) % modulus,
                modulus: modulus.clone(),
            },
            _ => unreachable!("field element variants must match"),
        }
    }

    pub(crate) fn sub(&self, other: &Fp) -> Fp {
        match (self, other) {
            (Fp::Bn254(a), Fp::Bn254(b)) => Fp::Bn254(*a - *b),
            _ => self.add(&other.neg()),
        }
    }

    pub(crate) fn neg(&self) -> Fp {
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
    pub(crate) fn inverse(&self) -> Option<Fp> {
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

    pub(crate) fn is_zero(&self) -> bool {
        match self {
            Fp::Bn254(a) => *a == Fr::from(0u64),
            Fp::Generic { value, .. } => value.is_zero(),
        }
    }

    /// Bit `i` of the canonical representative, as a field `0`/`1`, for each `i`
    /// asked; the representative is computed once.
    fn bits(&self) -> impl Fn(usize) -> Fp + '_ {
        let bn254 = match self {
            Fp::Bn254(a) => Some(a.into_bigint()),
            Fp::Generic { .. } => None,
        };
        move |i| match (self, &bn254) {
            (Fp::Bn254(_), Some(b)) => Fp::Bn254(if b.get_bit(i) { Fr::one() } else { Fr::zero() }),
            (Fp::Generic { value, modulus }, _) => Fp::Generic {
                value: (value >> i) & BigUint::one(),
                modulus: modulus.clone(),
            },
            (Fp::Bn254(_), None) => unreachable!("a BN254 value has its representative"),
        }
    }

    pub fn to_decimal(&self) -> String {
        self.to_biguint().to_str_radix(10)
    }

    /// The raw BN254 scalar, when this element lives in that field, so the Groth16
    /// backend consumes the witness directly without a `Fr → decimal → Fr` round-trip.
    pub fn as_bn254_fr(&self) -> Option<Fr> {
        match self {
            Fp::Bn254(a) => Some(*a),
            Fp::Generic { .. } => None,
        }
    }

    pub(crate) fn to_biguint(&self) -> BigUint {
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

/// The [`WitnessGen::FakeGlv`] decomposition (ePrint 2025/933, §4): a nonzero
/// `(a₁, a₂, b₁, b₂)` of the lattice `a₁ + λa₂ ≡ u·(b₁ + λb₂) (mod m)` with the least
/// `max |·|` among small combinations of an LLL-reduced basis, if that is below
/// `2^⌈bits(m)/4⌉`. The lattice has determinant `m`, so by Minkowski a nonzero vector
/// with `max |·| < m^¼` exists; an LLL basis spells it with coefficients in `[−3, 3]`.
pub fn fake_glv(u: &BigUint, m: &BigUint, lambda: &BigUint) -> Option<[num_bigint::BigInt; 4]> {
    use num_bigint::BigInt;
    if m.is_zero() {
        return None;
    }
    let z = BigInt::zero;
    let int = |x: &BigUint| BigInt::from(x % m);
    let mut b: [[BigInt; 4]; 4] = [
        [BigInt::from(m.clone()), z(), z(), z()],
        [-int(lambda), BigInt::one(), z(), z()],
        [int(u), z(), BigInt::one(), z()],
        [int(&(u * lambda)), z(), z(), BigInt::one()],
    ];
    lll(&mut b);
    let bound = BigInt::one() << m.bits().div_ceil(4) as usize;
    let mut best: Option<(BigInt, [BigInt; 4])> = None;
    for idx in 0..7usize.pow(4) {
        let c: [i64; 4] = std::array::from_fn(|i| (idx / 7usize.pow(i as u32) % 7) as i64 - 3);
        let v: [BigInt; 4] =
            std::array::from_fn(|j| (0..4).map(|i| &b[i][j] * c[i]).sum::<BigInt>());
        let norm = v
            .iter()
            .map(|x| x.magnitude().clone())
            .max()
            .map(BigInt::from)?;
        if !norm.is_zero() && norm < bound && best.as_ref().is_none_or(|(n, _)| norm < *n) {
            best = Some((norm, v));
        }
    }
    best.map(|(_, v)| v)
}

/// LLL-reduce (δ = 0.99) the rows of `b` in place, in exact integer arithmetic:
/// Gram–Schmidt as the integral `dᵢ`, `λₖⱼ` of Cohen, *A Course in Computational
/// Algebraic Number Theory*, Algorithm 2.6.7, recomputed after every change.
fn lll(b: &mut [[num_bigint::BigInt; 4]; 4]) {
    use num_bigint::BigInt;
    type Gs = ([BigInt; 5], [[BigInt; 4]; 4]);
    let gram = |b: &[[BigInt; 4]; 4]| -> Gs {
        let dot = |x: &[BigInt; 4], y: &[BigInt; 4]| x.iter().zip(y).map(|(p, q)| p * q).sum();
        let mut d: [BigInt; 5] = std::array::from_fn(|_| BigInt::one());
        let mut lam: [[BigInt; 4]; 4] = Default::default();
        for k in 0..4 {
            for j in 0..=k {
                let mut v: BigInt = dot(&b[k], &b[j]);
                for i in 0..j {
                    v = (&d[i + 1] * v - &lam[k][i] * &lam[j][i]) / &d[i];
                }
                if j < k {
                    lam[k][j] = v;
                } else {
                    d[k + 1] = v;
                }
            }
        }
        (d, lam)
    };
    // ⌊x / y⌉ for y > 0.
    let round = |x: &BigInt, y: &BigInt| -> BigInt {
        let (n, d) = (x * 2u32 + y, y * 2u32);
        let q = &n / &d;
        if Signed::is_negative(&(&n % &d)) {
            q - 1
        } else {
            q
        }
    };
    let mut k = 1;
    while k < 4 {
        for j in (0..k).rev() {
            let (d, lam) = gram(b);
            if (&lam[k][j] * 2u32).magnitude() > d[j + 1].magnitude() {
                let q = round(&lam[k][j], &d[j + 1]);
                let row = b[j].clone();
                for (x, y) in b[k].iter_mut().zip(&row) {
                    *x -= &q * y;
                }
            }
        }
        let (d, lam) = gram(b);
        let l = &lam[k][k - 1];
        if &d[k + 1] * &d[k - 1] * 100u32 < &d[k] * &d[k] * 99u32 - l * l * 100u32 {
            b.swap(k, k - 1);
            k = k.saturating_sub(1).max(1);
        } else {
            k += 1;
        }
    }
}

pub(crate) fn modulus_of(program: &PrimitiveProgram) -> Result<BigUint, SolveError> {
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

/// Read access to a variable assignment. The witness solves and the streaming
/// check/analysis use dense slots (O(1) lookups); the flat check/analysis keep
/// the sparse `BTreeMap`. All flow through the same generic `eval_*` code.
pub(crate) trait Assignment {
    fn get_fp(&self, var: VarId) -> Option<&Fp>;
}

/// Dense slots indexed by `VarId`, as the streaming solve produces them.
impl Assignment for [Option<Fp>] {
    #[inline]
    fn get_fp(&self, var: VarId) -> Option<&Fp> {
        self.get(var as usize).and_then(|o| o.as_ref())
    }
}

impl Assignment for BTreeMap<VarId, Fp> {
    #[inline]
    fn get_fp(&self, var: VarId) -> Option<&Fp> {
        self.get(&var)
    }
}

/// A witness assignment stored densely by `VarId`. Var ids are contiguous, so a
/// flat `Vec` turns each per-term lookup from a `BTreeMap` descent into an index.
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

    /// Convert once at the boundary to the `BTreeMap` the public API returns.
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

fn eval_lc(lc: &LinearCombination, assign: &(impl Assignment + ?Sized), modulus: &BigUint) -> Fp {
    let mut acc = Fp::from_const(&lc.constant, modulus);
    for term in &lc.terms {
        let coeff = Fp::from_const(&term.coeff, modulus);
        let var = assign
            .get_fp(term.var)
            .cloned()
            .unwrap_or_else(|| Fp::zero(modulus));
        acc = acc.add(&coeff.mul(&var));
    }
    acc
}

fn eval_expression(expr: &Expression, assign: &impl Assignment, modulus: &BigUint) -> Fp {
    let mut acc = Fp::from_const(&expr.constant, modulus);
    for lt in &expr.linear_terms {
        let coeff = Fp::from_const(&lt.coeff, modulus);
        let v = assign
            .get_fp(lt.var)
            .cloned()
            .unwrap_or_else(|| Fp::zero(modulus));
        acc = acc.add(&coeff.mul(&v));
    }
    for mt in &expr.mul_terms {
        let coeff = Fp::from_const(&mt.coeff, modulus);
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
    // Dense assignment sized to the highest var id; `Option` handles any gap and
    // not-yet-produced slots.
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
    // same-level ops run in parallel); small ones stay sequential to avoid the
    // level-analysis overhead.
    const PAR_THRESHOLD: usize = 4096;
    if witness_gen.len() >= PAR_THRESHOLD {
        solve_witness_parallel(witness_gen, &modulus, &mut assign)?;
    } else {
        solve_witness_sequential(witness_gen, &modulus, &mut assign)?;
    }

    Ok(assign.into_btreemap())
}

/// Dense slots (`slots[id]`) as the map the public API returns.
pub(crate) fn slots_into_map(slots: Vec<Option<Fp>>) -> BTreeMap<VarId, Fp> {
    DenseAssign { slots }.into_btreemap()
}

/// Solve the witness by **streaming** the hint program in bounded batches: the
/// caller's `feed` closure emits ops one at a time (in topological order); we
/// accumulate up to `BATCH` of them, solve that batch, apply its outputs, and
/// drop it before taking the next. Because ops are topologically ordered, any op
/// depends only on outputs already in `assign` (earlier batch) or earlier in its
/// own batch — so the result is identical to solving the whole program at once,
/// but peak memory is one batch of `WitnessGen` instead of the full expanded
/// `Vec` (the dominant footprint on heavy non-native EC circuits). Returns the
/// dense slots (`slots[id]`); `vars` need only contain the inputs (the ops
/// produce everything else); `n` presizes.
pub(crate) fn solve_witness_streamed_dense(
    vars: &[crate::primitive::Var],
    n: usize,
    modulus: &BigUint,
    inputs: &BTreeMap<VarId, String>,
    feed: impl FnOnce(&mut dyn FnMut(WitnessGen)),
) -> Result<Vec<Option<Fp>>, SolveError> {
    use crate::primitive::VarRole;
    let mut assign = DenseAssign::with_len(n);
    // Seed inputs (identical to `solve_witness`); the hint ops read but never
    // produce them.
    for var in vars {
        if matches!(var.role, VarRole::PublicInput | VarRole::PrivateInput) {
            let decimal = inputs
                .get(&var.id)
                .ok_or(SolveError::MissingInput(var.id))?;
            assign.set(var.id, Fp::from_decimal(decimal, modulus));
        }
    }
    // Op-count cap: keeps peak batch memory bounded regardless of circuit size.
    // ~10^5 ops is a few hundred MB even for wide non-native limbs, vs multi-GB
    // for the whole program.
    const BATCH: usize = 100_000;
    // Batches run sequentially: the ops arrive from a single-threaded expansion,
    // and level-parallel execution measured slower than sequential on every
    // example circuit (Ed25519 0.78 s vs 0.66 s, SHA-256 and Merkle no gain) —
    // the DAG is deep and narrow, so building levels costs more than it returns.
    let mut batch: Vec<WitnessGen> = Vec::with_capacity(BATCH);
    let mut err: Option<SolveError> = None;
    {
        let mut sink = |op: WitnessGen| {
            if err.is_some() {
                return;
            }
            batch.push(op);
            if batch.len() >= BATCH {
                if let Err(e) = solve_witness_sequential(&batch, modulus, &mut assign) {
                    err = Some(e);
                }
                batch.clear();
            }
        };
        feed(&mut sink);
    }
    if let Some(e) = err {
        return Err(e);
    }
    if !batch.is_empty() {
        solve_witness_sequential(&batch, modulus, &mut assign)?;
    }
    Ok(assign.slots)
}

/// `a⁻¹ mod m` by safegcd at a fixed 256 bits, for an odd `m` that fits; the
/// same value as the Fermat inverse when `m` is prime, at a fraction of the cost.
fn inverse_256(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    use crypto_bigint::{Odd, U256};
    let words = |x: &BigUint| {
        let d = x.to_u64_digits();
        (d.len() <= 4).then(|| {
            let mut w = [0u64; 4];
            w[..d.len()].copy_from_slice(&d);
            U256::from_words(w)
        })
    };
    let m = Option::from(Odd::new(words(m)?))?;
    let inv: U256 = Option::from(words(a)?.invert_odd_mod(&m))?;
    let bytes: Vec<u8> = inv
        .to_words()
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
    Some(BigUint::from_bytes_le(&bytes))
}

/// Execute one witness-gen op, reading each input LC's value through `eval_lc`
/// and reporting each output via `emit`. Pure over its inputs, so independent
/// ops run concurrently.
pub(crate) fn exec_witness_op<L, V: Copy>(
    op: &WitnessGen<L, V>,
    eval_lc: impl Fn(&L) -> Fp,
    modulus: &BigUint,
    emit: &mut impl FnMut(V, Fp),
) -> Result<(), SolveError> {
    match op {
        WitnessGen::Product { out, left, right } => {
            let l = eval_lc(left);
            let r = eval_lc(right);
            emit(*out, l.mul(&r));
        }
        WitnessGen::Linear { out, lc } => {
            let v = eval_lc(lc);
            emit(*out, v);
        }
        WitnessGen::Xor { out, a, b } => {
            let av = eval_lc(a);
            let bv = eval_lc(b);
            let ab = av.mul(&bv);
            // a + b - 2ab
            let v = av.add(&bv).sub(&ab.add(&ab));
            emit(*out, v);
        }
        WitnessGen::Or { out, a, b } => {
            let av = eval_lc(a);
            let bv = eval_lc(b);
            let ab = av.mul(&bv);
            // a + b - ab
            let v = av.add(&bv).sub(&ab);
            emit(*out, v);
        }
        WitnessGen::Inverse { out, input } => {
            let v = eval_lc(input);
            // Inverse-or-zero: 0 maps to 0 (the is_zero convention).
            let inv = v.inverse().unwrap_or_else(|| Fp::zero(modulus));
            emit(*out, inv);
        }
        WitnessGen::InverseOrZero { out, input } => {
            // `x⁻¹` when `x ≠ 0`, else `0` (unconstrained at 0)
            let v = eval_lc(input);
            let inv = v.inverse().unwrap_or_else(|| Fp::zero(modulus));
            emit(*out, inv);
        }
        WitnessGen::Bit { out, input, index } => {
            let v = eval_lc(input);
            emit(*out, v.bits()(*index as usize));
        }
        WitnessGen::Bits { outs, input } => {
            // Batched form of `Bit`: `outs[i]` is bit `i` of the input.
            let v = eval_lc(input);
            let bit = v.bits();
            for (i, out) in outs.iter().enumerate() {
                emit(*out, bit(i));
            }
        }
        WitnessGen::DivRem { q, r, num, den } => {
            let n = eval_lc(num);
            let d = eval_lc(den);
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
            let recompose = |limbs: &[L]| -> BigUint {
                let mut acc = BigUint::zero();
                for (i, lc) in limbs.iter().enumerate() {
                    let v = eval_lc(lc).to_biguint();
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
            let recompose = |limbs: &[L]| -> BigUint {
                let mut acc = BigUint::zero();
                for (i, lc) in limbs.iter().enumerate() {
                    let v = eval_lc(lc).to_biguint();
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
            // The inverse of A mod M (M prime — holds for the fields this hint
            // targets): safegcd when M fits 256 bits, else Fermat's A^(M-2).
            let w = inverse_256(&a_big, &m_big)
                .unwrap_or_else(|| a_big.modpow(&(&m_big - BigUint::from(2u32)), &m_big));
            let mask = (BigUint::one() << *limb_bits as usize) - BigUint::one();
            for (i, &o) in out.iter().enumerate() {
                let limb = (&w >> (*limb_bits as usize * i)) & &mask;
                emit(o, Fp::new(limb, modulus));
            }
        }
        WitnessGen::FakeGlv {
            out,
            u,
            modulus: m,
            lambda,
            limb_bits,
        } => {
            if *limb_bits > MAX_LIMB_BITS || out.len() != 4 {
                return Err(SolveError::MalformedHint(
                    "fake_glv: limb_bits or output count",
                ));
            }
            let recompose = |limbs: &[L]| -> BigUint {
                let mut acc = BigUint::zero();
                for (i, lc) in limbs.iter().enumerate() {
                    let v = eval_lc(lc).to_biguint();
                    acc += v << (*limb_bits as usize * i);
                }
                acc
            };
            let v = fake_glv(&recompose(u), &recompose(m), &recompose(lambda)).ok_or(
                SolveError::MalformedHint("fake_glv: no short lattice vector"),
            )?;
            for (o, x) in out.iter().zip(&v) {
                emit(*o, Fp::from_bigint(x, modulus));
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
            let recompose = |limbs: &[L]| -> BigUint {
                let mut acc = BigUint::zero();
                for (i, lc) in limbs.iter().enumerate() {
                    let v = eval_lc(lc).to_biguint();
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

/// Run ops one at a time in their (topological) order.
fn solve_witness_sequential(
    witness_gen: &[WitnessGen],
    modulus: &BigUint,
    assign: &mut DenseAssign,
) -> Result<(), SolveError> {
    // Scratch buffer so the op reads the shared assignment without `emit`
    // aliasing it, then apply the outputs.
    let mut outs: Vec<(VarId, Fp)> = Vec::new();
    for op in witness_gen {
        outs.clear();
        exec_witness_op(
            op,
            |lc| eval_lc(lc, assign, modulus),
            modulus,
            &mut |v, val| outs.push((v, val)),
        )?;
        for (v, val) in outs.drain(..) {
            assign.set(v, val);
        }
    }
    Ok(())
}

/// Solve the witness in parallel via the op DAG: same-level ops (none reading
/// another's output) are independent, so each wide level runs across rayon. Ops
/// are emitted in topological order, so one forward pass assigns levels. Produces
/// the identical assignment to the sequential path — every var is written by
/// exactly one op, and a level never reads a same-level output.
///
/// Deep, narrow DAGs (non-native EC arithmetic) have many levels a few ops wide,
/// where a rayon barrier per level costs more than the work; those levels run
/// inline. With one thread (wasm32, or a single-thread pool) the level analysis
/// is skipped entirely.
fn solve_witness_parallel(
    witness_gen: &[WitnessGen],
    modulus: &BigUint,
    assign: &mut DenseAssign,
) -> Result<(), SolveError> {
    use rayon::prelude::*;
    /// Levels narrower than this run inline (no barrier).
    const PAR_LEVEL: usize = 256;
    if cfg!(target_arch = "wasm32") || rayon::current_num_threads() <= 1 {
        return solve_witness_sequential(witness_gen, modulus, assign);
    }
    // Level of the op producing each var written in this batch.
    let mut produced_at: std::collections::HashMap<VarId, u32> =
        std::collections::HashMap::with_capacity(witness_gen.len() * 2);
    let mut level = vec![0u32; witness_gen.len()];
    let mut max_level = 0u32;
    for (idx, op) in witness_gen.iter().enumerate() {
        let mut lv = 0u32;
        op_read_vars(op, |rv| {
            if let Some(&p) = produced_at.get(&rv) {
                lv = lv.max(p + 1);
            }
        });
        level[idx] = lv;
        max_level = max_level.max(lv);
        op_output_vars(op, |o| {
            produced_at.insert(o, lv);
        });
    }
    drop(produced_at);
    let mut levels: Vec<Vec<usize>> = vec![Vec::new(); max_level as usize + 1];
    for (idx, &lv) in level.iter().enumerate() {
        levels[lv as usize].push(idx);
    }
    let mut outs: Vec<(VarId, Fp)> = Vec::new();
    for level_ops in &levels {
        if level_ops.len() < PAR_LEVEL {
            for &idx in level_ops {
                outs.clear();
                exec_witness_op(
                    &witness_gen[idx],
                    |lc| eval_lc(lc, assign, modulus),
                    modulus,
                    &mut |v, val| outs.push((v, val)),
                )?;
                for (v, val) in outs.drain(..) {
                    assign.set(v, val);
                }
            }
            continue;
        }
        let snapshot: &DenseAssign = assign;
        let produced: Vec<Vec<(VarId, Fp)>> = level_ops
            .par_chunks(64)
            .map(|chunk| {
                let mut out = Vec::new();
                for &idx in chunk {
                    exec_witness_op(
                        &witness_gen[idx],
                        |lc| eval_lc(lc, snapshot, modulus),
                        modulus,
                        &mut |v, val| out.push((v, val)),
                    )?;
                }
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
        WitnessGen::ModInverse { out, .. } | WitnessGen::FakeGlv { out, .. } => {
            out.iter().for_each(|o| f(*o))
        }
        WitnessGen::Sub2 { qabs, r, .. } => {
            f(*qabs);
            r.iter().for_each(|o| f(*o));
        }
    }
}

/// Visit each input `VarId` a witness-gen op reads.
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
        WitnessGen::FakeGlv {
            u, modulus, lambda, ..
        } => {
            each(u, &mut f);
            each(modulus, &mut f);
            each(lambda, &mut f);
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

/// Construct a field element from a decimal string against a program's field.
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

/// [`solve_and_check`], recording the inputs and outcome when
/// `XARK_DUMP_INPUTS=<dir>` is set: one JSON file per call, `{"circuit",
/// "inputs": [[leaf, decimal]…], "ok"}` — a corpus of real test inputs for
/// differential testing and witness search over two builds of the same circuit
/// (`crates/frontend/examples/difftest.rs`, `cargo xtask difftest`).
/// Every circuit test should solve through this (directly, or via
/// `xark_prover::Circuit`) so its inputs are checked too.
pub fn solve_and_check_recorded(
    circuit: &str,
    program: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>, SolveError> {
    let r = solve_and_check(program, inputs);
    if let Some(dir) = std::env::var_os("XARK_DUMP_INPUTS") {
        let names: BTreeMap<VarId, &str> = program
            .vars
            .iter()
            .map(|v| (v.id, v.name.as_str()))
            .collect();
        // Leaf names are paths like `a[0].x` and values decimals: `{:?}` quotes
        // them as JSON strings.
        let leaves: Vec<String> = inputs
            .iter()
            .map(|(id, val)| format!("[{:?},{val:?}]", names.get(id).copied().unwrap_or("")))
            .collect();
        let text = format!(
            "{{\"circuit\":{circuit:?},\"inputs\":[{}],\"ok\":{}}}",
            leaves.join(","),
            r.is_ok()
        );
        let mut h = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(&text, &mut h);
        let dir = std::path::Path::new(&dir);
        let _ = std::fs::create_dir_all(dir);
        let file = dir.join(format!(
            "{circuit}-{:016x}.json",
            std::hash::Hasher::finish(&h)
        ));
        let _ = std::fs::write(file, text);
    }
    r
}

/// `a·b == c` for one R1CS row against a solved assignment — the streaming
/// check's per-row test (reuses [`eval_lc`]). Never holds more than one row.
pub(crate) fn row_satisfied(
    a: &LinearCombination,
    b: &LinearCombination,
    c: &LinearCombination,
    assign: &(impl Assignment + ?Sized),
    modulus: &BigUint,
) -> bool {
    eval_lc(a, assign, modulus).mul(&eval_lc(b, assign, modulus)) == eval_lc(c, assign, modulus)
}

// Under-constraint (soundness smoke-test) analyzer.

/// A derived variable the analyzer could not prove is uniquely pinned by the
/// constraints (holding every other variable at the honest witness) — a potential
/// under-constraint a malicious prover might change without violating a constraint.
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
        let coeff = Fp::from_const(&mt.coeff, modulus);
        match (mt.left == v, mt.right == v) {
            (true, true) => a = a.add(&coeff),
            (true, false) => b = b.add(&coeff.mul(&get(mt.right))),
            (false, true) => b = b.add(&coeff.mul(&get(mt.left))),
            (false, false) => c = c.add(&coeff.mul(&get(mt.left)).mul(&get(mt.right))),
        }
    }
    for lt in &expr.linear_terms {
        let coeff = Fp::from_const(&lt.coeff, modulus);
        if lt.var == v {
            b = b.add(&coeff);
        } else {
            c = c.add(&coeff.mul(&get(lt.var)));
        }
    }
    c = c.add(&Fp::from_const(&expr.constant, modulus));
    (a, b, c)
}

/// Check every `Derived` variable is uniquely determined by the constraints,
/// given the honest witness `assign` (which must satisfy the program).
///
/// A *necessary* soundness check, not a full proof: it catches free/two-valued
/// variables (the dominant under-constraint bug class) by testing, per variable,
/// whether any value other than the honest one also satisfies every referencing
/// constraint (all others fixed). A variable pinned by a linear constraint is
/// unique; one pinned only by quadratics is checked against their second roots
/// (Vieta).
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

    // Each Derived var's analysis is independent (read-only shared state).
    // `filter_map().collect()` preserves order, keeping the result deterministic.
    use rayon::prelude::*;
    program
        .vars
        .par_iter()
        .filter_map(|var| {
            if !matches!(var.role, VarRole::Derived) {
                return None;
            }
            let v = var.id;
            let alpha = assign
                .get(&v)
                .cloned()
                .unwrap_or_else(|| Fp::zero(&modulus));
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
                let (a, b, _c) = univariate(&program.constraints[ci], v, assign, &modulus);
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
                    reason: "variable's coefficient is zero in every referencing constraint (free)"
                        .into(),
                });
            }
            for beta in &candidates {
                if *beta == alpha {
                    continue;
                }
                let satisfies_all = cons.iter().all(|&ci| {
                    let (a, b, c) = univariate(&program.constraints[ci], v, assign, &modulus);
                    a.mul(beta).mul(beta).add(&b.mul(beta)).add(&c).is_zero()
                });
                if satisfies_all {
                    return Some(UnderConstrained {
                        var: v,
                        name: var.name.clone(),
                        reason: "a different value also satisfies all its constraints (two-valued)"
                            .into(),
                    });
                }
            }
            None
        })
        .collect()
}

// CircuitProgram entry points — operate on R1CS rows (`a·b = c`) directly,
// avoiding the `to_primitive` flattening, so a loaded `circuit.xbc` is never
// materialized into `Expression`s. Equivalence with the `Expression`-based path
// is asserted in the tests below.

/// Run the witness-generation program of a [`CircuitProgram`](crate::circuit::CircuitProgram).
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

/// Reduce an R1CS row `a·b − c` to the univariate `A·v² + B·v + C` obtained by
/// fixing every variable except `v`. Splitting each of `a`, `b`, `c` into its
/// `v`-coefficient and the rest gives, for `a = aᵥ·v + a₀` etc.:
/// `A = aᵥ·bᵥ`, `B = aᵥ·b₀ + a₀·bᵥ − cᵥ`, `C = a₀·b₀ − c₀`.
pub(crate) fn univariate_r1cs(
    row: &crate::circuit::R1csRow,
    v: VarId,
    assign: &BTreeMap<VarId, Fp>,
    modulus: &BigUint,
) -> (Fp, Fp, Fp) {
    let split = |lc: &LinearCombination| -> (Fp, Fp) {
        let mut coeff_v = Fp::zero(modulus);
        let mut rest = Fp::from_const(&lc.constant, modulus);
        for t in &lc.terms {
            let coeff = Fp::from_const(&t.coeff, modulus);
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

/// [`univariate_r1cs`] for every distinct variable of `row`, in ascending var
/// order, from one evaluation of `a`, `b`, `c`: each var's rest is the full value
/// minus its own share (`a₀ = a − aᵥ·xᵥ`, likewise `b₀`, `c₀`), which is the same
/// field element, so a row costs O(width) instead of O(width²).
pub(crate) fn univariate_r1cs_row(
    row: &crate::circuit::R1csRow,
    assign: &(impl Assignment + ?Sized),
    modulus: &BigUint,
) -> Vec<(VarId, (Fp, Fp, Fp))> {
    let zero = Fp::zero(modulus);
    let zeros = || std::array::from_fn::<Fp, 3, _>(|_| zero.clone());
    let mut full = zeros();
    let mut coeffs: BTreeMap<VarId, [Fp; 3]> = BTreeMap::new();
    for (i, lc) in [&row.a, &row.b, &row.c].into_iter().enumerate() {
        full[i] = Fp::from_const(&lc.constant, modulus);
        for t in &lc.terms {
            let coeff = Fp::from_const(&t.coeff, modulus);
            full[i] = full[i].add(&coeff.mul(assign.get_fp(t.var).unwrap_or(&zero)));
            let own = &mut coeffs.entry(t.var).or_insert_with(zeros)[i];
            *own = own.add(&coeff);
        }
    }
    coeffs
        .into_iter()
        .map(|(v, [av, bv, cv])| {
            let x = assign.get_fp(v).unwrap_or(&zero);
            let a0 = full[0].sub(&av.mul(x));
            let b0 = full[1].sub(&bv.mul(x));
            let c0 = full[2].sub(&cv.mul(x));
            let a = av.mul(&bv);
            let b = av.mul(&b0).add(&a0.mul(&bv)).sub(&cv);
            (v, (a, b, a0.mul(&b0).sub(&c0)))
        })
        .collect()
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

    // Each derived variable's verdict is independent (reads only shared immutable
    // state); `collect` preserves source order, keeping the output deterministic.
    program
        .vars
        .par_iter()
        .filter(|var| matches!(var.role, VarRole::Derived))
        .filter_map(|var| check_one_var_cp(var, &refs, &program.constraints, assign, &modulus))
        .collect()
}

/// The per-variable under-constraint verdict (`None` = uniquely pinned). Pure
/// over shared immutable inputs, so it runs in parallel.
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

    /// The `CircuitProgram` (R1CS-row) path must agree exactly with the
    /// `PrimitiveProgram` (Expression) path — same witness, constraint verdict,
    /// and under-constraint verdicts. Covers a sound mul-gate, a dangling advice
    /// var (free path), and a booleanity-only bit (two-valued quadratic path).
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
    /// A level-ordering bug or lost write would give the wrong `u_i`.
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

    /// The 256-bit inverse is the Fermat inverse for the primes the hint targets,
    /// and declines what it can't do so the caller falls back.
    #[test]
    fn inverse_256_is_the_fermat_inverse() {
        let one = BigUint::one();
        let ed = (&one << 255u32) - 19u32;
        let k1 = (&one << 256u32) - (&one << 32u32) - 977u32;
        for m in [&ed, &k1] {
            let fermat = |a: &BigUint| a.modpow(&(m - 2u32), m);
            let mut a = BigUint::from(0x1234_5678_9abc_def0u64);
            for _ in 0..64 {
                a = (&a * &a + 7u32) % m;
                assert_eq!(inverse_256(&a, m), Some(fermat(&a)), "{a} mod {m}");
            }
            assert_eq!(inverse_256(&(m - 1u32), m), Some(fermat(&(m - 1u32))));
            assert_eq!(inverse_256(&one, m), Some(one.clone()));
        }
        // Even or wider than 256 bits: no answer, so the caller uses Fermat.
        assert_eq!(
            inverse_256(&BigUint::from(3u32), &BigUint::from(10u32)),
            None
        );
        assert_eq!(
            inverse_256(&BigUint::from(3u32), &((&one << 256u32) + 1u32)),
            None
        );
        // No inverse (a shares a factor with m).
        assert_eq!(
            inverse_256(&BigUint::from(3u32), &BigUint::from(9u32)),
            None
        );
    }
}
