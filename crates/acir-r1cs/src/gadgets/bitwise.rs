//! 32-bit word abstraction and bitwise operations on it.
//!
//! Every [`Word32`] is held as 32 bit-LCs (LSB first). Each LC's value at
//! proving time is 0 or 1. The optional `value: Option<u32>` is the concrete
//! word the prover sees; it's `None` during setup and propagated through
//! every operation in proving mode.
//!
//! Operations:
//!
//! | op        | constraints / 32-bit word                                          |
//! |-----------|--------------------------------------------------------------------|
//! | `rotr`    | 0 (pure index permutation)                                         |
//! | `shr`     | 0 (top `k` bits become the zero LC)                                |
//! | `not`     | 0 (per-bit `1 - x` LC)                                             |
//! | `and`     | 32 (`a_i * b_i = out_i`, output implicitly boolean)                |
//! | `xor`     | 32 (`(2 a_i) * b_i = aux_i`, plus output LC `a + b - aux`)         |
//! | `add_mod` | 32 (boolean bits) + 1 small linear (recompose), per call            |
//!
//! For widths other than 32 (e.g. `u8`, `u16`, `u64`), see [`WordN`] and
//! [`and_n`] / [`xor_n`]. These mirror the 32-bit primitives but parameterise
//! the bit width. Used by `BlackBoxFuncCall::{AND, XOR}` for Noir integer
//! types of arbitrary width up to 64. See ROADMAP step **WS-B.1** for the
//! design.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_relations::r1cs::{LinearCombination, SynthesisError, Variable};

use crate::gadgets::boolean::enforce_boolean;
use crate::gadgets::range::{decompose_into_bits, enforce_recompose_equals, pow2};
use crate::r1cs_builder::R1csBuilder;

/// A 32-bit word represented as 32 bit-LCs (LSB first) plus an optional
/// proving-time concrete value.
#[derive(Clone)]
pub struct Word32 {
    pub bits: Vec<LinearCombination<Fr>>, // length 32, LSB first
    pub value: Option<u32>,
}

impl Word32 {
    pub fn from_bits(bits: Vec<LinearCombination<Fr>>, value: Option<u32>) -> Self {
        debug_assert_eq!(bits.len(), 32);
        Self { bits, value }
    }

    /// Build a constant 32-bit word with all bits as constant LCs.
    pub fn constant(value: u32) -> Self {
        let mut bits = Vec::with_capacity(32);
        for i in 0..32 {
            let bit_val = (value >> i) & 1;
            let lc = if bit_val == 1 {
                LinearCombination(vec![(Fr::one(), Variable::One)])
            } else {
                LinearCombination(vec![])
            };
            bits.push(lc);
        }
        Self {
            bits,
            value: Some(value),
        }
    }

    /// Build a `Word32` from a single value-variable + its bit decomposition
    /// (each bit a single Variable, output of [`crate::gadgets::range::decompose_into_bits`]).
    pub fn from_decomposed(bit_vars: Vec<Variable>, value: Option<u32>) -> Self {
        debug_assert_eq!(bit_vars.len(), 32);
        let bits = bit_vars
            .into_iter()
            .map(|v| LinearCombination(vec![(Fr::one(), v)]))
            .collect();
        Self { bits, value }
    }
}

// ---- index/pure transformations --------------------------------------------

/// Right rotation: `out_i = a_{(i + k) mod 32}`.
pub fn rotr(a: &Word32, k: usize) -> Word32 {
    let k = k % 32;
    let bits = (0..32).map(|i| a.bits[(i + k) % 32].clone()).collect();
    let value = a.value.map(|v| v.rotate_right(k as u32));
    Word32::from_bits(bits, value)
}

/// Right shift: top `k` bits become zero, low bits drop off.
/// `out_i = a_{i + k}` if `i + k < 32`, else `0`.
pub fn shr(a: &Word32, k: usize) -> Word32 {
    let bits = (0..32)
        .map(|i| {
            if i + k < 32 {
                a.bits[i + k].clone()
            } else {
                LinearCombination(vec![])
            }
        })
        .collect();
    let value = a.value.map(|v| v >> k);
    Word32::from_bits(bits, value)
}

/// Bitwise NOT: `out_i = 1 - a_i`.
pub fn not(a: &Word32) -> Word32 {
    let bits = a
        .bits
        .iter()
        .map(|bit| {
            // (1, ONE) plus (-1)*bit
            let mut terms: Vec<(Fr, Variable)> = Vec::with_capacity(bit.0.len() + 1);
            terms.push((Fr::one(), Variable::One));
            for (c, v) in bit.0.iter() {
                terms.push((-*c, *v));
            }
            LinearCombination(terms)
        })
        .collect();
    let value = a.value.map(|v| !v);
    Word32::from_bits(bits, value)
}

// ---- AND / XOR --------------------------------------------------------------

/// Bitwise AND: for each bit, allocate `out_i` with `a_i * b_i = out_i`. `out_i`
/// is implicitly boolean if `a_i`, `b_i` are.
pub fn and(
    builder: &mut R1csBuilder<'_>,
    a: &Word32,
    b: &Word32,
) -> Result<Word32, SynthesisError> {
    let out_value = match (a.value, b.value) {
        (Some(av), Some(bv)) => Some(av & bv),
        _ => None,
    };
    let mut out_bits = Vec::with_capacity(32);
    for i in 0..32 {
        let av = a.value.map(|v| ((v >> i) & 1) as u8);
        let bv = b.value.map(|v| ((v >> i) & 1) as u8);
        let bit_value = match (av, bv) {
            (Some(x), Some(y)) => Some(if (x & y) == 1 { Fr::one() } else { Fr::zero() }),
            _ => None,
        };
        let out_var = builder.alloc_with_value(bit_value)?;
        builder.enforce(
            a.bits[i].clone(),
            b.bits[i].clone(),
            LinearCombination(vec![(Fr::one(), out_var)]),
        )?;
        out_bits.push(LinearCombination(vec![(Fr::one(), out_var)]));
    }
    Ok(Word32::from_bits(out_bits, out_value))
}

/// Bitwise XOR via `out = a + b - 2*a*b` (so `aux = a * b * 2`, and we materialise
/// `out` as a fresh boolean variable so its bits stay "1 LC-term" for cheap
/// downstream composition).
pub fn xor(
    builder: &mut R1csBuilder<'_>,
    a: &Word32,
    b: &Word32,
) -> Result<Word32, SynthesisError> {
    let two = Fr::one() + Fr::one();
    let out_value = match (a.value, b.value) {
        (Some(av), Some(bv)) => Some(av ^ bv),
        _ => None,
    };
    let mut out_bits = Vec::with_capacity(32);
    for i in 0..32 {
        let av = a.value.map(|v| ((v >> i) & 1) as u8);
        let bv = b.value.map(|v| ((v >> i) & 1) as u8);
        let out_bit_val = match (av, bv) {
            (Some(x), Some(y)) => Some(if (x ^ y) == 1 { Fr::one() } else { Fr::zero() }),
            _ => None,
        };
        let out_var = builder.alloc_with_value(out_bit_val)?;
        enforce_boolean(builder, out_var)?;

        // Enforce `(2*a) * b = (a + b - out)`.
        // Build the `2*a` LC and the `a + b - out` LC.
        let mut two_a: Vec<(Fr, Variable)> = Vec::with_capacity(a.bits[i].0.len());
        for (c, v) in a.bits[i].0.iter() {
            two_a.push((*c * two, *v));
        }
        let mut sum_lc: Vec<(Fr, Variable)> =
            Vec::with_capacity(a.bits[i].0.len() + b.bits[i].0.len() + 1);
        for (c, v) in a.bits[i].0.iter() {
            sum_lc.push((*c, *v));
        }
        for (c, v) in b.bits[i].0.iter() {
            sum_lc.push((*c, *v));
        }
        sum_lc.push((-Fr::one(), out_var));

        builder.enforce(
            LinearCombination(two_a),
            b.bits[i].clone(),
            LinearCombination(sum_lc),
        )?;

        out_bits.push(LinearCombination(vec![(Fr::one(), out_var)]));
    }
    Ok(Word32::from_bits(out_bits, out_value))
}

// ---- Addition mod 2^32 ------------------------------------------------------

/// Add up to a handful of `Word32`s as integers, allocate the 32-bit result and
/// a small carry decomposition, and enforce `sum_of_inputs = result + 2^32 * carry`.
/// Returns the result word.
///
/// Requires at most `MAX_TERMS` inputs (so the carry fits in `CARRY_BITS`).
pub fn add_mod_32(
    builder: &mut R1csBuilder<'_>,
    terms: &[&Word32],
) -> Result<Word32, SynthesisError> {
    // Up to 8 terms supported (carry < 2^32 * 8 = 2^35, so 3 carry bits).
    const MAX_TERMS: usize = 8;
    assert!(!terms.is_empty(), "add_mod_32 needs at least one term");
    assert!(
        terms.len() <= MAX_TERMS,
        "add_mod_32: too many terms ({} > {MAX_TERMS})",
        terms.len()
    );
    let carry_bits = log2_ceil(terms.len().max(1));

    // Concrete sum (proving time).
    let known: Option<u64> = terms
        .iter()
        .try_fold(0u64, |acc, w| w.value.map(|v| acc + v as u64));
    let (result_value, carry_value) = if let Some(s) = known {
        (Some(s as u32), Some((s >> 32) as u32))
    } else {
        (None, None)
    };

    // Allocate 32 result bits + carry_bits carry bits, all boolean.
    let mut result_bit_vars = Vec::with_capacity(32);
    for i in 0..32 {
        let bv = result_value.map(|v| {
            if ((v >> i) & 1) == 1 {
                Fr::one()
            } else {
                Fr::zero()
            }
        });
        let var = builder.alloc_with_value(bv)?;
        enforce_boolean(builder, var)?;
        result_bit_vars.push(var);
    }
    let mut carry_bit_vars = Vec::with_capacity(carry_bits);
    for j in 0..carry_bits {
        let bv = carry_value.map(|v| {
            if ((v >> j) & 1) == 1 {
                Fr::one()
            } else {
                Fr::zero()
            }
        });
        let var = builder.alloc_with_value(bv)?;
        enforce_boolean(builder, var)?;
        carry_bit_vars.push(var);
    }

    // Build `sum_of_inputs - result_value - 2^32 * carry_value = 0` as one
    // linear constraint.
    let mut lc: Vec<(Fr, Variable)> = Vec::new();
    for w in terms {
        for (i, bit) in w.bits.iter().enumerate() {
            let coeff = pow2(i);
            for (c, v) in bit.0.iter() {
                lc.push((*c * coeff, *v));
            }
        }
    }
    for (i, var) in result_bit_vars.iter().enumerate() {
        lc.push((-pow2(i), *var));
    }
    for (j, var) in carry_bit_vars.iter().enumerate() {
        lc.push((-pow2(32 + j), *var));
    }
    builder.enforce(builder.zero_lc(), builder.zero_lc(), LinearCombination(lc))?;

    Ok(Word32::from_decomposed(result_bit_vars, result_value))
}

fn log2_ceil(n: usize) -> usize {
    if n <= 1 {
        return 0;
    }
    (usize::BITS - (n - 1).leading_zeros()) as usize
}

// ============================================================================
// WordN: arbitrary-width bitwise gadget (1..=64 bits).
// ============================================================================

/// Maximum bit width accepted by [`WordN`] / [`and_n`] / [`xor_n`].
///
/// Noir's `BlackBoxFuncCall::{AND, XOR}` carry a `num_bits: u32` width.
/// Per ROADMAP step **WS-B.1**, we cap at 64 bits — wider integer types are
/// not part of Noir's surface for these opcodes.
pub const WORDN_MAX_BITS: usize = 64;

/// An `N`-bit word represented as `N` bit-LCs (LSB first) plus an optional
/// proving-time concrete value (stored as `u64`).
///
/// Used for the variable-width path that backs `BlackBoxFuncCall::{AND, XOR}`.
/// See ROADMAP step **WS-B.1** for context. For the fixed 32-bit path used by
/// SHA-256, see [`Word32`].
#[derive(Clone)]
pub struct WordN {
    pub bits: Vec<LinearCombination<Fr>>, // length == num_bits, LSB first
    pub num_bits: usize,
    pub value: Option<u64>,
}

impl WordN {
    /// Build a `WordN` from a pre-computed list of bit-LCs plus the bit width.
    pub fn from_bits(
        bits: Vec<LinearCombination<Fr>>,
        num_bits: usize,
        value: Option<u64>,
    ) -> Self {
        debug_assert_eq!(bits.len(), num_bits);
        Self {
            bits,
            num_bits,
            value,
        }
    }

    /// Build a `WordN` by allocating + range-decomposing `value_var` into
    /// `num_bits` boolean witness variables (LSB first).
    ///
    /// Each bit is implicitly range-constrained to `{0, 1}` by
    /// [`decompose_into_bits`], and `sum_i 2^i * bits[i] = value_var` is
    /// enforced as a single linear constraint.
    pub fn from_value_var(
        builder: &mut R1csBuilder<'_>,
        value_var: Variable,
        num_bits: usize,
        value: Option<Fr>,
    ) -> Result<Self, SynthesisError> {
        assert!(
            (1..=WORDN_MAX_BITS).contains(&num_bits),
            "WordN width {num_bits} out of range; see ROADMAP step WS-B.1 \
             ({WORDN_MAX_BITS}-bit cap on BlackBoxFuncCall::AND/XOR)"
        );
        let bit_vars = decompose_into_bits(builder, value_var, num_bits, value)?;
        let u64_value = value.map(fr_to_u64_low);
        let bits = bit_vars
            .into_iter()
            .map(|v| LinearCombination(vec![(Fr::one(), v)]))
            .collect();
        Ok(Self {
            bits,
            num_bits,
            value: u64_value,
        })
    }

    /// Bind this word's bit decomposition to an output `Variable` via
    /// [`enforce_recompose_equals`]: `sum_i 2^i * bits[i] = out_var`.
    pub fn bind_to_var(
        &self,
        builder: &R1csBuilder<'_>,
        out_var: Variable,
    ) -> Result<(), SynthesisError> {
        enforce_recompose_equals(builder, &self.bits, out_var)
    }
}

/// Bitwise AND on two `num_bits`-wide words. Mirrors [`and`] but with a
/// variable bit width.
///
/// Each bit costs one R1CS constraint: `a_i * b_i = out_i`. `out_i` is
/// implicitly boolean whenever the inputs are.
pub fn and_n(builder: &mut R1csBuilder<'_>, a: &WordN, b: &WordN) -> Result<WordN, SynthesisError> {
    assert_eq!(
        a.num_bits, b.num_bits,
        "and_n: width mismatch ({} vs {})",
        a.num_bits, b.num_bits
    );
    let num_bits = a.num_bits;
    assert!(
        (1..=WORDN_MAX_BITS).contains(&num_bits),
        "and_n: width {num_bits} out of range; see ROADMAP step WS-B.1"
    );

    let out_value = match (a.value, b.value) {
        (Some(av), Some(bv)) => Some(av & bv),
        _ => None,
    };
    let mut out_bits = Vec::with_capacity(num_bits);
    for i in 0..num_bits {
        let av = a.value.map(|v| ((v >> i) & 1) as u8);
        let bv = b.value.map(|v| ((v >> i) & 1) as u8);
        let bit_value = match (av, bv) {
            (Some(x), Some(y)) => Some(if (x & y) == 1 { Fr::one() } else { Fr::zero() }),
            _ => None,
        };
        let out_var = builder.alloc_with_value(bit_value)?;
        builder.enforce(
            a.bits[i].clone(),
            b.bits[i].clone(),
            LinearCombination(vec![(Fr::one(), out_var)]),
        )?;
        out_bits.push(LinearCombination(vec![(Fr::one(), out_var)]));
    }
    Ok(WordN::from_bits(out_bits, num_bits, out_value))
}

/// N-way bitwise XOR of arbitrary-width words (all the same width).
/// Computes `out_i = b1_i ⊕ b2_i ⊕ ... ⊕ bN_i` per bit position via the
/// parity identity `Σ_j bj_i = out_i + 2·k_i`, where `k_i ∈ [0, ⌊N/2⌋]`
/// is a small auxiliary carry. Cost per bit ≈ `1 boolean (out) + ceil(log2(⌊N/2⌋+1)) booleans (k) + 1 linear`.
///
/// Faster than a chain of `N − 1` binary [`xor_n`] calls when `N ≥ 3`. The
/// θ step of Keccak XORs 5 lane-bits per column; using this helper there
/// drops the column phase's bit cost from `~8 → ~5` constraints per
/// position, saving roughly 8% of total Keccak-f[1600] cost.
pub fn xor_n_inputs(
    builder: &mut R1csBuilder<'_>,
    inputs: &[&WordN],
) -> Result<WordN, SynthesisError> {
    assert!(inputs.len() >= 2, "xor_n_inputs requires at least 2 inputs");
    if inputs.len() == 2 {
        return xor_n(builder, inputs[0], inputs[1]);
    }
    let num_bits = inputs[0].num_bits;
    for w in inputs.iter().skip(1) {
        assert_eq!(
            w.num_bits, num_bits,
            "xor_n_inputs: width mismatch ({} vs {})",
            w.num_bits, num_bits
        );
    }
    let max_carry = inputs.len() / 2;
    let carry_bits = max(1, bit_width_for(max_carry));

    // Aggregate proving-time value: XOR all inputs together.
    let out_value: Option<u64> = inputs.iter().try_fold(0u64, |acc, w| w.value.map(|v| acc ^ v));

    let mut out_bits: Vec<LinearCombination<Fr>> = Vec::with_capacity(num_bits);
    for bit_i in 0..num_bits {
        // Sum the i-th input bits' values at proving time.
        let sum_val: Option<u64> = inputs.iter().try_fold(0u64, |acc, w| {
            w.value.map(|v| acc + ((v >> bit_i) & 1))
        });
        let out_bit_val = sum_val.map(|s| {
            if s & 1 == 1 {
                Fr::one()
            } else {
                Fr::zero()
            }
        });
        let out_var = builder.alloc_with_value(out_bit_val)?;
        enforce_boolean(builder, out_var)?;

        // Allocate carry k_i with `carry_bits` bits.
        let k_val = sum_val.map(|s| Fr::from(s >> 1));
        let k_var = builder.alloc_with_value(k_val)?;
        let _ = decompose_into_bits(builder, k_var, carry_bits, k_val)?;

        // Enforce Σ bj_i − out − 2·k = 0 as a single linear constraint
        // over each input's bit-LC plus the freshly allocated `out` and
        // `k`.
        let mut lc: Vec<(Fr, Variable)> = Vec::new();
        for w in inputs {
            for (c, v) in w.bits[bit_i].0.iter() {
                lc.push((*c, *v));
            }
        }
        lc.push((-Fr::one(), out_var));
        let two = Fr::one() + Fr::one();
        lc.push((-two, k_var));
        builder.enforce(builder.zero_lc(), builder.zero_lc(), LinearCombination(lc))?;

        out_bits.push(LinearCombination(vec![(Fr::one(), out_var)]));
    }
    Ok(WordN::from_bits(out_bits, num_bits, out_value))
}

/// Number of bits needed to represent any value in `[0, n]`. For `n = 0`
/// returns 1 (the minimum useful range-check width). Used by
/// [`xor_n_inputs`] to size the carry-bit decomposition.
fn bit_width_for(n: usize) -> usize {
    if n == 0 {
        1
    } else {
        (usize::BITS - n.leading_zeros()) as usize
    }
}

use std::cmp::max;

/// Bitwise XOR on two `num_bits`-wide words. Mirrors [`xor`] but with a
/// variable bit width.
///
/// Each bit costs one R1CS constraint + one boolean check on the freshly
/// materialised output bit (so it remains a single LC-term for cheap
/// downstream composition).
pub fn xor_n(builder: &mut R1csBuilder<'_>, a: &WordN, b: &WordN) -> Result<WordN, SynthesisError> {
    assert_eq!(
        a.num_bits, b.num_bits,
        "xor_n: width mismatch ({} vs {})",
        a.num_bits, b.num_bits
    );
    let num_bits = a.num_bits;
    assert!(
        (1..=WORDN_MAX_BITS).contains(&num_bits),
        "xor_n: width {num_bits} out of range; see ROADMAP step WS-B.1"
    );

    let two = Fr::one() + Fr::one();
    let out_value = match (a.value, b.value) {
        (Some(av), Some(bv)) => Some(av ^ bv),
        _ => None,
    };
    let mut out_bits = Vec::with_capacity(num_bits);
    for i in 0..num_bits {
        let av = a.value.map(|v| ((v >> i) & 1) as u8);
        let bv = b.value.map(|v| ((v >> i) & 1) as u8);
        let out_bit_val = match (av, bv) {
            (Some(x), Some(y)) => Some(if (x ^ y) == 1 { Fr::one() } else { Fr::zero() }),
            _ => None,
        };
        let out_var = builder.alloc_with_value(out_bit_val)?;
        enforce_boolean(builder, out_var)?;

        // Enforce `(2*a) * b = (a + b - out)`.
        let mut two_a: Vec<(Fr, Variable)> = Vec::with_capacity(a.bits[i].0.len());
        for (c, v) in a.bits[i].0.iter() {
            two_a.push((*c * two, *v));
        }
        let mut sum_lc: Vec<(Fr, Variable)> =
            Vec::with_capacity(a.bits[i].0.len() + b.bits[i].0.len() + 1);
        for (c, v) in a.bits[i].0.iter() {
            sum_lc.push((*c, *v));
        }
        for (c, v) in b.bits[i].0.iter() {
            sum_lc.push((*c, *v));
        }
        sum_lc.push((-Fr::one(), out_var));

        builder.enforce(
            LinearCombination(two_a),
            b.bits[i].clone(),
            LinearCombination(sum_lc),
        )?;
        out_bits.push(LinearCombination(vec![(Fr::one(), out_var)]));
    }
    Ok(WordN::from_bits(out_bits, num_bits, out_value))
}

/// Truncate an `Fr` to the low 64 bits as a `u64`. Used internally by
/// [`WordN::from_value_var`] when the value fits in `num_bits ≤ 64`.
fn fr_to_u64_low(fr: Fr) -> u64 {
    let bytes = crate::field::fr_to_be_bytes(&fr);
    let mut out = 0u64;
    for &b in &bytes[24..32] {
        out = (out << 8) | b as u64;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn alloc_constant_word(builder: &mut R1csBuilder<'_>, value: u32) -> Word32 {
        // Build 32 fresh boolean wires for the value; gives us a full-Variable Word32
        // that exercises both XOR/AND inputs realistically.
        let mut bits = Vec::with_capacity(32);
        for i in 0..32 {
            let bv = Some(if ((value >> i) & 1) == 1 {
                Fr::one()
            } else {
                Fr::zero()
            });
            let v = builder.alloc_with_value(bv).unwrap();
            enforce_boolean(builder, v).unwrap();
            bits.push(LinearCombination(vec![(Fr::one(), v)]));
        }
        Word32::from_bits(bits, Some(value))
    }

    fn run<F: FnOnce(&mut R1csBuilder<'_>)>(f: F) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut builder = R1csBuilder::new(cs.clone(), None);
        builder.finish_public_pass();
        // Re-make builder in proving mode by hand: we need witness map. Use a
        // trivial witness map below.
        drop(builder);
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();
        f(&mut b);
        cs.is_satisfied().unwrap()
    }

    #[test]
    fn xor_matches_native_random() {
        let mut rng = StdRng::seed_from_u64(0xCAFE_F00D);
        for _ in 0..10 {
            let a: u32 = rng.gen();
            let b: u32 = rng.gen();
            assert!(
                run(|builder| {
                    let aw = alloc_constant_word(builder, a);
                    let bw = alloc_constant_word(builder, b);
                    let out = xor(builder, &aw, &bw).unwrap();
                    assert_eq!(out.value, Some(a ^ b));
                }),
                "xor: a={a} b={b}"
            );
        }
    }

    #[test]
    fn and_matches_native_random() {
        let mut rng = StdRng::seed_from_u64(0xDEAD_BEEF);
        for _ in 0..10 {
            let a: u32 = rng.gen();
            let b: u32 = rng.gen();
            assert!(
                run(|builder| {
                    let aw = alloc_constant_word(builder, a);
                    let bw = alloc_constant_word(builder, b);
                    let out = and(builder, &aw, &bw).unwrap();
                    assert_eq!(out.value, Some(a & b));
                }),
                "and: a={a} b={b}"
            );
        }
    }

    #[test]
    fn not_rotr_shr_match_native() {
        let mut rng = StdRng::seed_from_u64(0x1234_5678);
        for _ in 0..10 {
            let a: u32 = rng.gen();
            let k = rng.gen_range(0..32);
            assert!(
                run(|builder| {
                    let aw = alloc_constant_word(builder, a);
                    let not_a = not(&aw);
                    assert_eq!(not_a.value, Some(!a));
                    let r = rotr(&aw, k);
                    assert_eq!(r.value, Some(a.rotate_right(k as u32)));
                    let s = shr(&aw, k);
                    assert_eq!(s.value, Some(a >> k));
                }),
                "not/rotr/shr: a={a} k={k}"
            );
        }
    }

    #[test]
    fn add_mod_32_matches_native() {
        let mut rng = StdRng::seed_from_u64(0xABCD_0001);
        for _ in 0..10 {
            let vals: Vec<u32> = (0..5).map(|_| rng.gen()).collect();
            let expect = vals.iter().fold(0u32, |acc, &x| acc.wrapping_add(x));
            let vals_clone = vals.clone();
            assert!(
                run(move |builder| {
                    let words: Vec<Word32> = vals_clone
                        .iter()
                        .map(|&v| alloc_constant_word(builder, v))
                        .collect();
                    let refs: Vec<&Word32> = words.iter().collect();
                    let out = add_mod_32(builder, &refs).unwrap();
                    assert_eq!(out.value, Some(expect));
                }),
                "add: vals={vals:?}"
            );
        }
    }

    /// Allocate a `WordN` whose bits are fresh boolean witness wires carrying
    /// the bits of `value` (mirrors `alloc_constant_word` for the variable-
    /// width path). Returns the resulting `WordN` plus the recomposed value
    /// variable so callers can rebind to it.
    fn alloc_constant_word_n(builder: &mut R1csBuilder<'_>, value: u64, num_bits: usize) -> WordN {
        let mut bits = Vec::with_capacity(num_bits);
        for i in 0..num_bits {
            let bv = Some(if ((value >> i) & 1) == 1 {
                Fr::one()
            } else {
                Fr::zero()
            });
            let v = builder.alloc_with_value(bv).unwrap();
            enforce_boolean(builder, v).unwrap();
            bits.push(LinearCombination(vec![(Fr::one(), v)]));
        }
        WordN::from_bits(bits, num_bits, Some(value))
    }

    fn mask(num_bits: usize) -> u64 {
        if num_bits == 64 {
            u64::MAX
        } else {
            (1u64 << num_bits) - 1
        }
    }

    #[test]
    fn and_n_matches_native_random_widths() {
        let mut rng = StdRng::seed_from_u64(0xA11D_AA7E);
        for &num_bits in &[8usize, 16, 32, 64] {
            for _ in 0..8 {
                let a: u64 = rng.gen::<u64>() & mask(num_bits);
                let b: u64 = rng.gen::<u64>() & mask(num_bits);
                let expect = a & b;
                assert!(
                    run(|builder| {
                        let aw = alloc_constant_word_n(builder, a, num_bits);
                        let bw = alloc_constant_word_n(builder, b, num_bits);
                        let out = and_n(builder, &aw, &bw).unwrap();
                        assert_eq!(out.value, Some(expect));
                        assert_eq!(out.num_bits, num_bits);
                    }),
                    "and_n: num_bits={num_bits} a={a:#x} b={b:#x}"
                );
            }
        }
    }

    #[test]
    fn xor_n_matches_native_random_widths() {
        let mut rng = StdRng::seed_from_u64(0x8E7E_4042);
        for &num_bits in &[8usize, 16, 32, 64] {
            for _ in 0..8 {
                let a: u64 = rng.gen::<u64>() & mask(num_bits);
                let b: u64 = rng.gen::<u64>() & mask(num_bits);
                let expect = a ^ b;
                assert!(
                    run(|builder| {
                        let aw = alloc_constant_word_n(builder, a, num_bits);
                        let bw = alloc_constant_word_n(builder, b, num_bits);
                        let out = xor_n(builder, &aw, &bw).unwrap();
                        assert_eq!(out.value, Some(expect));
                        assert_eq!(out.num_bits, num_bits);
                    }),
                    "xor_n: num_bits={num_bits} a={a:#x} b={b:#x}"
                );
            }
        }
    }

    #[test]
    fn xor_n_constraint_fails_on_bad_output() {
        // Build a XOR circuit then enforce that its output equals a lie.
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();
        let aw = alloc_constant_word_n(&mut b, 0xAAAA_AAAAu64, 32);
        let bw = alloc_constant_word_n(&mut b, 0x5555_5555u64, 32);
        let out = xor_n(&mut b, &aw, &bw).unwrap();
        // True XOR is 0xFFFF_FFFF; bind to a value var that asserts ==0.
        let bogus = b.alloc_with_value(Some(Fr::zero())).unwrap();
        out.bind_to_var(&b, bogus).unwrap();
        assert!(!cs.is_satisfied().unwrap());
    }

    #[test]
    fn add_mod_32_constraint_fails_on_bad_witness() {
        // If we lie about the result, satisfaction should fail.
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();
        let a = alloc_constant_word(&mut b, 7);
        let bw = alloc_constant_word(&mut b, 9);
        // Forge a "result" word with the wrong value but consistent bits.
        let _ = add_mod_32(&mut b, &[&a, &bw]).unwrap();
        // Now sneak in a contradicting result word that claims a+b=42 (wrong).
        // Build by alloc_with_value(Some(Fr::from(42))) for each bit forcibly.
        let mut bogus_bits = Vec::new();
        let bogus = 42u32;
        for i in 0..32 {
            let v = b
                .alloc_with_value(Some(if ((bogus >> i) & 1) == 1 {
                    Fr::one()
                } else {
                    Fr::zero()
                }))
                .unwrap();
            enforce_boolean(&b, v).unwrap();
            bogus_bits.push(LinearCombination(vec![(Fr::one(), v)]));
        }
        let bogus_word = Word32::from_bits(bogus_bits, Some(bogus));
        // Enforce: bogus = a + b (lie).
        let mut lc: Vec<(Fr, Variable)> = Vec::new();
        for (i, bit) in a.bits.iter().enumerate() {
            for (c, v) in bit.0.iter() {
                lc.push((*c * pow2(i), *v));
            }
        }
        for (i, bit) in bw.bits.iter().enumerate() {
            for (c, v) in bit.0.iter() {
                lc.push((*c * pow2(i), *v));
            }
        }
        for (i, bit) in bogus_word.bits.iter().enumerate() {
            for (c, v) in bit.0.iter() {
                lc.push((-*c * pow2(i), *v));
            }
        }
        b.enforce(b.zero_lc(), b.zero_lc(), LinearCombination(lc))
            .unwrap();
        assert!(!cs.is_satisfied().unwrap());
    }
}
