//! Range / bit-decomposition gadget.
//!
//! `decompose_into_bits(v, n)` allocates `n` boolean witnesses `b_0..b_{n-1}`
//! and enforces:
//!   1. each `b_i` is in `{0, 1}` (via [`enforce_boolean`]),
//!   2. `sum_i 2^i * b_i = v`.
//!
//! A pure range check is the same thing with the bits discarded.

use ark_bn254::Fr;
use ark_ff::{One, PrimeField};
use ark_relations::r1cs::{LinearCombination, SynthesisError, Variable};

use crate::field::fr_to_be_bytes;
use crate::gadgets::boolean::enforce_boolean;
use crate::r1cs_builder::R1csBuilder;

/// Maximum bit width we'll accept in a range gadget. BN254's scalar field is
/// ~254 bits; we cap below that to keep recomposition unambiguous.
pub const MAX_BITS: usize = 253;

/// Returns `Some(bit_i)` if `value` is known, otherwise `None` (setup mode).
fn ith_bit(value: Option<Fr>, i: usize) -> Option<Fr> {
    value.map(|v| {
        let bytes = fr_to_be_bytes(&v);
        // bytes is big-endian; bit i is byte (31 - i/8), bit (i % 8).
        let byte_index = 31 - i / 8;
        let bit_within = i % 8;
        let bit = (bytes[byte_index] >> bit_within) & 1;
        if bit == 1 {
            Fr::one()
        } else {
            Fr::from(0u64)
        }
    })
}

/// Recover an `Fr` value from a known `u128` little-endian magnitude.
#[inline]
fn pow2_fr(i: usize) -> Fr {
    let mut bytes = vec![0u8; 32];
    let byte_index = i / 8;
    let bit_within = i % 8;
    bytes[byte_index] = 1u8 << bit_within;
    Fr::from_le_bytes_mod_order(&bytes)
}

/// Decompose `value_var` into `num_bits` boolean variables (LSB first).
///
/// `value` is the proving-time concrete value (or `None` in setup mode).
pub fn decompose_into_bits(
    builder: &mut R1csBuilder<'_>,
    value_var: Variable,
    num_bits: usize,
    value: Option<Fr>,
) -> Result<Vec<Variable>, SynthesisError> {
    assert!(
        num_bits <= MAX_BITS,
        "decompose width {num_bits} exceeds MAX_BITS"
    );

    let mut bits = Vec::with_capacity(num_bits);
    let mut sum_terms: Vec<(Fr, Variable)> = Vec::with_capacity(num_bits + 1);

    for i in 0..num_bits {
        let bit_value = ith_bit(value, i);
        let bit_var = builder.alloc_with_value(bit_value)?;
        enforce_boolean(builder, bit_var)?;
        sum_terms.push((pow2_fr(i), bit_var));
        bits.push(bit_var);
    }

    // sum - value_var = 0
    sum_terms.push((-Fr::one(), value_var));
    builder.enforce(
        builder.zero_lc(),
        builder.zero_lc(),
        LinearCombination(sum_terms),
    )?;

    Ok(bits)
}

/// Range check: assert that `value_var` fits in `num_bits` bits. Drops the
/// decomposition.
pub fn enforce_range(
    builder: &mut R1csBuilder<'_>,
    value_var: Variable,
    num_bits: usize,
    value: Option<Fr>,
) -> Result<(), SynthesisError> {
    let _ = decompose_into_bits(builder, value_var, num_bits, value)?;
    Ok(())
}

/// Helper used by the SHA-256 gadget: equality between a 32-bit word's bit
/// decomposition (already allocated) and a value variable. Enforces
/// `sum_i 2^i * bits[i] = value_var`.
pub fn enforce_recompose_equals(
    builder: &R1csBuilder<'_>,
    bits: &[LinearCombination<Fr>],
    value_var: Variable,
) -> Result<(), SynthesisError> {
    let mut sum = LinearCombination(Vec::new());
    for (i, bit) in bits.iter().enumerate() {
        let coeff = pow2_fr(i);
        for (c, v) in bit.0.iter() {
            sum.0.push((*c * coeff, *v));
        }
    }
    sum.0.push((-Fr::one(), value_var));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), sum)
}

/// Return the literal `2^i` as an `Fr` (small-value helper for callers).
pub fn pow2(i: usize) -> Fr {
    pow2_fr(i)
}
