//! AES-128 (CBC mode, no padding) encryption gadget.
//!
//! Implements FIPS 197 AES-128 encryption in CBC mode with **no padding**
//! (input must be a multiple of 16 bytes). Used by Noir's
//! `BlackBoxFuncCall::AES128Encrypt`. Noir's `std::aes128::aes128_encrypt`
//! wrapper applies PKCS#7 padding **before** calling this opcode, so for a
//! 16-byte input the actual ACIR-level inputs are already 32 bytes
//! (a full padded block).
//!
//! ## Representation
//!
//! Every state byte is held as **8 bit-LCs (LSB first)** identical in shape
//! to a [`crate::gadgets::bitwise::Word32`] but width 8. All AES operations
//! except SubBytes are linear over GF(2), so XOR / ShiftRows / MixColumns /
//! AddRoundKey compose for free as `LinearCombination` algebra.
//!
//! ## Per-round cost
//!
//! | Step | R1CS cost per byte |
//! |---------------|-------------------------------------------------------|
//! | SubBytes | ~83 constraints (see [`s_box_in_circuit`] below) |
//! | ShiftRows | 0 (pure permutation of byte handles) |
//! | MixColumns | per byte: ~8 XOR constraints |
//! | AddRoundKey | per byte: 8 XOR constraints |
//!
//! Total ≈ 200 S-box invocations per CBC block (10 rounds × 16 bytes + 40
//! during key schedule), each costing ~83 constraints, so ~17k constraints
//! per encrypted block. Plus a fixed-size key schedule and per-block
//! AddRoundKey / MixColumns / XOR-with-previous-ciphertext overhead.
//!
//! ## S-box construction
//!
//! Each byte's S-box value is derived via the **GF(2^8) inverse + affine
//! transform** definition (FIPS 197 §5.1.1). The prover supplies the
//! 8-bit inverse `x_inv` and a `is_zero` flag; we verify
//! * `x * x_inv = 1 - is_zero` in **GF(2^8)** (a bit-multiplication
//!   constraint over the 64 cross-products),
//! * `x * is_zero = 0` (as field elements; forces `x = 0` when
//!   `is_zero = 1`),
//! * `x_inv * is_zero = 0` (forces `x_inv = 0` when `is_zero = 1`),
//! * `is_zero` is boolean.
//!
//! That makes `x_inv` the unique GF(2^8) inverse of `x` when `x ≠ 0`, and
//! `x_inv = 0` when `x = 0` (matching FIPS 197's convention `S(0) = 0x63`,
//! since the affine transform of `0` gives `0x63`).
//!
//! The output byte is then `Affine(x_inv) + 0x63`, where `Affine` is the
//! fixed 8×8 binary matrix from FIPS 197 §5.1.1 — pure XOR over GF(2),
//! so 0 R1CS constraints.

#![allow(clippy::needless_range_loop)]

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_relations::gr1cs::{LinearCombination, SynthesisError, Variable};

use crate::gadgets::boolean::enforce_boolean;
use crate::gadgets::range::{decompose_into_bits, pow2};
use crate::r1cs_builder::R1csBuilder;

// =============================================================================
// FIPS 197 constants
// =============================================================================

/// AES-128 round count.
const NR: usize = 10;
/// AES block size in bytes.
const BLOCK_BYTES: usize = 16;
/// AES-128 key size in bytes.
const KEY_BYTES: usize = 16;
/// Number of 32-bit words in a round-key schedule
/// (`(NR + 1) * 4 = 44` for AES-128).
const NB_WORDS: usize = 4 * (NR + 1);

/// FIPS 197 §5.2 round constants (used by the key schedule). `RCON[i]` is the
/// round constant for round `i+1` (1-indexed in the spec).
const RCON: [u8; 11] = [
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36,
];

/// FIPS 197 S-box (used only by the native reference). The in-circuit S-box
/// derives output bits algebraically — see [`s_box_in_circuit`].
#[rustfmt::skip]
const SBOX: [u8; 256] = [
 0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
 0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
 0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
 0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
 0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
 0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

// =============================================================================
// Native AES-128 (FIPS 197) — used by KAT + setup-mode value tracking.
// =============================================================================

/// AES-128 single-block encryption (ECB). Native reference.
pub fn aes128_block_encrypt_native(plaintext: &[u8; 16], key: &[u8; 16]) -> [u8; 16] {
    let round_keys = key_expansion_native(key);
    let mut state = *plaintext;
    add_round_key_native(&mut state, &round_keys, 0);
    for round in 1..NR {
        sub_bytes_native(&mut state);
        shift_rows_native(&mut state);
        mix_columns_native(&mut state);
        add_round_key_native(&mut state, &round_keys, round);
    }
    sub_bytes_native(&mut state);
    shift_rows_native(&mut state);
    add_round_key_native(&mut state, &round_keys, NR);
    state
}

/// AES-128 CBC encryption with **no padding**. `plaintext.len()` must be a
/// multiple of 16. Mirrors the contract of Noir's `aes128_encrypt` opcode
/// (the stdlib wrapper pads with PKCS#7 first).
pub fn aes128_encrypt_native(plaintext: &[u8], iv: &[u8; 16], key: &[u8; 16]) -> Vec<u8> {
    assert!(
        plaintext.len() % 16 == 0,
        "aes128_encrypt_native: input length {} not a multiple of 16",
        plaintext.len()
    );
    let mut prev = *iv;
    let mut out = Vec::with_capacity(plaintext.len());
    for block_idx in 0..plaintext.len() / 16 {
        let mut block = [0u8; 16];
        for j in 0..16 {
            block[j] = plaintext[block_idx * 16 + j] ^ prev[j];
        }
        let ct = aes128_block_encrypt_native(&block, key);
        out.extend_from_slice(&ct);
        prev = ct;
    }
    out
}

fn key_expansion_native(key: &[u8; KEY_BYTES]) -> [[u8; 4]; NB_WORDS] {
    let mut w = [[0u8; 4]; NB_WORDS];
    for i in 0..4 {
        w[i] = [key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]];
    }
    for i in 4..NB_WORDS {
        let mut temp = w[i - 1];
        if i % 4 == 0 {
            // RotWord
            temp = [temp[1], temp[2], temp[3], temp[0]];
            // SubWord
            for t in &mut temp {
                *t = SBOX[*t as usize];
            }
            // XOR Rcon
            temp[0] ^= RCON[i / 4];
        }
        for j in 0..4 {
            w[i][j] = w[i - 4][j] ^ temp[j];
        }
    }
    w
}

fn add_round_key_native(state: &mut [u8; 16], rk: &[[u8; 4]; NB_WORDS], round: usize) {
    for col in 0..4 {
        for row in 0..4 {
            state[col * 4 + row] ^= rk[round * 4 + col][row];
        }
    }
}

fn sub_bytes_native(state: &mut [u8; 16]) {
    for b in state.iter_mut() {
        *b = SBOX[*b as usize];
    }
}

fn shift_rows_native(state: &mut [u8; 16]) {
    // State is column-major: state[c*4 + r] is row r, column c.
    let mut out = [0u8; 16];
    for r in 0..4 {
        for c in 0..4 {
            out[c * 4 + r] = state[((c + r) % 4) * 4 + r];
        }
    }
    *state = out;
}

fn mix_columns_native(state: &mut [u8; 16]) {
    for c in 0..4 {
        let s0 = state[c * 4];
        let s1 = state[c * 4 + 1];
        let s2 = state[c * 4 + 2];
        let s3 = state[c * 4 + 3];
        state[c * 4] = xtime(s0) ^ (xtime(s1) ^ s1) ^ s2 ^ s3;
        state[c * 4 + 1] = s0 ^ xtime(s1) ^ (xtime(s2) ^ s2) ^ s3;
        state[c * 4 + 2] = s0 ^ s1 ^ xtime(s2) ^ (xtime(s3) ^ s3);
        state[c * 4 + 3] = (xtime(s0) ^ s0) ^ s1 ^ s2 ^ xtime(s3);
    }
}

/// Multiply by x in GF(2^8) with reduction polynomial 0x11B.
#[inline]
fn xtime(b: u8) -> u8 {
    let hi = b >> 7;
    let shifted = b << 1;
    if hi == 1 { shifted ^ 0x1b } else { shifted }
}

// =============================================================================
// In-circuit byte representation
// =============================================================================

/// A single AES state byte held as 8 bit-LCs (LSB first) plus an optional
/// proving-time concrete value. Mirrors the shape of [`crate::gadgets::bitwise::Word32`]
/// but width 8.
#[derive(Clone)]
struct Byte {
    /// 8 bit linear combinations (LSB first).
    bits: [LinearCombination<Fr>; 8],
    /// Proving-time concrete byte value, or `None` in setup mode.
    value: Option<u8>,
}

impl Byte {
    fn from_bit_lcs(bits: [LinearCombination<Fr>; 8], value: Option<u8>) -> Self {
        Self { bits, value }
    }

    /// Build a constant 8-bit value (no fresh witnesses, no constraints).
    fn constant(value: u8) -> Self {
        let bits: [LinearCombination<Fr>; 8] = std::array::from_fn(|i| {
            if (value >> i) & 1 == 1 {
                LinearCombination(vec![(Fr::one(), Variable::One)])
            } else {
                LinearCombination(vec![])
            }
        });
        Self {
            bits,
            value: Some(value),
        }
    }

    /// Bit-wise XOR of two bytes via per-bit allocation.
    fn xor(&self, builder: &mut R1csBuilder<'_>, other: &Byte) -> Result<Byte, SynthesisError> {
        let two = Fr::one() + Fr::one();
        let out_value = match (self.value, other.value) {
            (Some(a), Some(b)) => Some(a ^ b),
            _ => None,
        };
        let mut out_bits: [LinearCombination<Fr>; 8] =
            std::array::from_fn(|_| LinearCombination(vec![]));
        for i in 0..8 {
            let av = self.value.map(|v| (v >> i) & 1);
            let bv = other.value.map(|v| (v >> i) & 1);
            let out_bit_val = match (av, bv) {
                (Some(x), Some(y)) => Some(if (x ^ y) == 1 { Fr::one() } else { Fr::zero() }),
                _ => None,
            };
            let out_var = builder.alloc_with_value(out_bit_val)?;
            enforce_boolean(builder, out_var)?;

            // Enforce `(2*a) * b = (a + b - out)`.
            let mut two_a: Vec<(Fr, Variable)> = Vec::with_capacity(self.bits[i].0.len());
            for (c, v) in self.bits[i].0.iter() {
                two_a.push((*c * two, *v));
            }
            let mut sum_lc: Vec<(Fr, Variable)> =
                Vec::with_capacity(self.bits[i].0.len() + other.bits[i].0.len() + 1);
            for (c, v) in self.bits[i].0.iter() {
                sum_lc.push((*c, *v));
            }
            for (c, v) in other.bits[i].0.iter() {
                sum_lc.push((*c, *v));
            }
            sum_lc.push((-Fr::one(), out_var));

            builder.enforce(
                LinearCombination(two_a),
                other.bits[i].clone(),
                LinearCombination(sum_lc),
            )?;

            out_bits[i] = LinearCombination(vec![(Fr::one(), out_var)]);
        }
        Ok(Byte::from_bit_lcs(out_bits, out_value))
    }

    /// Multiply by `x` in GF(2^8) (the AES "xtime" operation). Each output
    /// bit is either a permutation of an input bit (free) or a 2-input XOR of
    /// input bits (materialised as a fresh witness via `xor_bits_to_bit`).
    /// Cost: ~3 fresh-bit XORs per byte × 4 constraints each = 12 constraints
    /// per xtime call (the 5 unchanged-permutation bits are free).
    fn xtime(&self, builder: &mut R1csBuilder<'_>) -> Result<Byte, SynthesisError> {
        let b = &self.bits;
        // Output bits b0..b7 for "multiply by x" in GF(2^8) with reduction 0x1B:
        // out_0 = b7
        // out_1 = b0 XOR b7
        // out_2 = b1
        // out_3 = b2 XOR b7
        // out_4 = b3 XOR b7
        // out_5 = b4
        // out_6 = b5
        // out_7 = b6
        let value = self.value.map(xtime);
        let input_value = self.value;
        let bit_vals_pair = |i: usize, j: usize| -> Option<[u8; 2]> {
            input_value.map(|v| [(v >> i) & 1, (v >> j) & 1])
        };
        let out_bits: [LinearCombination<Fr>; 8] = [
            b[7].clone(),
            xor_bits_to_bit(
                builder,
                &[&b[0], &b[7]],
                bit_vals_pair(0, 7).as_ref().map(|s| &s[..]),
                0,
                bit_value(value, 1),
            )?,
            b[1].clone(),
            xor_bits_to_bit(
                builder,
                &[&b[2], &b[7]],
                bit_vals_pair(2, 7).as_ref().map(|s| &s[..]),
                0,
                bit_value(value, 3),
            )?,
            xor_bits_to_bit(
                builder,
                &[&b[3], &b[7]],
                bit_vals_pair(3, 7).as_ref().map(|s| &s[..]),
                0,
                bit_value(value, 4),
            )?,
            b[4].clone(),
            b[5].clone(),
            b[6].clone(),
        ];
        Ok(Byte::from_bit_lcs(out_bits, value))
    }

    /// Build the byte's value as a linear combination
    /// `sum_{i=0..8} 2^i * bits[i]`. No constraints — pure LC arithmetic.
    fn value_lc(&self) -> LinearCombination<Fr> {
        let mut terms: Vec<(Fr, Variable)> = Vec::new();
        for i in 0..8 {
            let coeff = pow2(i);
            for (c, v) in self.bits[i].0.iter() {
                terms.push((*c * coeff, *v));
            }
        }
        LinearCombination(terms)
    }
}

/// Compute the value of bit `i` of an optional byte (for proving-time
/// witness allocation). Returns `None` in setup mode.
fn bit_value(byte_value: Option<u8>, i: usize) -> Option<u8> {
    byte_value.map(|v| (v >> i) & 1)
}

/// Materialise a parity bit equal to `(sum_of_bit_lcs + const_bit) mod 2`
/// where each input bit-LC evaluates to 0 or 1.
///
/// The function allocates one fresh boolean witness `out` and enough carry
/// witnesses `c_k` so that
/// `sum_of_input_bits + const_bit = out + 2 * (carry value)`. Single linear
/// R1CS constraint binds the sum; `out` and each carry bit get a boolean
/// constraint each.
///
/// Cost: `1 + ceil(log2(N/2 + 1))` boolean constraints + 1 linear constraint,
/// where `N` is the number of input bit-LCs (plus 1 if `const_bit = 1`).
///
/// `input_bit_values`, if provided, is the proving-time `{0,1}`-valued
/// concrete values of each input bit-LC in order; used to compute the carry
/// witness values eagerly.
fn xor_bits_to_bit(
    builder: &mut R1csBuilder<'_>,
    bit_lcs: &[&LinearCombination<Fr>],
    input_bit_values: Option<&[u8]>,
    const_bit: u8,
    out_value: Option<u8>,
) -> Result<LinearCombination<Fr>, SynthesisError> {
    assert!(const_bit <= 1, "const_bit must be 0 or 1");
    if let Some(vals) = input_bit_values {
        debug_assert_eq!(
            vals.len(),
            bit_lcs.len(),
            "input_bit_values length mismatch"
        );
    }
    let n = bit_lcs.len();
    let max_sum = n as u64 + const_bit as u64;
    // Number of carry bits needed: bit-width of floor(max_sum / 2).
    let carry_max = max_sum / 2;
    let carry_bits: usize = if carry_max == 0 {
        0
    } else {
        (u64::BITS - carry_max.leading_zeros()) as usize
    };

    // Compute concrete sum at proving time (if known) so we can populate the
    // out and carry witnesses eagerly.
    let sum_int: Option<u64> =
        input_bit_values.map(|vals| vals.iter().map(|b| *b as u64).sum::<u64>() + const_bit as u64);
    let computed_out: Option<u8> = sum_int.map(|s| (s & 1) as u8);
    let actual_out_value = out_value.or(computed_out);
    if let (Some(a), Some(b)) = (out_value, computed_out) {
        debug_assert_eq!(a, b, "xor_bits_to_bit: out_value mismatch");
    }
    let carry_total: Option<u64> = sum_int.map(|s| s >> 1);

    // Allocate output bit + carry bits.
    let out_fr = actual_out_value.map(|b| if b == 1 { Fr::one() } else { Fr::zero() });
    let out_var = builder.alloc_with_value(out_fr)?;
    enforce_boolean(builder, out_var)?;

    let mut carry_vars: Vec<Variable> = Vec::with_capacity(carry_bits);
    for k in 0..carry_bits {
        let bit_val = carry_total.map(|ct| {
            if (ct >> k) & 1 == 1 {
                Fr::one()
            } else {
                Fr::zero()
            }
        });
        let var = builder.alloc_with_value(bit_val)?;
        enforce_boolean(builder, var)?;
        carry_vars.push(var);
    }

    // Linear constraint: sum_of_input_bits + const_bit - out - 2*sum(2^k * carry_k) = 0.
    let mut terms: Vec<(Fr, Variable)> = Vec::new();
    for lc in bit_lcs {
        for (c, v) in lc.0.iter() {
            terms.push((*c, *v));
        }
    }
    if const_bit == 1 {
        terms.push((Fr::one(), Variable::One));
    }
    terms.push((-Fr::one(), out_var));
    for (k, cv) in carry_vars.iter().enumerate() {
        let coeff = -(pow2(k + 1));
        terms.push((coeff, *cv));
    }
    builder.enforce(
        builder.zero_lc(),
        builder.zero_lc(),
        LinearCombination(terms),
    )?;

    Ok(LinearCombination(vec![(Fr::one(), out_var)]))
}

// =============================================================================
// In-circuit S-box (GF(2^8) inverse + affine transform).
// =============================================================================

/// AES affine transform applied to a single byte after GF(2^8) inversion.
/// Each output bit is a fixed XOR of 5 input bits + a constant bit, per
/// FIPS 197 §5.1.1. Each output bit is materialised via
/// [`xor_bits_to_bit`] into a fresh boolean witness (so downstream gadgets
/// see single-Variable LCs).
///
/// Output bit `i` (LSB first) =
/// `x_i XOR x_{(i+4) mod 8} XOR x_{(i+5) mod 8}
/// XOR x_{(i+6) mod 8} XOR x_{(i+7) mod 8} XOR c_i`
/// where the constant byte is `0x63 = 0110_0011`, bit `i` of which is `c_i`.
fn affine_transform(builder: &mut R1csBuilder<'_>, input: &Byte) -> Result<Byte, SynthesisError> {
    let constant_byte: u8 = 0x63;
    let value = input.value.map(|x_inv| {
        let mut out = 0u8;
        for i in 0..8 {
            let mut bit = 0u8;
            for &k in &[0usize, 4, 5, 6, 7] {
                bit ^= (x_inv >> ((i + k) % 8)) & 1;
            }
            bit ^= (constant_byte >> i) & 1;
            out |= bit << i;
        }
        out
    });
    let mut out_bits: [LinearCombination<Fr>; 8] =
        std::array::from_fn(|_| LinearCombination(vec![]));
    for i in 0..8 {
        let idxs = [i % 8, (i + 4) % 8, (i + 5) % 8, (i + 6) % 8, (i + 7) % 8];
        let lcs = [
            &input.bits[idxs[0]],
            &input.bits[idxs[1]],
            &input.bits[idxs[2]],
            &input.bits[idxs[3]],
            &input.bits[idxs[4]],
        ];
        let input_bit_vals: Option<[u8; 5]> = input
            .value
            .map(|v| std::array::from_fn(|k| (v >> idxs[k]) & 1));
        let c_bit = (constant_byte >> i) & 1;
        out_bits[i] = xor_bits_to_bit(
            builder,
            &lcs,
            input_bit_vals.as_ref().map(|s| &s[..]),
            c_bit,
            bit_value(value, i),
        )?;
    }
    Ok(Byte::from_bit_lcs(out_bits, value))
}

/// AES S-box on a byte held as 8 bit-LCs. Returns a fresh `Byte` whose bits are
/// each a single Variable (so downstream XOR/MixColumns chains stay cheap).
///
/// Implements `S(x) = Affine(x^{-1}) XOR 0x63` (FIPS 197 §5.1.1) using the
/// GF(2^8) inverse + affine transform formulation. The cost breakdown is in
/// the module docstring. After the affine, we re-materialise each output bit
/// as a single boolean witness via `enforce_boolean` + a linear equality so
/// the bits stay single-Variable LCs.
fn s_box_in_circuit(builder: &mut R1csBuilder<'_>, input: &Byte) -> Result<Byte, SynthesisError> {
    let x_value = input.value;
    let (x_inv_value, is_zero_value) = match x_value {
        Some(x) => {
            if x == 0 {
                (Some(0u8), Some(1u8))
            } else {
                (Some(gf256_inv(x)), Some(0u8))
            }
        }
        None => (None, None),
    };

    // -- Allocate is_zero boolean. ---------------------------------------------
    let is_zero_fr = is_zero_value.map(|v| if v == 1 { Fr::one() } else { Fr::zero() });
    let is_zero_var = builder.alloc_with_value(is_zero_fr)?;
    enforce_boolean(builder, is_zero_var)?;
    let is_zero_lc = LinearCombination(vec![(Fr::one(), is_zero_var)]);

    // -- Allocate 8 boolean bits of x_inv. -------------------------------------
    let mut x_inv_bit_vars = [Variable::One; 8];
    for i in 0..8 {
        let bit_val = x_inv_value.map(|v| {
            if (v >> i) & 1 == 1 {
                Fr::one()
            } else {
                Fr::zero()
            }
        });
        let var = builder.alloc_with_value(bit_val)?;
        enforce_boolean(builder, var)?;
        x_inv_bit_vars[i] = var;
    }
    let x_inv_bits: [LinearCombination<Fr>; 8] =
        std::array::from_fn(|i| LinearCombination(vec![(Fr::one(), x_inv_bit_vars[i])]));

    // -- Enforce `x * is_zero = 0` (single R1CS over field elements). ----------
    // Forces `x = 0` when `is_zero = 1` (since byte values are in [0, 255], if
    // `x * 1 = 0` as a field element then `x = 0`).
    builder.enforce(input.value_lc(), is_zero_lc.clone(), builder.zero_lc())?;

    // -- Enforce `x_inv * is_zero = 0` (single R1CS). --------------------------
    // Forces `x_inv = 0` when `is_zero = 1` (so the S-box output is uniquely
    // determined: `Affine(0) XOR 0x63 = 0x63 XOR 0x63 =...`, see below).
    let x_inv_value_lc = {
        let mut terms: Vec<(Fr, Variable)> = Vec::with_capacity(8);
        for i in 0..8 {
            terms.push((pow2(i), x_inv_bit_vars[i]));
        }
        LinearCombination(terms)
    };
    builder.enforce(x_inv_value_lc, is_zero_lc, builder.zero_lc())?;

    // -- Compute the 64 cross-products p_{i,j} = x_bits[i] * x_inv_bits[j]. ----
    //
    // Each product is one fresh boolean witness + one R1CS AND constraint.
    let mut p = [[Variable::One; 8]; 8];
    for i in 0..8 {
        for j in 0..8 {
            let xi = x_value.map(|x| (x >> i) & 1);
            let yj = x_inv_value.map(|y| (y >> j) & 1);
            let pij_val = match (xi, yj) {
                (Some(a), Some(b)) => Some(if (a & b) == 1 { Fr::one() } else { Fr::zero() }),
                _ => None,
            };
            let pij = builder.alloc_with_value(pij_val)?;
            // Constraint: x_bits[i] * x_inv_bits[j] = pij.
            builder.enforce(
                input.bits[i].clone(),
                x_inv_bits[j].clone(),
                LinearCombination(vec![(Fr::one(), pij)]),
            )?;
            p[i][j] = pij;
        }
    }

    // -- GF(2^8) multiplication: compute the 8 output bits as XOR sums of p_ij. -
    //
    // Reduction polynomial m(x) = x^8 + x^4 + x^3 + x + 1 (0x11B).
    // For each (i, j), the product x^i * y^j = x^(i+j); reduce x^k for k ≥ 8
    // by repeated multiplication by x, using a lookup table of "bits of x^k mod m"
    // for k in [0, 14].
    //
    // Each output bit `prod_bits[k]` is an XOR (parity over GF(2)) of the
    // contributing `p[i][j]` witnesses. We materialise each parity bit via
    // [`xor_bits_to_bit`] (which uses a sum-with-carries decomposition so the
    // field-level identity matches the GF(2)-level XOR).
    let xk_bits = gf256_xk_bits();
    let mut prod_contribs: [Vec<LinearCombination<Fr>>; 8] = std::array::from_fn(|_| Vec::new());
    // Track which (i, j) cross-products contribute to each output bit, so we
    // can compute the carry witness values eagerly at proving time.
    let mut prod_pair_indices: [Vec<(usize, usize)>; 8] = std::array::from_fn(|_| Vec::new());
    for i in 0..8 {
        for j in 0..8 {
            let exponents = xk_bits[i + j];
            for k in 0..8 {
                if (exponents >> k) & 1 == 1 {
                    prod_contribs[k].push(LinearCombination(vec![(Fr::one(), p[i][j])]));
                    prod_pair_indices[k].push((i, j));
                }
            }
        }
    }

    // Compute the expected product = x * x_inv in GF(2^8) at proving time.
    let prod_value = match (x_value, x_inv_value) {
        (Some(a), Some(b)) => Some(gf256_mul(a, b)),
        _ => None,
    };

    // Materialise prod_bits[k] for k = 0..8. The bit k of prod is the parity
    // (XOR) of all contributing p[i][j] witnesses.
    let mut prod_bits: [LinearCombination<Fr>; 8] =
        std::array::from_fn(|_| LinearCombination(vec![]));
    for k in 0..8 {
        let refs: Vec<&LinearCombination<Fr>> = prod_contribs[k].iter().collect();
        let out_bit_val = prod_value.map(|v| (v >> k) & 1);
        // For each contributing (i, j) pair, the concrete value of p[i][j] is
        // bit_i(x) AND bit_j(x_inv) — known at proving time when both are.
        let input_bit_vals: Option<Vec<u8>> = match (x_value, x_inv_value) {
            (Some(xv), Some(yv)) => Some(
                prod_pair_indices[k]
                    .iter()
                    .map(|&(i, j)| ((xv >> i) & 1) & ((yv >> j) & 1))
                    .collect(),
            ),
            _ => None,
        };
        prod_bits[k] = xor_bits_to_bit(builder, &refs, input_bit_vals.as_deref(), 0, out_bit_val)?;
    }

    // -- Enforce prod_bits[0] = 1 - is_zero and prod_bits[1..8] = 0. -----------
    //
    // prod_bits[0] - (1 - is_zero) = 0 ⇒ prod_bits[0] + is_zero - 1 = 0.
    {
        let mut terms = prod_bits[0].0.clone();
        terms.push((Fr::one(), is_zero_var));
        terms.push((-Fr::one(), Variable::One));
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(terms),
        )?;
    }
    for k in 1..8 {
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(prod_bits[k].0.clone()),
        )?;
    }

    // -- Compose the S-box output: Affine(x_inv) XOR 0x63. ---------------------
    //
    // `affine_transform` folds in the `XOR 0x63` constant and materialises each
    // output bit into a single-Variable LC.
    let x_inv_byte = Byte::from_bit_lcs(x_inv_bits, x_inv_value);
    let affine_out = affine_transform(builder, &x_inv_byte)?;
    Ok(affine_out)
}

/// Precomputed reduction table: `xk_bits()[k]` is the byte representation of
/// `x^k mod (x^8 + x^4 + x^3 + x + 1)` for `k ∈ [0, 14]`. Indexed by exponent
/// `i + j ∈ [0, 14]` from the cross-product expansion. Bits LSB first inside
/// the returned `u8` (so `xk_bits()[k] & 1` is the constant coefficient).
fn gf256_xk_bits() -> [u8; 15] {
    let mut out = [0u8; 15];
    let mut cur: u16 = 1; // x^0 = 1
    for entry in out.iter_mut() {
        // Reduce cur modulo m(x) = x^8 + x^4 + x^3 + x + 1.
        let mut v = cur;
        while v >= 0x100 {
            // Find highest bit position; subtract 0x11B shifted appropriately.
            let high = 15 - v.leading_zeros() as usize;
            v ^= 0x11Bu16 << (high - 8);
        }
        *entry = v as u8;
        // Multiply by x for the next iteration (don't reduce yet).
        cur <<= 1;
    }
    out
}

/// GF(2^8) inverse via x^254 (Fermat). Returns 0 for input 0.
fn gf256_inv(x: u8) -> u8 {
    if x == 0 {
        return 0;
    }
    let mut acc: u8 = 1;
    let mut base = x;
    let mut exp: u32 = 254;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = gf256_mul(acc, base);
        }
        base = gf256_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// GF(2^8) multiplication with reduction polynomial 0x11B.
fn gf256_mul(mut a: u8, mut b: u8) -> u8 {
    let mut r: u8 = 0;
    for _ in 0..8 {
        if b & 1 == 1 {
            r ^= a;
        }
        let hi = a & 0x80;
        a <<= 1;
        if hi != 0 {
            a ^= 0x1b;
        }
        b >>= 1;
    }
    r
}

// =============================================================================
// In-circuit AES rounds and key schedule.
// =============================================================================

/// AES-128 single-block in-circuit encryption. The state is a 16-byte array
/// (column-major: byte `c*4 + r` is row `r`, column `c`). Returns 16 fresh
/// bytes after 10 rounds.
fn aes128_block_encrypt_in_circuit(
    builder: &mut R1csBuilder<'_>,
    plaintext: &[Byte; 16],
    round_keys: &[[Byte; 4]; NB_WORDS],
) -> Result<[Byte; 16], SynthesisError> {
    let mut state: [Byte; 16] = plaintext.clone();
    add_round_key(builder, &mut state, round_keys, 0)?;
    for round in 1..NR {
        sub_bytes(builder, &mut state)?;
        shift_rows(&mut state);
        mix_columns(builder, &mut state)?;
        add_round_key(builder, &mut state, round_keys, round)?;
    }
    sub_bytes(builder, &mut state)?;
    shift_rows(&mut state);
    add_round_key(builder, &mut state, round_keys, NR)?;
    Ok(state)
}

fn sub_bytes(builder: &mut R1csBuilder<'_>, state: &mut [Byte; 16]) -> Result<(), SynthesisError> {
    for byte in state.iter_mut() {
        *byte = s_box_in_circuit(builder, byte)?;
    }
    Ok(())
}

fn shift_rows(state: &mut [Byte; 16]) {
    let mut out: [Byte; 16] = state.clone();
    for r in 0..4 {
        for c in 0..4 {
            out[c * 4 + r] = state[((c + r) % 4) * 4 + r].clone();
        }
    }
    *state = out;
}

fn mix_columns(
    builder: &mut R1csBuilder<'_>,
    state: &mut [Byte; 16],
) -> Result<(), SynthesisError> {
    let mut out: [Byte; 16] = state.clone();
    for c in 0..4 {
        let s0 = state[c * 4].clone();
        let s1 = state[c * 4 + 1].clone();
        let s2 = state[c * 4 + 2].clone();
        let s3 = state[c * 4 + 3].clone();
        let t0 = s0.xtime(builder)?;
        let t1 = s1.xtime(builder)?;
        let t2 = s2.xtime(builder)?;
        let t3 = s3.xtime(builder)?;
        let s0 = &s0;
        let s1 = &s1;
        let s2 = &s2;
        let s3 = &s3;
        // out[0] = xtime(s0) XOR (xtime(s1) XOR s1) XOR s2 XOR s3
        // = t0 XOR t1 XOR s1 XOR s2 XOR s3
        out[c * 4] = chain_xor(builder, &[&t0, &t1, s1, s2, s3])?;
        // out[1] = s0 XOR xtime(s1) XOR (xtime(s2) XOR s2) XOR s3
        // = s0 XOR t1 XOR t2 XOR s2 XOR s3
        out[c * 4 + 1] = chain_xor(builder, &[s0, &t1, &t2, s2, s3])?;
        // out[2] = s0 XOR s1 XOR xtime(s2) XOR (xtime(s3) XOR s3)
        // = s0 XOR s1 XOR t2 XOR t3 XOR s3
        out[c * 4 + 2] = chain_xor(builder, &[s0, s1, &t2, &t3, s3])?;
        // out[3] = (xtime(s0) XOR s0) XOR s1 XOR s2 XOR xtime(s3)
        // = t0 XOR s0 XOR s1 XOR s2 XOR t3
        out[c * 4 + 3] = chain_xor(builder, &[&t0, s0, s1, s2, &t3])?;
    }
    *state = out;
    Ok(())
}

/// XOR of N bytes. For `N ≤ 2` falls through to the binary `Byte::xor`; for
/// `N ≥ 3` uses the parity identity `Σ bit_j = out + 2·k` with a small
/// carry `k ∈ [0, ⌊N/2⌋]` decomposed into `ceil(log2(⌊N/2⌋+1))` bits.
/// Cost per output bit drops from `2·(N−1)` constraints (chained binary
/// XORs) to `1 + ceil(log2(⌊N/2⌋+1)) + 1`, saving ~25–40% on the AES
/// MixColumns row XOR (4 × 5-term XORs per round × 9 rounds).
fn chain_xor(builder: &mut R1csBuilder<'_>, terms: &[&Byte]) -> Result<Byte, SynthesisError> {
    assert!(!terms.is_empty(), "chain_xor: empty terms");
    if terms.len() == 1 {
        return Ok(terms[0].clone());
    }
    if terms.len() == 2 {
        return terms[0].xor(builder, terms[1]);
    }
    let n = terms.len();
    let max_carry = n / 2;
    let carry_bits = if max_carry == 0 {
        1
    } else {
        (usize::BITS - max_carry.leading_zeros()) as usize
    };
    let out_value: Option<u8> = terms
        .iter()
        .try_fold(0u8, |acc, b| b.value.map(|v| acc ^ v));
    let mut out_bits: [LinearCombination<Fr>; 8] =
        std::array::from_fn(|_| LinearCombination(vec![]));
    for bit_i in 0..8 {
        let sum_val: Option<u32> = terms.iter().try_fold(0u32, |acc, b| {
            b.value.map(|v| acc + (((v >> bit_i) & 1) as u32))
        });
        let out_bit_val = sum_val.map(|s| if s & 1 == 1 { Fr::one() } else { Fr::zero() });
        let out_var = builder.alloc_with_value(out_bit_val)?;
        enforce_boolean(builder, out_var)?;

        let k_val = sum_val.map(|s| Fr::from(s >> 1));
        let k_var = builder.alloc_with_value(k_val)?;
        let _ = decompose_into_bits(builder, k_var, carry_bits, k_val)?;

        let mut lc: Vec<(Fr, Variable)> = Vec::new();
        for b in terms {
            for (c, v) in b.bits[bit_i].0.iter() {
                lc.push((*c, *v));
            }
        }
        lc.push((-Fr::one(), out_var));
        let two = Fr::one() + Fr::one();
        lc.push((-two, k_var));
        builder.enforce(builder.zero_lc(), builder.zero_lc(), LinearCombination(lc))?;

        out_bits[bit_i] = LinearCombination(vec![(Fr::one(), out_var)]);
    }
    Ok(Byte::from_bit_lcs(out_bits, out_value))
}

fn add_round_key(
    builder: &mut R1csBuilder<'_>,
    state: &mut [Byte; 16],
    round_keys: &[[Byte; 4]; NB_WORDS],
    round: usize,
) -> Result<(), SynthesisError> {
    for c in 0..4 {
        for r in 0..4 {
            let new_byte = state[c * 4 + r].xor(builder, &round_keys[round * 4 + c][r])?;
            state[c * 4 + r] = new_byte;
        }
    }
    Ok(())
}

/// In-circuit AES-128 key expansion. Returns 44 four-byte round-key words.
fn expand_key_in_circuit(
    builder: &mut R1csBuilder<'_>,
    key: &[Byte; 16],
) -> Result<[[Byte; 4]; NB_WORDS], SynthesisError> {
    // Build the placeholder array of empty bytes (will be overwritten).
    let placeholder: [Byte; 4] = std::array::from_fn(|_| Byte::constant(0));
    let mut w: [[Byte; 4]; NB_WORDS] = std::array::from_fn(|_| placeholder.clone());
    for i in 0..4 {
        w[i] = [
            key[4 * i].clone(),
            key[4 * i + 1].clone(),
            key[4 * i + 2].clone(),
            key[4 * i + 3].clone(),
        ];
    }
    for i in 4..NB_WORDS {
        let mut temp = w[i - 1].clone();
        if i % 4 == 0 {
            // RotWord
            temp = [
                temp[1].clone(),
                temp[2].clone(),
                temp[3].clone(),
                temp[0].clone(),
            ];
            // SubWord
            for t in &mut temp {
                *t = s_box_in_circuit(builder, t)?;
            }
            // XOR Rcon (RCON[i/4] applied to byte 0)
            let rcon_byte = Byte::constant(RCON[i / 4]);
            temp[0] = temp[0].xor(builder, &rcon_byte)?;
        }
        for j in 0..4 {
            w[i][j] = w[i - 4][j].xor(builder, &temp[j])?;
        }
    }
    Ok(w)
}

// =============================================================================
// Public entry point (called by the lowering layer)
// =============================================================================

/// Run AES-128 CBC encryption (no padding) on `plaintext_vars` (each a u8-valued
/// `(Variable, Option<Fr>)` pair). Returns the ciphertext as a `Vec<Variable>`
/// of fresh witness vars, each holding one output byte and pinned to its bit
/// decomposition via a single linear equality.
///
/// `plaintext_vars.len()` must be a non-zero multiple of 16 (the contract of
/// Noir's `BlackBoxFuncCall::AES128Encrypt`). The 16-byte `iv` and `key`
/// arrays are also `(Variable, Option<Fr>)` pairs.
pub fn aes128_encrypt_in_circuit(
    builder: &mut R1csBuilder<'_>,
    plaintext_vars: &[(Variable, Option<Fr>)],
    iv_vars: &[(Variable, Option<Fr>); 16],
    key_vars: &[(Variable, Option<Fr>); 16],
) -> Result<Vec<Variable>, SynthesisError> {
    assert!(
        !plaintext_vars.is_empty() && plaintext_vars.len() % BLOCK_BYTES == 0,
        "aes128_encrypt_in_circuit: input length {} must be a positive \
 multiple of {}",
        plaintext_vars.len(),
        BLOCK_BYTES,
    );

    // -- 1. Decompose every input byte (plaintext, iv, key) into 8 bit-LCs. ----
    //
    // Each byte gets bit-decomposed (LSB first); this doubles as the implicit
    // 8-bit range check on the input bytes. Noir already emits a RANGE opcode
    // for u8-typed witnesses, but the decomposition we do here is independent
    // — it's needed for the bit-level AES algebra.
    let plaintext: Vec<Byte> = plaintext_vars
        .iter()
        .map(|(v, val)| decompose_byte(builder, *v, *val))
        .collect::<Result<_, _>>()?;
    let iv_bytes: [Byte; 16] = {
        let v: Vec<Byte> = iv_vars
            .iter()
            .map(|(v, val)| decompose_byte(builder, *v, *val))
            .collect::<Result<_, _>>()?;
        v.try_into().map_err(|_| SynthesisError::Unsatisfiable)?
    };
    let key_bytes: [Byte; 16] = {
        let v: Vec<Byte> = key_vars
            .iter()
            .map(|(v, val)| decompose_byte(builder, *v, *val))
            .collect::<Result<_, _>>()?;
        v.try_into().map_err(|_| SynthesisError::Unsatisfiable)?
    };

    // -- 2. Expand the key once. -----------------------------------------------
    let round_keys = expand_key_in_circuit(builder, &key_bytes)?;

    // -- 3. CBC: for each block, XOR with prev, then AES single-block encrypt. -
    let n_blocks = plaintext.len() / BLOCK_BYTES;
    let mut out_vars: Vec<Variable> = Vec::with_capacity(plaintext.len());
    let mut prev: [Byte; 16] = iv_bytes;
    for block_idx in 0..n_blocks {
        // XOR plaintext_block with prev (the IV or previous ciphertext).
        let mut input_block: [Byte; 16] = std::array::from_fn(|_| Byte::constant(0));
        for j in 0..BLOCK_BYTES {
            input_block[j] = plaintext[block_idx * BLOCK_BYTES + j].xor(builder, &prev[j])?;
        }
        // Encrypt.
        let ct_block = aes128_block_encrypt_in_circuit(builder, &input_block, &round_keys)?;
        // Materialise each ciphertext byte as a fresh value-Variable bound to
        // its bit decomposition via a single linear equality.
        for byte in ct_block.iter() {
            let byte_value_fr = byte.value.map(|v| Fr::from(v as u64));
            let var = builder.alloc_with_value(byte_value_fr)?;
            crate::gadgets::range::enforce_recompose_equals(builder, &byte.bits, var)?;
            out_vars.push(var);
        }
        prev = ct_block;
    }
    Ok(out_vars)
}

/// Decompose a byte-valued `Variable` into 8 boolean wires and return a
/// `Byte`. The decomposition also enforces the 8-bit range check on `var`.
fn decompose_byte(
    builder: &mut R1csBuilder<'_>,
    var: Variable,
    value: Option<Fr>,
) -> Result<Byte, SynthesisError> {
    let bit_vars = decompose_into_bits(builder, var, 8, value)?;
    let bits: [LinearCombination<Fr>; 8] =
        std::array::from_fn(|i| LinearCombination(vec![(Fr::one(), bit_vars[i])]));
    let value_u8 = value.map(fr_to_u8_low);
    Ok(Byte::from_bit_lcs(bits, value_u8))
}

/// Truncate an `Fr` to its low 8 bits. Bytes are range-checked elsewhere; this
/// just safely takes the LSB.
fn fr_to_u8_low(fr: Fr) -> u8 {
    let bytes = crate::field::fr_to_be_bytes(&fr);
    bytes[31]
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::WitnessMap;
    use aes::cipher::{BlockModeEncrypt, KeyIvInit, block_padding::NoPadding};
    use ark_relations::gr1cs::ConstraintSystem;
    use rand::Rng;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    type Aes128CbcEnc = cbc::Encryptor<aes::Aes128>;

    fn aes_crate_cbc(plaintext: &[u8], iv: &[u8; 16], key: &[u8; 16]) -> Vec<u8> {
        let mut buf = plaintext.to_vec();
        let len = plaintext.len();
        Aes128CbcEnc::new(key.into(), iv.into())
            .encrypt_padded::<NoPadding>(&mut buf, len)
            .expect("aes crate: input block-aligned");
        buf
    }

    fn alloc_byte(builder: &mut R1csBuilder<'_>, value: u8) -> (Variable, Option<Fr>) {
        let fr = Fr::from(value as u64);
        let v = builder.alloc_with_value(Some(fr)).unwrap();
        (v, Some(fr))
    }

    fn byte_var_value(cs: &ark_relations::gr1cs::ConstraintSystemRef<Fr>, v: Variable) -> u8 {
        let fr = cs.assigned_value(v).expect("variable has an assignment");
        fr_to_u8_low(fr)
    }

    #[test]
    fn aes_native_matches_aes_crate_on_fips197_kat() {
        // FIPS 197 Appendix B KAT (single block ECB; with all-zero IV this also
        // matches the first block of CBC since prev ^ pt = pt).
        let plaintext = hex::decode("3243f6a8885a308d313198a2e0370734").unwrap();
        let key = hex::decode("2b7e151628aed2a6abf7158809cf4f3c").unwrap();
        let expected_ct = hex::decode("3925841d02dc09fbdc118597196a0b32").unwrap();

        let mut pt16 = [0u8; 16];
        pt16.copy_from_slice(&plaintext);
        let mut key16 = [0u8; 16];
        key16.copy_from_slice(&key);
        let got = aes128_block_encrypt_native(&pt16, &key16);
        assert_eq!(&got[..], &expected_ct[..], "AES-128 ECB KAT failed");

        // Cross-check vs `aes` crate's CBC mode with zero IV.
        let iv = [0u8; 16];
        let cbc_got = aes_crate_cbc(&plaintext, &iv, &key16);
        let our_cbc = aes128_encrypt_native(&plaintext, &iv, &key16);
        assert_eq!(cbc_got, our_cbc, "aes crate vs native CBC disagree");
    }

    #[test]
    fn aes_in_circuit_matches_native_on_kat() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let plaintext_bytes = hex::decode("3243f6a8885a308d313198a2e0370734").unwrap();
        let key_bytes_vec = hex::decode("2b7e151628aed2a6abf7158809cf4f3c").unwrap();
        let mut key_bytes = [0u8; 16];
        key_bytes.copy_from_slice(&key_bytes_vec);
        let iv_bytes = [0u8; 16];

        let pt_vars: Vec<(Variable, Option<Fr>)> = plaintext_bytes
            .iter()
            .map(|&byte| alloc_byte(&mut b, byte))
            .collect();
        let iv_vars: [(Variable, Option<Fr>); 16] =
            std::array::from_fn(|i| alloc_byte(&mut b, iv_bytes[i]));
        let key_vars: [(Variable, Option<Fr>); 16] =
            std::array::from_fn(|i| alloc_byte(&mut b, key_bytes[i]));

        let out = aes128_encrypt_in_circuit(&mut b, &pt_vars, &iv_vars, &key_vars).unwrap();
        assert!(cs.is_satisfied().unwrap(), "constraint system unsatisfied");
        assert_eq!(out.len(), 16);

        let expected = aes128_encrypt_native(&plaintext_bytes, &iv_bytes, &key_bytes);
        for i in 0..16 {
            let got = byte_var_value(&cs, out[i]);
            assert_eq!(got, expected[i], "byte {i} mismatch");
        }
        println!(
            "AES-128 (16-byte input): {} constraints, {} witnesses",
            cs.num_constraints(),
            cs.num_witness_variables()
        );
    }

    #[test]
    fn aes_in_circuit_random_block() {
        let mut rng = StdRng::seed_from_u64(0xAE5_F00D);
        let plaintext: [u8; 16] = rng.r#gen();
        let key: [u8; 16] = rng.r#gen();
        let iv: [u8; 16] = rng.r#gen();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let pt_vars: Vec<(Variable, Option<Fr>)> = plaintext
            .iter()
            .map(|&byte| alloc_byte(&mut b, byte))
            .collect();
        let iv_vars: [(Variable, Option<Fr>); 16] =
            std::array::from_fn(|i| alloc_byte(&mut b, iv[i]));
        let key_vars: [(Variable, Option<Fr>); 16] =
            std::array::from_fn(|i| alloc_byte(&mut b, key[i]));

        let out = aes128_encrypt_in_circuit(&mut b, &pt_vars, &iv_vars, &key_vars).unwrap();
        assert!(cs.is_satisfied().unwrap());

        let expected_native = aes128_encrypt_native(&plaintext, &iv, &key);
        let expected_crate = aes_crate_cbc(&plaintext, &iv, &key);
        assert_eq!(expected_native, expected_crate, "native vs aes crate");
        for i in 0..16 {
            let got = byte_var_value(&cs, out[i]);
            assert_eq!(got, expected_native[i], "byte {i} mismatch");
        }
    }

    #[test]
    fn aes_in_circuit_two_block_cbc() {
        // 32 bytes of plaintext exercises CBC chaining (block 2 XORs with
        // ciphertext block 1 before encryption).
        let mut rng = StdRng::seed_from_u64(0x0002_B10C_5C8C);
        let plaintext: [u8; 32] = rng.r#gen();
        let key: [u8; 16] = rng.r#gen();
        let iv: [u8; 16] = rng.r#gen();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let pt_vars: Vec<(Variable, Option<Fr>)> = plaintext
            .iter()
            .map(|&byte| alloc_byte(&mut b, byte))
            .collect();
        let iv_vars: [(Variable, Option<Fr>); 16] =
            std::array::from_fn(|i| alloc_byte(&mut b, iv[i]));
        let key_vars: [(Variable, Option<Fr>); 16] =
            std::array::from_fn(|i| alloc_byte(&mut b, key[i]));

        let out = aes128_encrypt_in_circuit(&mut b, &pt_vars, &iv_vars, &key_vars).unwrap();
        assert!(cs.is_satisfied().unwrap());

        let expected = aes_crate_cbc(&plaintext, &iv, &key);
        assert_eq!(out.len(), 32);
        for i in 0..32 {
            let got = byte_var_value(&cs, out[i]);
            assert_eq!(got, expected[i], "byte {i} mismatch (CBC two-block)");
        }
    }

    #[test]
    fn gf256_inv_roundtrips() {
        for x in 1u8..=255 {
            let inv = gf256_inv(x);
            assert_eq!(gf256_mul(x, inv), 1, "inv({x}) wrong");
        }
        assert_eq!(gf256_inv(0), 0);
    }

    #[test]
    fn sbox_all_inputs_match_table() {
        // For every byte x, the in-circuit S-box should produce SBOX[x].
        for x in 0u8..=255 {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let map = WitnessMap::<Fr>::new();
            let mut b = R1csBuilder::new(cs.clone(), Some(&map));
            b.finish_public_pass();

            let (v, val) = alloc_byte(&mut b, x);
            let input = decompose_byte(&mut b, v, val).unwrap();
            let out = s_box_in_circuit(&mut b, &input).unwrap();
            assert!(
                cs.is_satisfied().unwrap(),
                "S-box constraints unsatisfied at x={x:#x}"
            );
            assert_eq!(out.value, Some(SBOX[x as usize]), "S-box value at x={x:#x}");
        }
    }

    #[test]
    fn sbox_zero_input_special_case() {
        // S(0) must equal 0x63 (FIPS 197 §5.1.1 — the affine transform of 0).
        assert_eq!(SBOX[0], 0x63);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let (v, val) = alloc_byte(&mut b, 0);
        let input = decompose_byte(&mut b, v, val).unwrap();
        let out = s_box_in_circuit(&mut b, &input).unwrap();
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(out.value, Some(0x63));
    }
}
