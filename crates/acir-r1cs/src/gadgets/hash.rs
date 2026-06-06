//! SHA-256 compression gadget.
//!
//! Implements the NIST FIPS 180-4 SHA-256 compression function `F` so that
//! given a 16-word message block and 8-word state, we produce 8-word
//! `state' = F(state, block)`.
//!
//! This is what Noir emits as `BlackBoxFuncCall::Sha256Compression` and is
//! the building block used by every higher-level SHA-256 wrapper.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_relations::gr1cs::{LinearCombination, SynthesisError, Variable};

use crate::gadgets::bitwise::{Word32, add_mod_32, and, not, rotr, shr, xor};
use crate::gadgets::range::decompose_into_bits;
use crate::r1cs_builder::R1csBuilder;

/// SHA-256 round constants (first 32 bits of fractional parts of cube roots
/// of the first 64 primes).
pub const K256: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Decompose a single u32 value variable into a [`Word32`] with all bits as
/// freshly-allocated boolean variables.
pub fn word32_from_value_var(
    builder: &mut R1csBuilder<'_>,
    value_var: Variable,
    value: Option<Fr>,
) -> Result<Word32, SynthesisError> {
    let bits = decompose_into_bits(builder, value_var, 32, value)?;
    let u32_value = value.map(fr_to_u32);
    Ok(Word32::from_decomposed(bits, u32_value))
}

/// SHA-256 compression: produces 8 output words from 16 message words and an
/// 8-word state. Returns the new 8-word state.
pub fn sha256_compression(
    builder: &mut R1csBuilder<'_>,
    input: &[Word32; 16],
    state: &[Word32; 8],
) -> Result<[Word32; 8], SynthesisError> {
    // -- Message schedule W[0..64] ------------------------------------------
    let mut w: Vec<Word32> = Vec::with_capacity(64);
    for word in input.iter() {
        w.push(word.clone());
    }
    for i in 16..64 {
        // σ0(x) = ROTR(x,7) XOR ROTR(x,18) XOR SHR(x,3)
        let s0 = xor_triple(
            builder,
            &rotr(&w[i - 15], 7),
            &rotr(&w[i - 15], 18),
            &shr(&w[i - 15], 3),
        )?;
        // σ1(x) = ROTR(x,17) XOR ROTR(x,19) XOR SHR(x,10)
        let s1 = xor_triple(
            builder,
            &rotr(&w[i - 2], 17),
            &rotr(&w[i - 2], 19),
            &shr(&w[i - 2], 10),
        )?;
        let next = add_mod_32(builder, &[&w[i - 16], &s0, &w[i - 7], &s1])?;
        w.push(next);
    }

    // -- Working state ------------------------------------------------------
    let mut a = state[0].clone();
    let mut b = state[1].clone();
    let mut c = state[2].clone();
    let mut d = state[3].clone();
    let mut e = state[4].clone();
    let mut f = state[5].clone();
    let mut g = state[6].clone();
    let mut h = state[7].clone();

    for i in 0..64 {
        // Σ1(e) = ROTR(e,6) XOR ROTR(e,11) XOR ROTR(e,25)
        let big_sigma1 = xor_triple(builder, &rotr(&e, 6), &rotr(&e, 11), &rotr(&e, 25))?;
        // Ch(e,f,g) = (e AND f) XOR (NOT e AND g)
        let ch = {
            let e_and_f = and(builder, &e, &f)?;
            let not_e_and_g = and(builder, &not(&e), &g)?;
            xor(builder, &e_and_f, &not_e_and_g)?
        };
        let k_word = Word32::constant(K256[i]);
        // T1 = h + Σ1(e) + Ch + K[i] + W[i]
        let t1 = add_mod_32(builder, &[&h, &big_sigma1, &ch, &k_word, &w[i]])?;

        // Σ0(a) = ROTR(a,2) XOR ROTR(a,13) XOR ROTR(a,22)
        let big_sigma0 = xor_triple(builder, &rotr(&a, 2), &rotr(&a, 13), &rotr(&a, 22))?;
        // Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c)
        let maj = {
            let a_and_b = and(builder, &a, &b)?;
            let a_and_c = and(builder, &a, &c)?;
            let b_and_c = and(builder, &b, &c)?;
            xor_triple(builder, &a_and_b, &a_and_c, &b_and_c)?
        };
        // T2 = Σ0 + Maj
        let t2 = add_mod_32(builder, &[&big_sigma0, &maj])?;

        // Rotate working state.
        h = g.clone();
        g = f.clone();
        f = e.clone();
        e = add_mod_32(builder, &[&d, &t1])?;
        d = c.clone();
        c = b.clone();
        b = a.clone();
        a = add_mod_32(builder, &[&t1, &t2])?;
    }

    // -- Final: state[i] + working[i] mod 2^32 ------------------------------
    Ok([
        add_mod_32(builder, &[&state[0], &a])?,
        add_mod_32(builder, &[&state[1], &b])?,
        add_mod_32(builder, &[&state[2], &c])?,
        add_mod_32(builder, &[&state[3], &d])?,
        add_mod_32(builder, &[&state[4], &e])?,
        add_mod_32(builder, &[&state[5], &f])?,
        add_mod_32(builder, &[&state[6], &g])?,
        add_mod_32(builder, &[&state[7], &h])?,
    ])
}

/// Batched 3-input XOR `a XOR b XOR c` on 32-bit words. Replaces the
/// chained `xor(xor(a, b), c)` formulation with the parity identity
/// `a_i + b_i + c_i = out_i + 2·k_i`, where `k_i ∈ {0, 1}` is a single
/// auxiliary carry bit per bit position. Cost per bit drops from
/// `2 · 2 = 4` (two binary XORs) to `3` (one out boolean + one k
/// boolean + one linear). Saves ~14% on SHA-256 compression across the
/// 288 `xor_triple` call sites in the round + message-schedule loops.
fn xor_triple(
    builder: &mut R1csBuilder<'_>,
    a: &Word32,
    b: &Word32,
    c: &Word32,
) -> Result<Word32, SynthesisError> {
    use crate::gadgets::boolean::enforce_boolean;
    let out_value = match (a.value, b.value, c.value) {
        (Some(av), Some(bv), Some(cv)) => Some(av ^ bv ^ cv),
        _ => None,
    };
    let mut out_bits: Vec<LinearCombination<Fr>> = Vec::with_capacity(32);
    for i in 0..32 {
        let av = a.value.map(|v| (v >> i) & 1);
        let bv = b.value.map(|v| (v >> i) & 1);
        let cv = c.value.map(|v| (v >> i) & 1);
        let sum_val: Option<u32> = match (av, bv, cv) {
            (Some(x), Some(y), Some(z)) => Some(x + y + z),
            _ => None,
        };
        let out_bit_val = sum_val.map(|s| if s & 1 == 1 { Fr::one() } else { Fr::zero() });
        let out_var = builder.alloc_with_value(out_bit_val)?;
        enforce_boolean(builder, out_var)?;

        // Carry k ∈ {0, 1}: floor((a + b + c) / 2). For 3 boolean inputs
        // the sum is in [0, 3], so the carry is exactly one bit.
        let k_val = sum_val.map(|s| if s >> 1 == 1 { Fr::one() } else { Fr::zero() });
        let k_var = builder.alloc_with_value(k_val)?;
        enforce_boolean(builder, k_var)?;

        // a_i + b_i + c_i − out − 2·k = 0.
        let two = Fr::one() + Fr::one();
        let mut lc: Vec<(Fr, Variable)> = Vec::new();
        for (coef, var) in a.bits[i].0.iter() {
            lc.push((*coef, *var));
        }
        for (coef, var) in b.bits[i].0.iter() {
            lc.push((*coef, *var));
        }
        for (coef, var) in c.bits[i].0.iter() {
            lc.push((*coef, *var));
        }
        lc.push((-Fr::one(), out_var));
        lc.push((-two, k_var));
        builder.enforce(builder.zero_lc(), builder.zero_lc(), LinearCombination(lc))?;

        out_bits.push(LinearCombination(vec![(Fr::one(), out_var)]));
    }
    Ok(Word32::from_bits(out_bits, out_value))
}

/// Convert a known `Fr` (assumed to fit in 32 bits) into a `u32` for tracking.
pub fn fr_to_u32(fr: Fr) -> u32 {
    use crate::field::fr_to_be_bytes;
    let bytes = fr_to_be_bytes(&fr);
    let mut out = 0u32;
    for &b in &bytes[28..32] {
        out = (out << 8) | b as u32;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::WitnessMap;
    use ark_ff::One;
    use ark_relations::gr1cs::ConstraintSystem;
    use sha2::block_api::compress256;

    fn alloc_word_with_bits(builder: &mut R1csBuilder<'_>, value: u32) -> Word32 {
        let mut bit_vars = Vec::with_capacity(32);
        for i in 0..32 {
            let bv = Some(if ((value >> i) & 1) == 1 {
                Fr::one()
            } else {
                ark_ff::Zero::zero()
            });
            let v = builder.alloc_with_value(bv).unwrap();
            crate::gadgets::boolean::enforce_boolean(builder, v).unwrap();
            bit_vars.push(v);
        }
        Word32::from_decomposed(bit_vars, Some(value))
    }

    #[test]
    fn compression_matches_sha2_crate_on_abc_block() {
        // Padded "abc" message: single 512-bit block.
        let mut block = [0u8; 64];
        block[0..3].copy_from_slice(b"abc");
        block[3] = 0x80;
        // length in bits = 24, big-endian in last 8 bytes.
        block[63] = 24;

        // Reference: sha2 0.11's compress256 takes a slice of `[u8; 64]`.
        let mut state = [
            0x6a09e667u32,
            0xbb67ae85,
            0x3c6ef372,
            0xa54ff53a,
            0x510e527f,
            0x9b05688c,
            0x1f83d9ab,
            0x5be0cd19,
        ];
        compress256(&mut state, &[block]);

        let expected = state;
        // SHA-256("abc") canonical: ba7816bf 8f01cfea 414140de 5dae2223
        // b00361a3 96177a9c b410ff61 f20015ad
        assert_eq!(expected[0], 0xba7816bf);
        assert_eq!(expected[7], 0xf20015ad);

        // Now run through our gadget.
        let mut block_words = [0u32; 16];
        for (i, w) in block_words.iter_mut().enumerate() {
            *w = u32::from_be_bytes(block[i * 4..i * 4 + 4].try_into().unwrap());
        }
        let iv = [
            0x6a09e667u32,
            0xbb67ae85,
            0x3c6ef372,
            0xa54ff53a,
            0x510e527f,
            0x9b05688c,
            0x1f83d9ab,
            0x5be0cd19,
        ];

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let input: [Word32; 16] =
            std::array::from_fn(|i| alloc_word_with_bits(&mut b, block_words[i]));
        let state_in: [Word32; 8] = std::array::from_fn(|i| alloc_word_with_bits(&mut b, iv[i]));

        let out = sha256_compression(&mut b, &input, &state_in).unwrap();

        for i in 0..8 {
            assert_eq!(
                out[i].value,
                Some(expected[i]),
                "word {i} mismatch: got {:08x} want {:08x}",
                out[i].value.unwrap(),
                expected[i]
            );
        }

        // The full constraint system must be satisfied.
        assert!(cs.is_satisfied().unwrap(), "constraint system unsatisfied");
        println!("SHA-256 compression: {} constraints", cs.num_constraints());
    }
}
