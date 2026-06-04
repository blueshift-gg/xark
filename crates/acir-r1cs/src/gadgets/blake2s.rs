//! Blake2s compression + padding gadget (ROADMAP step **WS-D.2**).
//!
//! Implements the RFC 7693 Blake2s hash on a **variable-length byte input**
//! producing a 32-byte digest. Used by Noir's `BlackBoxFuncCall::Blake2s`.
//!
//! ## Design
//!
//! Blake2s operates on **32-bit little-endian words**. The input is split into
//! 64-byte blocks; the last block is right-padded with zero bytes. A 64-bit
//! byte counter `t` advances by the **bytes consumed so far** (NOT
//! zero-padded count) on each compression call. The last block sets the
//! finalization flag `f0 = 0xFFFFFFFF` (XOR'd into `v[14]`).
//!
//! For an unkeyed 32-byte digest (the only mode Noir emits) the initial state
//! is `h[0..8] = IV[0..8]` with `h[0] ^= 0x01010020` (parameter block:
//! depth=1, fanout=1, key length=0, digest length=32).
//!
//! ### What's data-independent at circuit-compile time
//!
//! The input **length** is fixed at compile time (it's a `Vec<FunctionInput>`
//! whose length is baked into the ACIR opcode). Therefore the byte counter
//! `t` per block, the number of blocks, and the final-block flag are all
//! constants — no constraints needed for that bookkeeping.
//!
//! ### Bit packing strategy
//!
//! Each input byte is range-decomposed into 8 boolean wires (LSB-first). For
//! every 32-bit message word `m[j]`, we pack the bits of the 4 consecutive
//! bytes covering it directly into a `Word32` (LSB of `m[j]` = LSB of byte
//! `4j`; bit 8 of `m[j]` = LSB of byte `4j+1`; …). This avoids a recompose +
//! redecompose roundtrip per byte. Bytes past the input length are zero
//! (constant `0` LCs), so the last (partial) block packs zero-bit LCs for the
//! tail.
//!
//! ### Mixing function G(a, b, c, d, x, y)
//!
//! ```text
//! v[a] = v[a] + v[b] + x
//! v[d] = (v[d] XOR v[a]) >>> 16
//! v[c] = v[c] + v[d]
//! v[b] = (v[b] XOR v[c]) >>> 12
//! v[a] = v[a] + v[b] + y
//! v[d] = (v[d] XOR v[a]) >>> 8
//! v[c] = v[c] + v[d]
//! v[b] = (v[b] XOR v[c]) >>> 7
//! ```
//!
//! Per round we run 8 calls to G (4 columns + 4 diagonals). Each G has 4
//! `add_mod_32`s and 4 XOR-then-rotr operations. Rotations are free (pure
//! index permutations on `Word32`).
//!
//! Per compression call: 10 rounds × 8 G = 80 mixing operations, so
//! 320 `add_mod_32` (32 bool wires + 1 lin eq + 2 carry bits ≈ 35 constraints
//! each) and 320 XOR + rotates (32 constraints each) ≈ 21–24k constraints per
//! 64-byte block, plus bit-decomposition of each input byte (8 constraints).

#![allow(clippy::needless_range_loop)]

use ark_bn254::Fr;
use ark_ff::One;
use ark_relations::r1cs::{LinearCombination, SynthesisError, Variable};

use crate::gadgets::bitwise::{add_mod_32, xor, Word32};
use crate::gadgets::range::{decompose_into_bits, enforce_recompose_equals};
use crate::r1cs_builder::R1csBuilder;

/// Blake2s initialization vector (FIPS-aligned IV from RFC 7693 §2.6 —
/// identical to the first 32 bits of the fractional parts of the square roots
/// of the first eight primes, which SHA-256 uses too).
pub const BLAKE2S_IV: [u32; 8] = [
    0x6A09_E667,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

/// Per-round message-word permutation σ (10 rounds × 16 indices). RFC 7693
/// §2.7 / Table 2.
pub const BLAKE2S_SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

/// G-mixing rotation constants (RFC 7693 §2.1) — right-rotation amounts.
const R1: usize = 16;
const R2: usize = 12;
const R3: usize = 8;
const R4: usize = 7;

/// Number of compression rounds.
const ROUNDS: usize = 10;

/// Block size in bytes.
const BLOCK_BYTES: usize = 64;

/// Digest size in bytes (Blake2s always — Noir only emits 32-byte outputs).
const DIGEST_BYTES: usize = 32;

/// Parameter-block XOR applied to `h[0]` for an unkeyed 32-byte digest:
/// `0x0101_kknn` with `kk = 0` (no key) and `nn = 32` (digest length).
const PARAM_BLOCK_H0_XOR: u32 = 0x0101_0020;

// =============================================================================
// Native reference (used by KAT + setup-mode value tracking)
// =============================================================================

/// Native Blake2s implementation. Used by the gadget at proving time to
/// track concrete intermediate values, and by the KAT test to cross-check
/// the gadget against the `blake2` crate.
pub fn blake2s_native(input: &[u8]) -> [u8; 32] {
    let mut h = BLAKE2S_IV;
    h[0] ^= PARAM_BLOCK_H0_XOR;

    let n = input.len();
    // Number of complete blocks before the final block. The final block is
    // always processed separately so we can apply the finalization flag.
    let full_blocks = if n == 0 { 0 } else { (n - 1) / BLOCK_BYTES };

    for i in 0..full_blocks {
        let start = i * BLOCK_BYTES;
        let t = (start + BLOCK_BYTES) as u64;
        let mut block = [0u8; BLOCK_BYTES];
        block.copy_from_slice(&input[start..start + BLOCK_BYTES]);
        let m = block_to_words(&block);
        compress_native(&mut h, &m, t, false);
    }

    // Final block.
    let mut block = [0u8; BLOCK_BYTES];
    let tail_start = full_blocks * BLOCK_BYTES;
    let tail_len = n - tail_start;
    block[..tail_len].copy_from_slice(&input[tail_start..]);
    let t = n as u64;
    let m = block_to_words(&block);
    compress_native(&mut h, &m, t, true);

    let mut out = [0u8; DIGEST_BYTES];
    for (i, w) in h.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&w.to_le_bytes());
    }
    out
}

fn block_to_words(block: &[u8; BLOCK_BYTES]) -> [u32; 16] {
    let mut m = [0u32; 16];
    for j in 0..16 {
        m[j] = u32::from_le_bytes(block[j * 4..j * 4 + 4].try_into().unwrap());
    }
    m
}

fn compress_native(h: &mut [u32; 8], m: &[u32; 16], t: u64, last_block: bool) {
    let mut v = [0u32; 16];
    v[0..8].copy_from_slice(h);
    v[8..16].copy_from_slice(&BLAKE2S_IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    if last_block {
        v[14] ^= 0xFFFF_FFFFu32;
    }

    for r in 0..ROUNDS {
        let s = &BLAKE2S_SIGMA[r];
        mix_native(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        mix_native(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        mix_native(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        mix_native(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);

        mix_native(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        mix_native(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        mix_native(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        mix_native(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }

    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

#[inline]
fn mix_native(v: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, x: u32, y: u32) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(R1 as u32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(R2 as u32);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(R3 as u32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(R4 as u32);
}

// =============================================================================
// In-circuit gadget
// =============================================================================

/// Run Blake2s on `input_vars` (each is a u8-valued `(Variable, Option<Fr>)`
/// pair). Returns 32 freshly-allocated witness `Variable`s, each holding one
/// output byte and bound via a single linear equality to its bit
/// decomposition. The byte counter, padding, and finalization flag are all
/// derived from `input_vars.len()` at circuit-build time, so they incur no
/// constraints of their own.
pub fn blake2s_in_circuit(
    builder: &mut R1csBuilder<'_>,
    input_vars: &[(Variable, Option<Fr>)],
) -> Result<[Variable; DIGEST_BYTES], SynthesisError> {
    // -- 1. Decompose every input byte into 8 boolean wires. -------------------
    //
    // Each byte `Variable` gets bit-decomposed (LSB first). The decomposition
    // also gives us the implicit 8-bit range check for free — equivalent to
    // the RANGE opcode that Noir emits for `u8`-typed witnesses anyway.
    let n = input_vars.len();
    let mut byte_bits: Vec<[Variable; 8]> = Vec::with_capacity(n);
    let mut byte_values: Vec<Option<u8>> = Vec::with_capacity(n);
    for (var, value) in input_vars.iter() {
        let bits = decompose_into_bits(builder, *var, 8, *value)?;
        let bits_arr: [Variable; 8] = std::array::from_fn(|i| bits[i]);
        byte_bits.push(bits_arr);
        byte_values.push(value.map(fr_to_u8_low));
    }

    // -- 2. Initialise state h = IV with the parameter block XOR'd into h[0]. --
    //
    // h[i] starts as a constant `Word32`; subsequent compressions replace it
    // with full-width words. Held as in-circuit `Word32`s the whole way.
    let mut h: [Word32; 8] = std::array::from_fn(|i| {
        let mut iv_i = BLAKE2S_IV[i];
        if i == 0 {
            iv_i ^= PARAM_BLOCK_H0_XOR;
        }
        Word32::constant(iv_i)
    });

    // -- 3. Iterate over 64-byte blocks. ---------------------------------------
    //
    // The final block always runs with `last_block = true`. For empty input,
    // we still process a single all-zero block per RFC 7693 §3.3.
    let full_blocks = if n == 0 { 0 } else { (n - 1) / BLOCK_BYTES };
    for block_idx in 0..full_blocks {
        let m = pack_block_message(&byte_bits, &byte_values, block_idx * BLOCK_BYTES, n);
        let t = ((block_idx + 1) * BLOCK_BYTES) as u64;
        h = compress_in_circuit(builder, &h, &m, t, false)?;
    }
    {
        let tail_start = full_blocks * BLOCK_BYTES;
        let m = pack_block_message(&byte_bits, &byte_values, tail_start, n);
        let t = n as u64;
        h = compress_in_circuit(builder, &h, &m, t, true)?;
    }

    // -- 4. Output: 8 LE u32 words -> 32 bytes, allocated as witness vars. -----
    //
    // For each output word we already have a `Word32` with a full bit
    // decomposition. To emit individual bytes we re-pack groups of 8 bits,
    // allocate a fresh byte witness, and pin it via a single linear
    // recomposition constraint.
    let mut out_bytes = [Variable::One; DIGEST_BYTES];
    for word_idx in 0..8 {
        let word = &h[word_idx];
        for byte_in_word in 0..4 {
            let bit_start = byte_in_word * 8;
            let byte_lcs: Vec<LinearCombination<Fr>> =
                (0..8).map(|b| word.bits[bit_start + b].clone()).collect();
            let byte_value = word.value.map(|w| ((w >> bit_start) & 0xFF) as u8);
            let byte_fr = byte_value.map(|b| Fr::from(b as u64));
            let byte_var = builder.alloc_with_value(byte_fr)?;
            enforce_recompose_equals(builder, &byte_lcs, byte_var)?;
            out_bytes[word_idx * 4 + byte_in_word] = byte_var;
        }
    }

    Ok(out_bytes)
}

/// Build the 16 32-bit message words for a single 64-byte block.
///
/// Each message word `m[j]` is constructed from the bits of bytes
/// `[block_start + 4j .. block_start + 4j + 4]`. Bytes past the input length
/// `n` are zero-padded with the constant-zero LC (`LinearCombination(vec![])`).
fn pack_block_message(
    byte_bits: &[[Variable; 8]],
    byte_values: &[Option<u8>],
    block_start: usize,
    n: usize,
) -> [Word32; 16] {
    std::array::from_fn(|j| {
        let mut bit_lcs: Vec<LinearCombination<Fr>> = Vec::with_capacity(32);
        let mut known_value: Option<u32> = Some(0);
        for byte_in_word in 0..4 {
            let byte_idx = block_start + j * 4 + byte_in_word;
            if byte_idx < n {
                for bit in 0..8 {
                    let v = byte_bits[byte_idx][bit];
                    bit_lcs.push(LinearCombination(vec![(Fr::one(), v)]));
                }
                if let Some(b) = byte_values[byte_idx] {
                    if let Some(acc) = known_value.as_mut() {
                        *acc |= (b as u32) << (8 * byte_in_word);
                    }
                } else {
                    known_value = None;
                }
            } else {
                for _ in 0..8 {
                    bit_lcs.push(LinearCombination(vec![]));
                }
            }
        }
        Word32::from_bits(bit_lcs, known_value)
    })
}

/// One Blake2s compression-function call. Returns the updated 8-word state.
fn compress_in_circuit(
    builder: &mut R1csBuilder<'_>,
    h: &[Word32; 8],
    m: &[Word32; 16],
    t: u64,
    last_block: bool,
) -> Result<[Word32; 8], SynthesisError> {
    // Local working state v[0..16].
    let mut v: Vec<Word32> = Vec::with_capacity(16);
    for word in h.iter() {
        v.push(word.clone());
    }
    for &iv_i in BLAKE2S_IV.iter() {
        v.push(Word32::constant(iv_i));
    }
    // XOR t (low/high) into v[12] / v[13]. Constants — no fresh constraints
    // beyond the XOR itself, which materialises a fresh witness per bit.
    let t_lo = t as u32;
    let t_hi = (t >> 32) as u32;
    v[12] = xor(builder, &v[12], &Word32::constant(t_lo))?;
    v[13] = xor(builder, &v[13], &Word32::constant(t_hi))?;
    if last_block {
        v[14] = xor(builder, &v[14], &Word32::constant(0xFFFF_FFFFu32))?;
    }

    for r in 0..ROUNDS {
        let s = &BLAKE2S_SIGMA[r];
        mix_in_circuit(builder, &mut v, 0, 4, 8, 12, &m[s[0]], &m[s[1]])?;
        mix_in_circuit(builder, &mut v, 1, 5, 9, 13, &m[s[2]], &m[s[3]])?;
        mix_in_circuit(builder, &mut v, 2, 6, 10, 14, &m[s[4]], &m[s[5]])?;
        mix_in_circuit(builder, &mut v, 3, 7, 11, 15, &m[s[6]], &m[s[7]])?;

        mix_in_circuit(builder, &mut v, 0, 5, 10, 15, &m[s[8]], &m[s[9]])?;
        mix_in_circuit(builder, &mut v, 1, 6, 11, 12, &m[s[10]], &m[s[11]])?;
        mix_in_circuit(builder, &mut v, 2, 7, 8, 13, &m[s[12]], &m[s[13]])?;
        mix_in_circuit(builder, &mut v, 3, 4, 9, 14, &m[s[14]], &m[s[15]])?;
    }

    // h'[i] = h[i] XOR v[i] XOR v[i+8].
    let mut out: Vec<Word32> = Vec::with_capacity(8);
    for i in 0..8 {
        let lo = xor(builder, &h[i], &v[i])?;
        let full = xor(builder, &lo, &v[i + 8])?;
        out.push(full);
    }
    Ok(out.try_into().unwrap_or_else(|_| unreachable!()))
}

/// In-circuit G mixing function.
#[allow(clippy::too_many_arguments)]
fn mix_in_circuit(
    builder: &mut R1csBuilder<'_>,
    v: &mut [Word32],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: &Word32,
    y: &Word32,
) -> Result<(), SynthesisError> {
    // v[a] = v[a] + v[b] + x
    v[a] = add_mod_32(builder, &[&v[a], &v[b], x])?;
    // v[d] = (v[d] XOR v[a]) >>> R1
    v[d] = rotr_w32(&xor(builder, &v[d], &v[a])?, R1);
    // v[c] = v[c] + v[d]
    v[c] = add_mod_32(builder, &[&v[c], &v[d]])?;
    // v[b] = (v[b] XOR v[c]) >>> R2
    v[b] = rotr_w32(&xor(builder, &v[b], &v[c])?, R2);
    // v[a] = v[a] + v[b] + y
    v[a] = add_mod_32(builder, &[&v[a], &v[b], y])?;
    // v[d] = (v[d] XOR v[a]) >>> R3
    v[d] = rotr_w32(&xor(builder, &v[d], &v[a])?, R3);
    // v[c] = v[c] + v[d]
    v[c] = add_mod_32(builder, &[&v[c], &v[d]])?;
    // v[b] = (v[b] XOR v[c]) >>> R4
    v[b] = rotr_w32(&xor(builder, &v[b], &v[c])?, R4);
    Ok(())
}

/// Right rotation of a `Word32`: thin wrapper around the bitwise `rotr` helper
/// (kept inline here so we don't add yet another import).
fn rotr_w32(a: &Word32, k: usize) -> Word32 {
    crate::gadgets::bitwise::rotr(a, k)
}

/// Truncate an `Fr` to its low 8 bits. The caller passes byte-valued witnesses
/// (range-checked elsewhere or via `decompose_into_bits` later), so the high
/// bytes are zero in practice; we just take the LSB safely.
fn fr_to_u8_low(fr: Fr) -> u8 {
    // BE bytes; the LSB is the last byte.
    let bytes = crate::field::fr_to_be_bytes(&fr);
    bytes[31]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::WitnessMap;
    use ark_relations::r1cs::ConstraintSystem;
    use blake2::{Blake2s256, Digest};
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    /// Expected `blake2s(b"abc")` digest from RFC 7693 / `blake2` crate.
    const ABC_DIGEST_HEX: &str = "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982";

    fn alloc_byte(builder: &mut R1csBuilder<'_>, value: u8) -> (Variable, Option<Fr>) {
        let fr = Fr::from(value as u64);
        let v = builder.alloc_with_value(Some(fr)).unwrap();
        (v, Some(fr))
    }

    fn byte_var_value(cs: &ark_relations::r1cs::ConstraintSystemRef<Fr>, v: Variable) -> u8 {
        let fr = match v {
            Variable::Witness(idx) => cs.borrow().unwrap().witness_assignment[idx],
            Variable::One => Fr::one(),
            _ => panic!("byte_var_value: not a witness or one"),
        };
        fr_to_u8_low(fr)
    }

    #[test]
    fn blake2s_native_matches_blake2_crate_on_abc() {
        let got = blake2s_native(b"abc");
        let mut hasher = Blake2s256::new();
        hasher.update(b"abc");
        let want: [u8; 32] = hasher.finalize().into();
        assert_eq!(got, want);
        assert_eq!(hex::encode(got), ABC_DIGEST_HEX);
    }

    #[test]
    fn blake2s_native_matches_blake2_crate_random_lengths() {
        let mut rng = StdRng::seed_from_u64(0xB2_5B_25_00);
        // Cover empty, sub-block, exact-block, two-block, and just-past-two-block
        // edge cases to exercise the padding logic.
        for &len in &[0usize, 1, 17, 55, 56, 63, 64, 65, 100, 128, 129] {
            let input: Vec<u8> = (0..len).map(|_| rng.gen()).collect();
            let got = blake2s_native(&input);
            let mut hasher = Blake2s256::new();
            hasher.update(&input);
            let want: [u8; 32] = hasher.finalize().into();
            assert_eq!(got, want, "blake2s_native mismatch at len={len}");
        }
    }

    #[test]
    fn blake2s_in_circuit_matches_native_on_abc() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let input = b"abc";
        let in_vars: Vec<(Variable, Option<Fr>)> =
            input.iter().map(|&byte| alloc_byte(&mut b, byte)).collect();

        let out = blake2s_in_circuit(&mut b, &in_vars).unwrap();

        assert!(cs.is_satisfied().unwrap(), "constraint system unsatisfied");

        let expected = blake2s_native(input);
        for i in 0..DIGEST_BYTES {
            let got = byte_var_value(&cs, out[i]);
            assert_eq!(got, expected[i], "byte {i} mismatch");
        }

        println!(
            "Blake2s (3-byte input): {} constraints, {} witnesses",
            cs.num_constraints(),
            cs.num_witness_variables()
        );
    }

    #[test]
    fn blake2s_in_circuit_random_lengths() {
        let mut rng = StdRng::seed_from_u64(0xB1A2_E5C0);
        // Random non-trivial lengths up to ~100 bytes; one is just over a
        // block to make sure the multi-block path executes.
        let lens = [3usize, 31, 64, 65, 100];
        for &len in &lens {
            let input: Vec<u8> = (0..len).map(|_| rng.gen()).collect();
            let cs = ConstraintSystem::<Fr>::new_ref();
            let map = WitnessMap::<Fr>::new();
            let mut b = R1csBuilder::new(cs.clone(), Some(&map));
            b.finish_public_pass();

            let in_vars: Vec<(Variable, Option<Fr>)> =
                input.iter().map(|&byte| alloc_byte(&mut b, byte)).collect();

            let out = blake2s_in_circuit(&mut b, &in_vars).unwrap();
            assert!(
                cs.is_satisfied().unwrap(),
                "constraint system unsatisfied at len={len}"
            );

            let expected = blake2s_native(&input);
            for i in 0..DIGEST_BYTES {
                let got = byte_var_value(&cs, out[i]);
                assert_eq!(got, expected[i], "byte {i} mismatch at len={len}");
            }
        }
    }

    #[test]
    fn blake2s_in_circuit_empty_input() {
        // RFC 7693 §3.3: empty input still processes a single all-zero block
        // with t = 0 and last_block = true.
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let in_vars: Vec<(Variable, Option<Fr>)> = vec![];
        let out = blake2s_in_circuit(&mut b, &in_vars).unwrap();
        assert!(cs.is_satisfied().unwrap());

        let expected = blake2s_native(b"");
        for i in 0..DIGEST_BYTES {
            let got = byte_var_value(&cs, out[i]);
            assert_eq!(got, expected[i], "byte {i} mismatch");
        }
    }
}
