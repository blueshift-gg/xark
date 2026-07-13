//! `xark-blake3`: the BLAKE3 compression function + single-block hash, written
//! entirely in the `xark` `Field` subset.
//!
//! Circuit authors just `use xark_blake3::blake3_hash_one_block;` — the compiler
//! inlines the whole compression (all 7 rounds, 8 `G` mixes per round, fully
//! `while`-loop unrolled at compile time), so it lowers to the same R1CS as if
//! written inline. It builds on the VERIFIED 32-bit word layer in `xark-bits`.
//!
//! ## Conventions
//!
//! - A 32-bit word is a `[Field; 32]` of little-endian bits (bit `i` has weight
//!   `2^i`), matching `xark-bits`. BLAKE3 reads message bytes little-endian, so
//!   each of the 16 message *words* is the LE-`u32` value of 4 consecutive bytes.
//! - `xor32` is bit-by-bit (32 gates); `rotr32` is pure re-wiring (0 gates);
//!   `add32` is modular add mod 2^32 (33 gates).
//!
//! ## What's here
//!
//! - [`blake3_hash_one_block`]: hash a single (≤64-byte) block as the *root* of a
//!   one-chunk message — flags `CHUNK_START | CHUNK_END | ROOT = 11`, counter 0.
//!   Returns the 256-bit digest as 8 words. This is spec-compliant BLAKE3 for
//!   inputs of 0..=64 bytes (a single chunk that is also the root node).
//! - [`blake3`]: variable-length single-chunk hash of a `[Field; N_BYTES]` byte
//!   array (`N_BYTES <= 1024`), chaining [`compress`] across up to 16 blocks.

#![no_std]
// Circuit-lowered gadget code: the block count is const-folded from a native
// `usize`; `(N + 63) / 64` keeps the exact MIR the compiler lowers (a `div_ceil`
// method call is not part of the accepted circuit subset).
#![allow(clippy::manual_div_ceil)]

use xark::Field;
use xark_bits::{add3, add32, read_n, rotr32, sha256_iv, xor32};

// ===========================================================================
// Small array-extraction helpers.
//
// The circuit storage model does NOT support reading a whole inner `[Field; 32]`
// word *out* of a nested array as a value (`arr[t]` copies a whole inner array,
// which the compiler drops). Only *scalar* nested access (`arr[t][j]`) works, so
// we rebuild each word element-by-element (zero gates).
// ===========================================================================

// Extract word `t` from a nested `[[Field; 32]; 16]` into a fresh flat local.
// Extract word `t` from a nested `[[Field; 32]; 8]` into a fresh flat local.
// Extract word `t` from a nested `[[Field; 32]; 4]` into a fresh flat local.
// Used to unpack the 4 updated words returned by `g`.

// ===========================================================================
// The BLAKE3 `G` mixing function.
//
//   a = (a + b + mx) mod 2^32
//   d = (d ^ a) >>> 16
//   c = (c + d) mod 2^32
//   b = (b ^ c) >>> 12
//   a = (a + b + my) mod 2^32
//   d = (d ^ a) >>> 8
//   c = (c + d) mod 2^32
//   b = (b ^ c) >>> 7
//
// Returns the 4 updated words `[a, b, c, d]`.
// ===========================================================================

/// BLAKE3 quarter-round mix. All four inputs are 32-bit words; `mx`/`my` are the
/// two message words for this mix. Returns `[a, b, c, d]` after mixing.
fn g(
    a: [Field; 32],
    b: [Field; 32],
    c: [Field; 32],
    d: [Field; 32],
    mx: [Field; 32],
    my: [Field; 32],
) -> [[Field; 32]; 4] {
    let a = add3(a, b, mx);
    let d = rotr32(xor32(d, a), 16);
    let c = add32(c, d);
    let b = rotr32(xor32(b, c), 12);
    let a = add3(a, b, my);
    let d = rotr32(xor32(d, a), 8);
    let c = add32(c, d);
    let b = rotr32(xor32(b, c), 7);

    let zero = [Field::from(0u8); 32];
    let mut out = [zero; 4];
    let mut j = 0usize;
    while j < 32usize {
        out[0][j] = a[j];
        out[1][j] = b[j];
        out[2][j] = c[j];
        out[3][j] = d[j];
        j += 1;
    }
    out
}

// ===========================================================================
// One BLAKE3 round: mix the 4 columns then the 4 diagonals of the 16-word state.
// ===========================================================================

/// Apply one BLAKE3 round to `state` using message words `block`, returning the
/// updated 16-word state.
fn round(state: [[Field; 32]; 16], block: [[Field; 32]; 16]) -> [[Field; 32]; 16] {
    // Pull all 16 state words into flat locals.
    let s0 = read_n(state, 0);
    let s1 = read_n(state, 1);
    let s2 = read_n(state, 2);
    let s3 = read_n(state, 3);
    let s4 = read_n(state, 4);
    let s5 = read_n(state, 5);
    let s6 = read_n(state, 6);
    let s7 = read_n(state, 7);
    let s8 = read_n(state, 8);
    let s9 = read_n(state, 9);
    let s10 = read_n(state, 10);
    let s11 = read_n(state, 11);
    let s12 = read_n(state, 12);
    let s13 = read_n(state, 13);
    let s14 = read_n(state, 14);
    let s15 = read_n(state, 15);

    // Pull all 16 message words into flat locals.
    let m0 = read_n(block, 0);
    let m1 = read_n(block, 1);
    let m2 = read_n(block, 2);
    let m3 = read_n(block, 3);
    let m4 = read_n(block, 4);
    let m5 = read_n(block, 5);
    let m6 = read_n(block, 6);
    let m7 = read_n(block, 7);
    let m8 = read_n(block, 8);
    let m9 = read_n(block, 9);
    let m10 = read_n(block, 10);
    let m11 = read_n(block, 11);
    let m12 = read_n(block, 12);
    let m13 = read_n(block, 13);
    let m14 = read_n(block, 14);
    let m15 = read_n(block, 15);

    // --- Mix the columns. ---
    let r = g(s0, s4, s8, s12, m0, m1);
    let s0 = read_n(r, 0);
    let s4 = read_n(r, 1);
    let s8 = read_n(r, 2);
    let s12 = read_n(r, 3);

    let r = g(s1, s5, s9, s13, m2, m3);
    let s1 = read_n(r, 0);
    let s5 = read_n(r, 1);
    let s9 = read_n(r, 2);
    let s13 = read_n(r, 3);

    let r = g(s2, s6, s10, s14, m4, m5);
    let s2 = read_n(r, 0);
    let s6 = read_n(r, 1);
    let s10 = read_n(r, 2);
    let s14 = read_n(r, 3);

    let r = g(s3, s7, s11, s15, m6, m7);
    let s3 = read_n(r, 0);
    let s7 = read_n(r, 1);
    let s11 = read_n(r, 2);
    let s15 = read_n(r, 3);

    // --- Mix the diagonals. ---
    let r = g(s0, s5, s10, s15, m8, m9);
    let s0 = read_n(r, 0);
    let s5 = read_n(r, 1);
    let s10 = read_n(r, 2);
    let s15 = read_n(r, 3);

    let r = g(s1, s6, s11, s12, m10, m11);
    let s1 = read_n(r, 0);
    let s6 = read_n(r, 1);
    let s11 = read_n(r, 2);
    let s12 = read_n(r, 3);

    let r = g(s2, s7, s8, s13, m12, m13);
    let s2 = read_n(r, 0);
    let s7 = read_n(r, 1);
    let s8 = read_n(r, 2);
    let s13 = read_n(r, 3);

    let r = g(s3, s4, s9, s14, m14, m15);
    let s3 = read_n(r, 0);
    let s4 = read_n(r, 1);
    let s9 = read_n(r, 2);
    let s14 = read_n(r, 3);

    // Write the updated words back into a fresh state array (scalar slot writes).
    let zero = [Field::from(0u8); 32];
    let mut out = [zero; 16];
    let mut j = 0usize;
    while j < 32usize {
        out[0][j] = s0[j];
        out[1][j] = s1[j];
        out[2][j] = s2[j];
        out[3][j] = s3[j];
        out[4][j] = s4[j];
        out[5][j] = s5[j];
        out[6][j] = s6[j];
        out[7][j] = s7[j];
        out[8][j] = s8[j];
        out[9][j] = s9[j];
        out[10][j] = s10[j];
        out[11][j] = s11[j];
        out[12][j] = s12[j];
        out[13][j] = s13[j];
        out[14][j] = s14[j];
        out[15][j] = s15[j];
        j += 1;
    }
    out
}

// ===========================================================================
// Message permutation between rounds.
//   MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
//   permuted[i] = m[MSG_PERMUTATION[i]]
// ===========================================================================

/// Permute the 16 message words per BLAKE3's fixed schedule (zero gates).
/// `permuted[i] = block[MSG_PERMUTATION[i]]`; the permutation is unrolled with
/// compile-time-constant source indices (a data-driven `perm[i]` table lookup is
/// not part of the circuit subset).
fn permute(block: [[Field; 32]; 16]) -> [[Field; 32]; 16] {
    // MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
    let w0 = read_n(block, 2);
    let w1 = read_n(block, 6);
    let w2 = read_n(block, 3);
    let w3 = read_n(block, 10);
    let w4 = read_n(block, 7);
    let w5 = read_n(block, 0);
    let w6 = read_n(block, 4);
    let w7 = read_n(block, 13);
    let w8 = read_n(block, 1);
    let w9 = read_n(block, 11);
    let w10 = read_n(block, 12);
    let w11 = read_n(block, 5);
    let w12 = read_n(block, 9);
    let w13 = read_n(block, 14);
    let w14 = read_n(block, 15);
    let w15 = read_n(block, 8);

    let zero = [Field::from(0u8); 32];
    let mut out = [zero; 16];
    let mut j = 0usize;
    while j < 32usize {
        out[0][j] = w0[j];
        out[1][j] = w1[j];
        out[2][j] = w2[j];
        out[3][j] = w3[j];
        out[4][j] = w4[j];
        out[5][j] = w5[j];
        out[6][j] = w6[j];
        out[7][j] = w7[j];
        out[8][j] = w8[j];
        out[9][j] = w9[j];
        out[10][j] = w10[j];
        out[11][j] = w11[j];
        out[12][j] = w12[j];
        out[13][j] = w13[j];
        out[14][j] = w14[j];
        out[15][j] = w15[j];
        j += 1;
    }
    out
}

// ===========================================================================
// The IV (first 4 words feed the compression state; all 8 form the initial
// chaining value for unkeyed hashing). These are the SHA-256 initial hash words.
// ===========================================================================

// BLAKE3 / SHA-256 IV words H0..H7, as field constants.

// ===========================================================================
// The BLAKE3 compression function.
//
//   state = [ cv[0..8], IV[0..4], counter_low, counter_high, block_len, flags ]
//   7 rounds (permuting the message block after each of the first 6)
//   out[i]   = state[i]   ^ state[i+8]   (i in 0..8)
//   out[i+8] = state[i+8] ^ cv[i]        (i in 0..8)
// ===========================================================================

/// BLAKE3 compression: mix `cv` and `block` with the given counter halves,
/// `block_len` and `flags` words, returning the 16-word feed-forward output.
///
/// `counter_low`, `counter_high`, `block_len` and `flags` are 32-bit words
/// (`[Field; 32]` bit arrays).
pub fn compress(
    cv: [[Field; 32]; 8],
    block: [[Field; 32]; 16],
    counter_low: [Field; 32],
    counter_high: [Field; 32],
    block_len: [Field; 32],
    flags: [Field; 32],
) -> [[Field; 32]; 16] {
    // Decompose the 4 IV words needed at state positions 8..12 into bit arrays.
    let ivc = sha256_iv();
    let iv0 = ivc[0].to_bits::<32>();
    let iv1 = ivc[1].to_bits::<32>();
    let iv2 = ivc[2].to_bits::<32>();
    let iv3 = ivc[3].to_bits::<32>();

    // Extract the 8 chaining-value words as flat locals (reused in feed-forward).
    let cv0 = read_n(cv, 0);
    let cv1 = read_n(cv, 1);
    let cv2 = read_n(cv, 2);
    let cv3 = read_n(cv, 3);
    let cv4 = read_n(cv, 4);
    let cv5 = read_n(cv, 5);
    let cv6 = read_n(cv, 6);
    let cv7 = read_n(cv, 7);

    // Assemble the initial 16-word state.
    let zero = [Field::from(0u8); 32];
    let mut state = [zero; 16];
    let mut j = 0usize;
    while j < 32usize {
        state[0][j] = cv0[j];
        state[1][j] = cv1[j];
        state[2][j] = cv2[j];
        state[3][j] = cv3[j];
        state[4][j] = cv4[j];
        state[5][j] = cv5[j];
        state[6][j] = cv6[j];
        state[7][j] = cv7[j];
        state[8][j] = iv0[j];
        state[9][j] = iv1[j];
        state[10][j] = iv2[j];
        state[11][j] = iv3[j];
        state[12][j] = counter_low[j];
        state[13][j] = counter_high[j];
        state[14][j] = block_len[j];
        state[15][j] = flags[j];
        j += 1;
    }

    // 7 rounds; permute the message block after each of the first 6.
    let st = round(state, block);
    let block = permute(block);
    let st = round(st, block);
    let block = permute(block);
    let st = round(st, block);
    let block = permute(block);
    let st = round(st, block);
    let block = permute(block);
    let st = round(st, block);
    let block = permute(block);
    let st = round(st, block);
    let block = permute(block);
    let st = round(st, block);

    // Feed-forward: out[i] = state[i] ^ state[i+8]; out[i+8] = state[i+8] ^ cv[i].
    let s0 = read_n(st, 0);
    let s1 = read_n(st, 1);
    let s2 = read_n(st, 2);
    let s3 = read_n(st, 3);
    let s4 = read_n(st, 4);
    let s5 = read_n(st, 5);
    let s6 = read_n(st, 6);
    let s7 = read_n(st, 7);
    let s8 = read_n(st, 8);
    let s9 = read_n(st, 9);
    let s10 = read_n(st, 10);
    let s11 = read_n(st, 11);
    let s12 = read_n(st, 12);
    let s13 = read_n(st, 13);
    let s14 = read_n(st, 14);
    let s15 = read_n(st, 15);

    let o0 = xor32(s0, s8);
    let o1 = xor32(s1, s9);
    let o2 = xor32(s2, s10);
    let o3 = xor32(s3, s11);
    let o4 = xor32(s4, s12);
    let o5 = xor32(s5, s13);
    let o6 = xor32(s6, s14);
    let o7 = xor32(s7, s15);
    let o8 = xor32(s8, cv0);
    let o9 = xor32(s9, cv1);
    let o10 = xor32(s10, cv2);
    let o11 = xor32(s11, cv3);
    let o12 = xor32(s12, cv4);
    let o13 = xor32(s13, cv5);
    let o14 = xor32(s14, cv6);
    let o15 = xor32(s15, cv7);

    let mut out = [zero; 16];
    let mut j = 0usize;
    while j < 32usize {
        out[0][j] = o0[j];
        out[1][j] = o1[j];
        out[2][j] = o2[j];
        out[3][j] = o3[j];
        out[4][j] = o4[j];
        out[5][j] = o5[j];
        out[6][j] = o6[j];
        out[7][j] = o7[j];
        out[8][j] = o8[j];
        out[9][j] = o9[j];
        out[10][j] = o10[j];
        out[11][j] = o11[j];
        out[12][j] = o12[j];
        out[13][j] = o13[j];
        out[14][j] = o14[j];
        out[15][j] = o15[j];
        j += 1;
    }
    out
}

// ===========================================================================
// Single-block root hash.
// ===========================================================================

/// Hash a single (≤64-byte) block as a one-chunk root node.
///
/// `input_words` holds the 16 message words (each a `[Field; 32]` LE bit word);
/// `block_len_bytes` is the number of message bytes in this block (0..=64) as a
/// single `Field`. Flags = `CHUNK_START | CHUNK_END | ROOT = 1 | 2 | 8 = 11`,
/// counter = 0. Returns the 8-word (256-bit) BLAKE3 digest.
pub fn blake3_hash_one_block(
    input_words: [[Field; 32]; 16],
    block_len_bytes: Field,
) -> [[Field; 32]; 8] {
    // Initial chaining value = the full 8-word IV (unkeyed hashing).
    let ivc = sha256_iv();
    let zero = [Field::from(0u8); 32];
    let mut cv = [zero; 8];
    let mut i = 0usize;
    while i < 8usize {
        let word = ivc[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize {
            cv[i][j] = word[j];
            j += 1;
        }
        i += 1;
    }

    // counter = 0 (both halves), block_len = message length, flags = 11.
    let counter_low = Field::from(0u8).to_bits::<32>();
    let counter_high = Field::from(0u8).to_bits::<32>();
    let block_len = block_len_bytes.to_bits::<32>();
    let flags = Field::from(11u8).to_bits::<32>();

    let full = compress(cv, input_words, counter_low, counter_high, block_len, flags);

    // The digest is the first 8 output words.
    let mut out = [zero; 8];
    let mut i = 0usize;
    while i < 8usize {
        let word = read_n(full, i);
        let mut j = 0usize;
        while j < 32usize {
            out[i][j] = word[j];
            j += 1;
        }
        i += 1;
    }
    out
}

// ===========================================================================
// Variable-length single-chunk hash (message ≤ 1024 bytes = ≤ 16 blocks).
// ===========================================================================

/// Variable-length BLAKE3 for a single chunk (message ≤ 1024 bytes). `N_BYTES`
/// is a compile-time constant; the message is a byte array (each `Field` a byte,
/// range-checked `< 256` when decomposed). (Multi-chunk tree mode — messages
/// over 1024 bytes — is a future extension.)
///
/// ## Chunk chaining
///
/// The message is split into 64-byte blocks (the final block zero-padded to 64
/// bytes, but with `block_len` = its real byte count). Blocks are compressed in
/// sequence, threading the chaining value:
///
/// - `cv` starts as the full 8-word IV (unkeyed hashing);
/// - every block uses `counter = 0` (single chunk) and `block_len` = the number
///   of real message bytes in that block (64 for every block but the last);
/// - `flags` = `CHUNK_START (1)` on the FIRST block, `CHUNK_END (2) | ROOT (8) =
///   10` on the LAST block, `0` on interior blocks — so a one-block message gets
///   `1 | 10 = 11`, exactly matching [`blake3_hash_one_block`];
/// - after each block `cv` becomes the first 8 output words of [`compress`].
///
/// Returns the first 8 words of the final compression = the 256-bit digest.
///
/// Each 32-bit message word is the little-endian `u32` of 4 consecutive bytes:
/// byte `k` of the word occupies bits `8k..8k+8`, built with [`Field::to_bits`]
/// `::<8>()` (matching the byte layout used by [`blake3_hash_one_block`]).
pub fn blake3<const N_BYTES: usize>(msg: [Field; N_BYTES]) -> [[Field; 32]; 8] {
    // Single-chunk MVP: a chunk is at most 1024 bytes (16 × 64-byte blocks).
    const {
        assert!(
            N_BYTES <= 1024,
            "single-chunk BLAKE3 MVP: message must be <= 1024 bytes"
        )
    };

    // Number of 64-byte blocks in this chunk (always at least one — the empty
    // message still compresses one zero block with block_len = 0).
    let num_blocks = if N_BYTES == 0usize {
        1usize
    } else {
        (N_BYTES + 63usize) / 64usize
    };

    // Zero-padded 16-block (1024-byte) buffer; copy the real message bytes in.
    // The buffer is fixed-size so byte indices are always in bounds; only the
    // first `num_blocks * 64` bytes are ever consumed below.
    let mut buf = [Field::from(0u8); 1024];
    let mut i = 0usize;
    while i < N_BYTES {
        buf[i] = msg[i];
        i += 1;
    }

    // Initial chaining value = the full 8-word IV (unkeyed hashing).
    let ivc = sha256_iv();
    let zero = [Field::from(0u8); 32];
    let mut cv = [zero; 8];
    let mut i = 0usize;
    while i < 8usize {
        let word = ivc[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize {
            cv[i][j] = word[j];
            j += 1;
        }
        i += 1;
    }

    // counter = 0 for every block of a single chunk (both 32-bit halves).
    let counter_low = Field::from(0u8).to_bits::<32>();
    let counter_high = Field::from(0u8).to_bits::<32>();

    // Compress each block, threading the chaining value.
    let mut b = 0usize;
    while b < num_blocks {
        // Assemble this block's 16 message words from bytes buf[b*64 .. b*64+64].
        // Word `t` = LE-u32 of bytes 4t..4t+4; byte `k` fills bits 8k..8k+8.
        let mut block = [zero; 16];
        let mut t = 0usize;
        while t < 16usize {
            let mut k = 0usize;
            while k < 4usize {
                let byte = buf[b * 64usize + t * 4usize + k];
                let bits = byte.to_bits::<8>();
                let mut j = 0usize;
                while j < 8usize {
                    block[t][k * 8usize + j] = bits[j];
                    j += 1;
                }
                k += 1;
            }
            t += 1;
        }

        // block_len = the real byte count of this block (64 except the last).
        let len_bytes = if b + 1usize == num_blocks {
            N_BYTES - b * 64usize
        } else {
            64usize
        };
        let block_len = Field::from(len_bytes as u64).to_bits::<32>();

        // flags: CHUNK_START (1) on the first block, CHUNK_END|ROOT (10) on the
        // last (a single-chunk message is the root). Interior blocks get 0.
        let first_flag = if b == 0usize { 1u64 } else { 0u64 };
        let last_flag = if b + 1usize == num_blocks {
            10u64
        } else {
            0u64
        };
        let flags = Field::from(first_flag + last_flag).to_bits::<32>();

        let full = compress(cv, block, counter_low, counter_high, block_len, flags);

        // Next chaining value = first 8 output words of this compression.
        let mut i = 0usize;
        while i < 8usize {
            let word = read_n(full, i);
            let mut j = 0usize;
            while j < 32usize {
                cv[i][j] = word[j];
                j += 1;
            }
            i += 1;
        }
        b += 1;
    }

    // After the final block, `cv` holds the first 8 output words = the digest.
    cv
}
