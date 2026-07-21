//! `xark-blake2s`: BLAKE2s compression + hash in the `xark` `Field` subset, so
//! the compiler inlines the whole compression (rounds and `G` mixes unrolled) to
//! the same R1CS as inline code. Built on the verified 32-bit word layer in
//! `xark-bits`. Unkeyed only, fixed 32-byte digest.
//!
//! Soundness conventions: a 32-bit word is a `[Field; 32]` of little-endian bits
//! (bit `i` has weight `2^i`), matching `xark-bits`. BLAKE2s reads message bytes
//! little-endian, so each of the 16 message words is the LE-`u32` of 4 consecutive
//! bytes.
//!
//! [`blake2s_hash_one_block`] hashes a single (≤64-byte) message as one final
//! block; [`blake2s`] is a Merkle–Damgård chain over [`compress`] for a
//! compile-time `N_BYTES`-byte message.

#![no_std]
// Circuit-lowered gadget code: the block count is const-folded from a native
// `usize`; `(N + 63) / 64` keeps the exact MIR the compiler lowers (a `div_ceil`
// method call is not part of the accepted circuit subset).
#![allow(clippy::manual_div_ceil)]

use xark::Field;
use xark_bits::{add3, add32, read_n, rotr32, sha256_iv, xor32};

// The circuit storage model can't read a whole inner `[Field; 32]` word out of a
// nested array as a value (`arr[t]` copies a whole inner array, which the compiler
// drops); only scalar nested access (`arr[t][j]`) works, so words are rebuilt
// element-by-element (zero gates).

/// BLAKE2s mixing function. All four inputs are 32-bit words; `x`/`y` are the two
/// message words for this mix. Returns `[a, b, c, d]` after mixing.
fn g(
    a: [Field; 32],
    b: [Field; 32],
    c: [Field; 32],
    d: [Field; 32],
    x: [Field; 32],
    y: [Field; 32],
) -> [[Field; 32]; 4] {
    let a = add3(a, b, x);
    let d = rotr32(xor32(d, a), 16);
    let c = add32(c, d);
    let b = rotr32(xor32(b, c), 12);
    let a = add3(a, b, y);
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

/// Apply one BLAKE2s round to `state` (mix 4 columns then 4 diagonals) using the
/// 16 SIGMA-permuted message words `x0..x15` in mix order (permutation applied by
/// `compress`), returning the updated 16-word state.
// The 16 message words are passed as separate args (the compiler only supports
// scalar array access, not a `[[Field; 32]; 16]` parameter through this call).
#[allow(clippy::too_many_arguments)]
fn round(
    state: [[Field; 32]; 16],
    x0: [Field; 32],
    x1: [Field; 32],
    x2: [Field; 32],
    x3: [Field; 32],
    x4: [Field; 32],
    x5: [Field; 32],
    x6: [Field; 32],
    x7: [Field; 32],
    x8: [Field; 32],
    x9: [Field; 32],
    x10: [Field; 32],
    x11: [Field; 32],
    x12: [Field; 32],
    x13: [Field; 32],
    x14: [Field; 32],
    x15: [Field; 32],
) -> [[Field; 32]; 16] {
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

    // Mix the columns.
    let r = g(s0, s4, s8, s12, x0, x1);
    let s0 = read_n(r, 0);
    let s4 = read_n(r, 1);
    let s8 = read_n(r, 2);
    let s12 = read_n(r, 3);

    let r = g(s1, s5, s9, s13, x2, x3);
    let s1 = read_n(r, 0);
    let s5 = read_n(r, 1);
    let s9 = read_n(r, 2);
    let s13 = read_n(r, 3);

    let r = g(s2, s6, s10, s14, x4, x5);
    let s2 = read_n(r, 0);
    let s6 = read_n(r, 1);
    let s10 = read_n(r, 2);
    let s14 = read_n(r, 3);

    let r = g(s3, s7, s11, s15, x6, x7);
    let s3 = read_n(r, 0);
    let s7 = read_n(r, 1);
    let s11 = read_n(r, 2);
    let s15 = read_n(r, 3);

    // Mix the diagonals.
    let r = g(s0, s5, s10, s15, x8, x9);
    let s0 = read_n(r, 0);
    let s5 = read_n(r, 1);
    let s10 = read_n(r, 2);
    let s15 = read_n(r, 3);

    let r = g(s1, s6, s11, s12, x10, x11);
    let s1 = read_n(r, 0);
    let s6 = read_n(r, 1);
    let s11 = read_n(r, 2);
    let s12 = read_n(r, 3);

    let r = g(s2, s7, s8, s13, x12, x13);
    let s2 = read_n(r, 0);
    let s7 = read_n(r, 1);
    let s8 = read_n(r, 2);
    let s13 = read_n(r, 3);

    let r = g(s3, s4, s9, s14, x14, x15);
    let s3 = read_n(r, 0);
    let s4 = read_n(r, 1);
    let s9 = read_n(r, 2);
    let s14 = read_n(r, 3);

    // Write words back via scalar slot writes.
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

/// BLAKE2s compression: mix the 8-word chaining value `h` with the 16-word
/// message `block` under the 64-bit counter (`t_low`, `t_high`) and the
/// final-block flag word `f_final`, returning the updated 8-word chaining value.
///
/// `t_low`, `t_high` and `f_final` are 32-bit words (`[Field; 32]` bit arrays);
/// `f_final` is all-ones (`0xFFFFFFFF`) for the final block, otherwise all-zero.
pub fn compress(
    h: [[Field; 32]; 8],
    block: [[Field; 32]; 16],
    t_low: [Field; 32],
    t_high: [Field; 32],
    f_final: [Field; 32],
) -> [[Field; 32]; 8] {
    let ivc = sha256_iv();
    let iv0 = ivc[0].to_bits::<32>();
    let iv1 = ivc[1].to_bits::<32>();
    let iv2 = ivc[2].to_bits::<32>();
    let iv3 = ivc[3].to_bits::<32>();
    let iv4 = ivc[4].to_bits::<32>();
    let iv5 = ivc[5].to_bits::<32>();
    let iv6 = ivc[6].to_bits::<32>();
    let iv7 = ivc[7].to_bits::<32>();

    // Chaining-value words as flat locals (reused in feed-forward).
    let h0 = read_n(h, 0);
    let h1 = read_n(h, 1);
    let h2 = read_n(h, 2);
    let h3 = read_n(h, 3);
    let h4 = read_n(h, 4);
    let h5 = read_n(h, 5);
    let h6 = read_n(h, 6);
    let h7 = read_n(h, 7);

    // v[12..15] fold in the counter halves and the final-block flag.
    let v12 = xor32(iv4, t_low);
    let v13 = xor32(iv5, t_high);
    let v14 = xor32(iv6, f_final);

    let zero = [Field::from(0u8); 32];
    let mut state = [zero; 16];
    let mut j = 0usize;
    while j < 32usize {
        state[0][j] = h0[j];
        state[1][j] = h1[j];
        state[2][j] = h2[j];
        state[3][j] = h3[j];
        state[4][j] = h4[j];
        state[5][j] = h5[j];
        state[6][j] = h6[j];
        state[7][j] = h7[j];
        state[8][j] = iv0[j];
        state[9][j] = iv1[j];
        state[10][j] = iv2[j];
        state[11][j] = iv3[j];
        state[12][j] = v12[j];
        state[13][j] = v13[j];
        state[14][j] = v14[j];
        state[15][j] = iv7[j];
        j += 1;
    }

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

    // 10 rounds; each `round` call passes the message words selected by that
    // round's SIGMA permutation (indices baked in per row).
    // row0: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
    let st = round(
        state, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,
    );
    // row1: 14 10 4 8 9 15 13 6 1 12 0 2 11 7 5 3
    let st = round(
        st, m14, m10, m4, m8, m9, m15, m13, m6, m1, m12, m0, m2, m11, m7, m5, m3,
    );
    // row2: 11 8 12 0 5 2 15 13 10 14 3 6 7 1 9 4
    let st = round(
        st, m11, m8, m12, m0, m5, m2, m15, m13, m10, m14, m3, m6, m7, m1, m9, m4,
    );
    // row3: 7 9 3 1 13 12 11 14 2 6 5 10 4 0 15 8
    let st = round(
        st, m7, m9, m3, m1, m13, m12, m11, m14, m2, m6, m5, m10, m4, m0, m15, m8,
    );
    // row4: 9 0 5 7 2 4 10 15 14 1 11 12 6 8 3 13
    let st = round(
        st, m9, m0, m5, m7, m2, m4, m10, m15, m14, m1, m11, m12, m6, m8, m3, m13,
    );
    // row5: 2 12 6 10 0 11 8 3 4 13 7 5 15 14 1 9
    let st = round(
        st, m2, m12, m6, m10, m0, m11, m8, m3, m4, m13, m7, m5, m15, m14, m1, m9,
    );
    // row6: 12 5 1 15 14 13 4 10 0 7 6 3 9 2 8 11
    let st = round(
        st, m12, m5, m1, m15, m14, m13, m4, m10, m0, m7, m6, m3, m9, m2, m8, m11,
    );
    // row7: 13 11 7 14 12 1 3 9 5 0 15 4 8 6 2 10
    let st = round(
        st, m13, m11, m7, m14, m12, m1, m3, m9, m5, m0, m15, m4, m8, m6, m2, m10,
    );
    // row8: 6 15 14 9 11 3 0 8 12 2 13 7 1 4 10 5
    let st = round(
        st, m6, m15, m14, m9, m11, m3, m0, m8, m12, m2, m13, m7, m1, m4, m10, m5,
    );
    // row9: 10 2 8 4 7 6 1 5 15 11 9 14 3 12 13 0
    let st = round(
        st, m10, m2, m8, m4, m7, m6, m1, m5, m15, m11, m9, m14, m3, m12, m13, m0,
    );

    let v0 = read_n(st, 0);
    let v1 = read_n(st, 1);
    let v2 = read_n(st, 2);
    let v3 = read_n(st, 3);
    let v4 = read_n(st, 4);
    let v5 = read_n(st, 5);
    let v6 = read_n(st, 6);
    let v7 = read_n(st, 7);
    let v8 = read_n(st, 8);
    let v9 = read_n(st, 9);
    let v10 = read_n(st, 10);
    let v11 = read_n(st, 11);
    let v12b = read_n(st, 12);
    let v13b = read_n(st, 13);
    let v14b = read_n(st, 14);
    let v15 = read_n(st, 15);

    // Feed-forward: h[i] = h[i] ^ v[i] ^ v[i+8].
    let o0 = xor32(xor32(h0, v0), v8);
    let o1 = xor32(xor32(h1, v1), v9);
    let o2 = xor32(xor32(h2, v2), v10);
    let o3 = xor32(xor32(h3, v3), v11);
    let o4 = xor32(xor32(h4, v4), v12b);
    let o5 = xor32(xor32(h5, v5), v13b);
    let o6 = xor32(xor32(h6, v6), v14b);
    let o7 = xor32(xor32(h7, v7), v15);

    let mut out = [zero; 8];
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
        j += 1;
    }
    out
}

/// Hash a single (≤64-byte) message block with unkeyed BLAKE2s (32-byte digest).
///
/// `input_words` holds the 16 message words (each a `[Field; 32]` LE bit word);
/// `input_len_bytes` is the number of message bytes in this block (0..=64) as a
/// single `Field`.
///
/// The initial chaining value is the IV with the parameter word folded into
/// `h[0]`: `h[0] = IV[0] ^ 0x01010020` (digest_len = 32, key_len = 0, fanout = 1,
/// depth = 1). Since this is the only (final) block, the counter `t` = message
/// length and the final-block flag is set. Returns the 8-word (256-bit) digest.
pub fn blake2s_hash_one_block(
    input_words: [[Field; 32]; 16],
    input_len_bytes: Field,
) -> [[Field; 32]; 8] {
    // Initial chaining value: IV with the parameter block folded into h[0]
    // (h[0] = IV[0] ^ 0x01010020 = 0x6A09E667 ^ 0x01010020 = 0x6B08E647).
    let ivc = sha256_iv();
    let h_words: [Field; 8] = [
        Field::from(1795745351u32), // 0x6B08E647 = IV[0] ^ 0x01010020
        ivc[1],
        ivc[2],
        ivc[3],
        ivc[4],
        ivc[5],
        ivc[6],
        ivc[7],
    ];

    let zero = [Field::from(0u8); 32];
    let mut h = [zero; 8];
    let mut i = 0usize;
    while i < 8usize {
        let word = h_words[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize {
            h[i][j] = word[j];
            j += 1;
        }
        i += 1;
    }

    // Counter low = message length; counter high = 0; final-block flag = all-ones.
    let t_low = input_len_bytes.to_bits::<32>();
    let t_high = Field::from(0u8).to_bits::<32>();
    let f_final = Field::from(4294967295u32).to_bits::<32>(); // 0xFFFFFFFF

    compress(h, input_words, t_low, t_high, f_final)
}

/// Variable-length unkeyed BLAKE2s-256. `N_BYTES` is a compile-time constant; the
/// message is the `N_BYTES` witness bytes `msg[0..N_BYTES]`, each range-checked to
/// `0..256` (via `to_bits::<8>()`). Returns the 8-word (256-bit) digest.
///
/// A Merkle–Damgård chain over the verified [`compress`] primitive: the initial
/// chaining value is the IV with the unkeyed-256 parameter block folded into `h[0]`
/// (`h[0] = IV[0] ^ 0x01010020 = 0x6B08E647`), then each 64-byte block is
/// compressed in turn.
///
/// Ordering (identical to [`blake2s_hash_one_block`]): within a 64-byte block, word
/// `t` is the LE-`u32` of bytes `blk*64 + 4t .. +4`, and byte `k` occupies bits
/// `8k..8k+8` of the `[Field; 32]` word (byte bits LE, `Field::to_bits::<8>()`); the
/// final block is zero-padded to 64 bytes.
///
/// Counter/finalization: after block `blk` the 64-bit counter `t = min((blk+1)*64,
/// N_BYTES)` splits into low/high halves `t_low`/`t_high`; `f_final` is all-ones
/// (`0xFFFFFFFF`) on the last block only.
///
/// Per the BLAKE2 spec at least one block is always compressed (empty message → one
/// all-zero block, counter `0`, final flag set), and an exact multiple of 64 gets no
/// extra block: `n_blocks = if N_BYTES == 0 { 1 } else { ⌈N_BYTES/64⌉ }`.
pub fn blake2s<const N_BYTES: usize>(msg: [Field; N_BYTES]) -> [[Field; 32]; 8] {
    let zero = [Field::from(0u8); 32];

    // Compile-time block count (const-folded). At least one block; an exact
    // multiple of 64 bytes gets no extra padding block.
    let n_blocks = if N_BYTES == 0usize {
        1usize
    } else {
        (N_BYTES + 63usize) / 64usize
    };

    // Initial chaining value: IV with the unkeyed BLAKE2s-256 parameter block
    // folded into h[0] (h[0] = IV[0] ^ 0x01010020 = 0x6B08E647).
    let ivc = sha256_iv();
    let h_words: [Field; 8] = [
        Field::from(1795745351u32), // 0x6B08E647
        ivc[1],
        ivc[2],
        ivc[3],
        ivc[4],
        ivc[5],
        ivc[6],
        ivc[7],
    ];
    let mut h = [zero; 8];
    let mut i = 0usize;
    while i < 8usize {
        let word = h_words[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize {
            h[i][j] = word[j];
            j += 1;
        }
        i += 1;
    }

    // Merkle–Damgård: compress each 64-byte block, threading the chaining value.
    let mut blk = 0usize;
    while blk < n_blocks {
        // Assemble this block's 16 message words from bytes blk*64 .. blk*64+64.
        // Word `t` = LE-u32 of bytes 4t..4t+4; byte `k` fills bits 8k..8k+8. Bytes
        // past the message end are the zero constant (final-block padding).
        let mut block = [zero; 16];
        let mut t = 0usize;
        while t < 16usize {
            let mut k = 0usize;
            while k < 4usize {
                let pos = blk * 64usize + t * 4usize + k;
                if pos < N_BYTES {
                    let bits = msg[pos].to_bits::<8>();
                    let mut j = 0usize;
                    while j < 8usize {
                        block[t][k * 8usize + j] = bits[j];
                        j += 1;
                    }
                }
                k += 1;
            }
            t += 1;
        }

        // Counter = cumulative bytes compressed after this block.
        let t_total = if (blk + 1usize) * 64usize < N_BYTES {
            (blk + 1usize) * 64usize
        } else {
            N_BYTES
        };
        let t_low = Field::from((t_total & 0xFFFFFFFFusize) as u64).to_bits::<32>();
        let t_high = Field::from((t_total >> 32) as u64).to_bits::<32>();

        // Final-block flag: all-ones (0xFFFFFFFF) on the last block, else 0.
        let f_word = if blk + 1usize == n_blocks {
            4294967295u32
        } else {
            0u32
        };
        let f_final = Field::from(f_word).to_bits::<32>();

        // Compress and thread the new chaining value word-by-word (a whole inner
        // word can't be read out of the returned nested array — see `read8`).
        let out = compress(h, block, t_low, t_high, f_final);
        let mut i = 0usize;
        while i < 8usize {
            let word = read_n(out, i);
            let mut j = 0usize;
            while j < 32usize {
                h[i][j] = word[j];
                j += 1;
            }
            i += 1;
        }

        blk += 1;
    }

    h
}

/// A BLAKE-family 256-bit digest — 8 words × 32 little-endian bits, whose canonical
/// bytes serialize each word **little-endian** (BLAKE2s and BLAKE3 both do this).
///
/// The raw `[[Field; 32]; 8]` output type is shared with SHA-256, which serializes
/// its words **big-endian** — and Rust allows only one `RequireEqCircuit<Hash>` impl
/// per type. So a BLAKE output is wrapped in `Blake256` to select the LE packing:
/// `require_eq(Blake256(blake2s(msg)), expected)`. This wrapper is BLAKE-specific, so
/// it lives here (not in `xark-hash`), built on the shared [`xark_hash::Hash::pack`].
pub struct Blake256(pub [[Field; 32]; 8]);

impl xark::RequireEqCircuit<xark_hash::Hash> for Blake256 {
    #[inline]
    fn require_eq_circuit(self, rhs: xark_hash::Hash) {
        // Word `w`, bit `i` → bit `i%8` of hash byte `4w + i/8`, weight
        // `2^(8·(31 − (4w + i/8)) + i%8)` in the big-endian hash integer.
        let mut bits = [Field::from(0u8); 256];
        let mut w = 0usize;
        while w < 8usize {
            let mut i = 0usize;
            while i < 32usize {
                let byte = 4usize * w + i / 8usize;
                bits[8usize * (31usize - byte) + i % 8usize] = self.0[w][i];
                i += 1;
            }
            w += 1;
        }
        xark_hash::Hash::pack(bits).require_eq_circuit(rhs);
    }
}

/// Bring the gadget's public API into scope alongside the xark circuit
/// essentials (`Field`, `Public`/`Private`, `require_eq`, `#[circuit]`) and the
/// shared `Hash` digest type, so a circuit crate needs a single
/// `use xark_blake2s::prelude::*;`.
pub mod prelude {
    pub use crate::*; // gadget API + the local `Blake256` wrapper
    pub use xark::prelude::*;
    pub use xark_hash::Hash;
}
