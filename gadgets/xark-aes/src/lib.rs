//! `xark-aes`: AES-128/256 (block, CTR, and authenticated GCM) written in the
//! `xark` `Field` subset. All modes are forward-only (stream encrypt == decrypt),
//! so no inverse cipher is needed; GCM adds a GF(2¹²⁸) multiply-accumulate
//! ([`gf128_mul`] → GHASH) for the authentication tag.
//!
//! A byte is a `[Field; 8]` of little-endian bits (bit `i` = coefficient of `x^i`
//! in the GF(2^8) polynomial basis). State/round keys are flat `[[Field; 8]; N]`
//! byte arrays: state uses FIPS-197 column-major index `row + 4*col`; the expanded
//! key uses index `4*word + byte_in_word`, so round `k`'s byte `i` is `ek[16*k + i]`.
//!
//! S-box: `affine(inv(b))` with the GF(2^8) inverse computed as `b^254`. The
//! multiplicative group has order 255, so `b^254 = b^-1` for `b != 0` and
//! `0^254 = 0`, meaning `b^254` IS the S-box inverse for all 256 bytes — no zero
//! special-case, no advice/hint. `b^254` uses an Itoh–Tsujii addition chain; GF
//! squaring is a linear (Frobenius) map so it is XOR-only, and the 4 general muls
//! (64 AND gates each) dominate.
//!
//! Everything is straight-line: no data-dependent control flow, every `while` has
//! a literal bound and is fully unrolled, selection is pure index arithmetic. All
//! additions here are GF(2) XORs — never modular field adds.

#![no_std]
// Circuit-lowered gadget code: native `usize` index math is const-folded, but the
// method forms clippy suggests (`div_ceil`, `is_multiple_of`) are not part of the
// accepted circuit subset — keep the explicit `(N + 15) / 16` and `w % 8 == 0`.
#![allow(clippy::manual_div_ceil)]
#![allow(clippy::manual_is_multiple_of)]

use xark::{Field, require_eq};

// GF(2^8) arithmetic on `[Field; 8]` little-endian bit vectors.
// Irreducible polynomial m(x) = x^8 + x^4 + x^3 + x + 1  (AES, 0x11B).

/// Reduce a 15-coefficient GF(2) polynomial modulo the AES irreducible `m(x)`,
/// returning the 8 low bits. Uses `x^8 ≡ x^4+x^3+x+1`: a coefficient at position
/// `pos >= 8` folds (XORs) into positions `pos-8, pos-7, pos-5, pos-4`. Folds
/// high→low so cascaded carries settle.
fn gf_reduce(p_in: [Field; 15]) -> [Field; 8] {
    let mut p = [Field::from(0u8); 15];
    let mut i = 0usize;
    while i < 15usize {
        p[i] = p_in[i];
        i += 1;
    }
    let mut step = 0usize;
    while step < 7usize {
        let pos = 14usize - step;
        let t = p[pos];
        p[pos - 8] = p[pos - 8].xor(t);
        p[pos - 7] = p[pos - 7].xor(t);
        p[pos - 5] = p[pos - 5].xor(t);
        p[pos - 4] = p[pos - 4].xor(t);
        step += 1;
    }
    let mut o = [Field::from(0u8); 8];
    let mut i = 0usize;
    while i < 8usize {
        o[i] = p[i];
        i += 1;
    }
    o
}

/// GF(2^8) multiplication: schoolbook polynomial multiply (64 AND gates, one per
/// `a[i]·b[j]`) XOR-accumulated into 15 positions, then reduced mod `m(x)`.
pub fn gf_mul(a: [Field; 8], b: [Field; 8]) -> [Field; 8] {
    let mut p = [Field::from(0u8); 15];
    let mut i = 0usize;
    while i < 8usize {
        let mut j = 0usize;
        while j < 8usize {
            let prod = a[i] * b[j]; // boolean AND (1 R1CS mult gate)
            p[i + j] = p[i + j].xor(prod);
            j += 1;
        }
        i += 1;
    }
    gf_reduce(p)
}

/// GF(2^8) squaring: in characteristic 2 this is the linear Frobenius map
/// `(Σ a_i x^i)^2 = Σ a_i x^{2i}` (cross terms vanish), so it is XOR-only. Closed
/// form after reduction mod `m(x)`, validated against `gf_mul(a,a)`.
pub fn gf_square(a: [Field; 8]) -> [Field; 8] {
    let mut o = [Field::from(0u8); 8];
    o[0] = a[0].xor(a[4]).xor(a[6]);
    o[1] = a[4].xor(a[6]).xor(a[7]);
    o[2] = a[1].xor(a[5]);
    o[3] = a[4].xor(a[5]).xor(a[6]).xor(a[7]);
    o[4] = a[2].xor(a[4]).xor(a[7]);
    o[5] = a[5].xor(a[6]);
    o[6] = a[3].xor(a[5]);
    o[7] = a[6].xor(a[7]);
    o
}

/// GF(2^8) multiplicative inverse (with `inv(0)=0`) as `a^254`, via the
/// Itoh–Tsujii addition chain: `a^(2^k-1)` towers built from squares + muls.
///   r2 = a^3, r4 = a^15, r6 = a^63, r7 = a^127, inv = (a^127)^2 = a^254.
pub fn gf_inv(a: [Field; 8]) -> [Field; 8] {
    let r2 = gf_mul(gf_square(a), a); // a^(2^2-1) = a^3
    let r4 = gf_mul(gf_square(gf_square(r2)), r2); // a^(2^4-1) = a^15
    let r6 = gf_mul(gf_square(gf_square(r4)), r2); // a^(2^6-1) = a^63
    let r7 = gf_mul(gf_square(r6), a); // a^(2^7-1) = a^127
    gf_square(r7) // a^254 = a^-1
}

/// One row of the AES S-box GF(2)-affine map (before adding the constant):
/// `b_i ⊕ b_{i+4} ⊕ b_{i+5} ⊕ b_{i+6} ⊕ b_{i+7}` (indices mod 8).
fn aff_row(b: [Field; 8], i: usize) -> Field {
    let t = b[i].xor(b[(i + 4) % 8]);
    let t = t.xor(b[(i + 5) % 8]);
    let t = t.xor(b[(i + 6) % 8]);
    t.xor(b[(i + 7) % 8])
}

/// Boolean NOT of a bit: `1 - x` (no gate). Applies the `+c_i` term of the
/// affine map for the bits of `0x63` that are set.
fn bnot(x: Field) -> Field {
    Field::from(1u8) - x
}

/// The AES S-box: `affine(gf_inv(byte))`. The affine constant is `0x63`
/// (bits 0,1,5,6 set → those output bits are complemented).
pub fn sbox(byte: [Field; 8]) -> [Field; 8] {
    let b = gf_inv(byte);
    let mut o = [Field::from(0u8); 8];
    o[0] = bnot(aff_row(b, 0)); // c0 = 1
    o[1] = bnot(aff_row(b, 1)); // c1 = 1
    o[2] = aff_row(b, 2); // c2 = 0
    o[3] = aff_row(b, 3); // c3 = 0
    o[4] = aff_row(b, 4); // c4 = 0
    o[5] = bnot(aff_row(b, 5)); // c5 = 1
    o[6] = bnot(aff_row(b, 6)); // c6 = 1
    o[7] = aff_row(b, 7); // c7 = 0
    o
}

/// GF(2^8) multiply-by-`x` (i.e. by 2), a.k.a. `xtime`: shift up one position and
/// reduce (`x^8 ≡ x^4+x^3+x+1`). Linear: 3 XOR gates (the fold of the top bit).
fn xtime(a: [Field; 8]) -> [Field; 8] {
    let mut o = [Field::from(0u8); 8];
    o[0] = a[7];
    o[1] = a[0].xor(a[7]);
    o[2] = a[1];
    o[3] = a[2].xor(a[7]);
    o[4] = a[3].xor(a[7]);
    o[5] = a[4];
    o[6] = a[5];
    o[7] = a[6];
    o
}

/// Bytewise XOR of two bytes (8 XOR gates).
fn bxor(a: [Field; 8], b: [Field; 8]) -> [Field; 8] {
    let mut o = [Field::from(0u8); 8];
    let mut i = 0usize;
    while i < 8usize {
        o[i] = a[i].xor(b[i]);
        i += 1;
    }
    o
}

// Whole-byte reads from nested arrays (rebuilt bit-by-bit — reading a whole inner
// `[Field; 8]` out of a nested array is not supported by the subset).

fn rd16(s: [[Field; 8]; 16], k: usize) -> [Field; 8] {
    let mut o = [Field::from(0u8); 8];
    let mut j = 0usize;
    while j < 8usize {
        o[j] = s[k][j];
        j += 1;
    }
    o
}

fn rd176(s: [[Field; 8]; 176], k: usize) -> [Field; 8] {
    let mut o = [Field::from(0u8); 8];
    let mut j = 0usize;
    while j < 8usize {
        o[j] = s[k][j];
        j += 1;
    }
    o
}

/// Whole-byte read from a nested `[[Field; 8]; M]` (generic over the array size —
/// used for the AES-128/256 expanded keys of 176/240 bytes).
fn rdn<const M: usize>(s: [[Field; 8]; M], k: usize) -> [Field; 8] {
    let mut o = [Field::from(0u8); 8];
    let mut j = 0usize;
    while j < 8usize {
        o[j] = s[k][j];
        j += 1;
    }
    o
}

// AES round operations. Each returns a fresh state (arrays are Copy, passed by
// value — no in-place mutation of a borrowed array).

/// SubBytes: apply the S-box to every state byte (16 S-boxes).
fn sub_bytes(s: [[Field; 8]; 16]) -> [[Field; 8]; 16] {
    let mut o = [[Field::from(0u8); 8]; 16];
    let mut i = 0usize;
    while i < 16usize {
        let y = sbox(rd16(s, i));
        let mut j = 0usize;
        while j < 8usize {
            o[i][j] = y[j];
            j += 1;
        }
        i += 1;
    }
    o
}

/// ShiftRows: row `r` is cyclically left-shifted by `r`.
/// `out[r + 4c] = in[r + 4*((c+r) mod 4)]` (pure rewiring, no gates).
fn shift_rows(s: [[Field; 8]; 16]) -> [[Field; 8]; 16] {
    let mut o = [[Field::from(0u8); 8]; 16];
    let mut r = 0usize;
    while r < 4usize {
        let mut c = 0usize;
        while c < 4usize {
            let src = r + 4usize * ((c + r) % 4usize);
            let dst = r + 4usize * c;
            let mut j = 0usize;
            while j < 8usize {
                o[dst][j] = s[src][j];
                j += 1;
            }
            c += 1;
        }
        r += 1;
    }
    o
}

/// MixColumns: each column is multiplied by the fixed circulant `[2,3,1,1]` in
/// GF(2^8). `3·s = xtime(s) ⊕ s`. XOR-only apart from the linear `xtime`.
fn mix_columns(s: [[Field; 8]; 16]) -> [[Field; 8]; 16] {
    let mut o = [[Field::from(0u8); 8]; 16];
    let mut c = 0usize;
    while c < 4usize {
        let s0 = rd16(s, 4usize * c);
        let s1 = rd16(s, 4usize * c + 1usize);
        let s2 = rd16(s, 4usize * c + 2usize);
        let s3 = rd16(s, 4usize * c + 3usize);
        // o0 = 2·s0 ⊕ 3·s1 ⊕ s2 ⊕ s3
        let o0 = bxor(bxor(xtime(s0), bxor(xtime(s1), s1)), bxor(s2, s3));
        // o1 = s0 ⊕ 2·s1 ⊕ 3·s2 ⊕ s3
        let o1 = bxor(bxor(s0, xtime(s1)), bxor(bxor(xtime(s2), s2), s3));
        // o2 = s0 ⊕ s1 ⊕ 2·s2 ⊕ 3·s3
        let o2 = bxor(bxor(s0, s1), bxor(xtime(s2), bxor(xtime(s3), s3)));
        // o3 = 3·s0 ⊕ s1 ⊕ s2 ⊕ 2·s3
        let o3 = bxor(bxor(bxor(xtime(s0), s0), s1), bxor(s2, xtime(s3)));
        let mut j = 0usize;
        while j < 8usize {
            o[4usize * c][j] = o0[j];
            o[4usize * c + 1usize][j] = o1[j];
            o[4usize * c + 2usize][j] = o2[j];
            o[4usize * c + 3usize][j] = o3[j];
            j += 1;
        }
        c += 1;
    }
    o
}

/// AddRoundKey: XOR the state with round `round`'s 16-byte round key
/// (`ek[16*round + i]`).
fn add_round_key<const EK: usize>(
    s: [[Field; 8]; 16],
    ek: [[Field; 8]; EK],
    round: usize,
) -> [[Field; 8]; 16] {
    let mut o = [[Field::from(0u8); 8]; 16];
    let mut i = 0usize;
    while i < 16usize {
        let kb = rdn(ek, 16usize * round + i);
        let mut j = 0usize;
        while j < 8usize {
            o[i][j] = s[i][j].xor(kb[j]);
            j += 1;
        }
        i += 1;
    }
    o
}

// Key expansion: 44 words (176 bytes) from the 16-byte key.

/// Round-constant byte for round `round` (1..=10) as an LE bit array.
/// Rcon = [01,02,04,08,10,20,40,80,1b,36] for rounds 1..10 (only byte 0 of each
/// key-schedule word gets it XORed). Index 0 is unused (zero).
fn rcon(round: usize) -> [Field; 8] {
    let table: [[Field; 8]; 11] = [
        bits8_const(0),    // unused
        bits8_const(0x01), // round 1
        bits8_const(0x02),
        bits8_const(0x04),
        bits8_const(0x08),
        bits8_const(0x10),
        bits8_const(0x20),
        bits8_const(0x40),
        bits8_const(0x80),
        bits8_const(0x1b),
        bits8_const(0x36), // round 10
    ];
    rd(table, round)
}

/// Whole-byte read from an `[[Field;8];11]` (rebuilt bit-by-bit).
fn rd(t: [[Field; 8]; 11], k: usize) -> [Field; 8] {
    let mut o = [Field::from(0u8); 8];
    let mut j = 0usize;
    while j < 8usize {
        o[j] = t[k][j];
        j += 1;
    }
    o
}

/// A compile-time byte constant as an LE bit array (all constants, no gates).
fn bits8_const(v: usize) -> [Field; 8] {
    let mut o = [Field::from(0u8); 8];
    let one = Field::from(1u8);
    if v & 1usize != 0usize {
        o[0] = one;
    }
    if v & 2usize != 0usize {
        o[1] = one;
    }
    if v & 4usize != 0usize {
        o[2] = one;
    }
    if v & 8usize != 0usize {
        o[3] = one;
    }
    if v & 16usize != 0usize {
        o[4] = one;
    }
    if v & 32usize != 0usize {
        o[5] = one;
    }
    if v & 64usize != 0usize {
        o[6] = one;
    }
    if v & 128usize != 0usize {
        o[7] = one;
    }
    o
}

/// Expand the 16-byte key into the 176-byte (44-word) key schedule.
/// Word layout in `ek`: byte `4*word + b` at index `4*word + b`.
fn key_expansion(key: [[Field; 8]; 16]) -> [[Field; 8]; 176] {
    let mut ek = [[Field::from(0u8); 8]; 176];
    // Words 0..3 = the key verbatim.
    let mut i = 0usize;
    while i < 16usize {
        let kb = rd16(key, i);
        let mut j = 0usize;
        while j < 8usize {
            ek[i][j] = kb[j];
            j += 1;
        }
        i += 1;
    }

    // Rounds 1..10: each emits one new group of 4 words. No `if i%4` branch —
    // the per-round structure is fixed (first word uses RotWord/SubWord/Rcon).
    let mut round = 1usize;
    while round < 11usize {
        let base = 16usize * round; // byte index of word (4*round)
        // temp = previous word W[4*round - 1] = ek[base-4 .. base]
        let t0 = rd176(ek, base - 4usize);
        let t1 = rd176(ek, base - 3usize);
        let t2 = rd176(ek, base - 2usize);
        let t3 = rd176(ek, base - 1usize);
        // RotWord [t0,t1,t2,t3] -> [t1,t2,t3,t0]; SubWord; Rcon on byte 0.
        let s0 = bxor(sbox(t1), rcon(round));
        let s1 = sbox(t2);
        let s2 = sbox(t3);
        let s3 = sbox(t0);
        // W[4*round] = W[4*round-4] XOR temp.
        let w00 = bxor(rd176(ek, base - 16usize), s0);
        let w01 = bxor(rd176(ek, base - 15usize), s1);
        let w02 = bxor(rd176(ek, base - 14usize), s2);
        let w03 = bxor(rd176(ek, base - 13usize), s3);
        let mut j = 0usize;
        while j < 8usize {
            ek[base][j] = w00[j];
            ek[base + 1usize][j] = w01[j];
            ek[base + 2usize][j] = w02[j];
            ek[base + 3usize][j] = w03[j];
            j += 1;
        }
        // W[4*round + c] = W[4*round + c - 4] XOR W[4*round + c - 1], c = 1,2,3.
        // Each word is 4 bytes, so loop over all 4 byte lanes.
        let mut c = 1usize;
        while c < 4usize {
            let cur = base + 4usize * c; // first byte of word (4round+c)
            let prev = cur - 4usize; // first byte of previous word (4round+c-1)
            let far = cur - 16usize; // first byte of word (4round+c-4)
            let mut b = 0usize;
            while b < 4usize {
                let nw = bxor(rd176(ek, far + b), rd176(ek, prev + b));
                let mut j = 0usize;
                while j < 8usize {
                    ek[cur + b][j] = nw[j];
                    j += 1;
                }
                b += 1;
            }
            c += 1;
        }
        round += 1;
    }
    ek
}

// ===========================================================================
// AES-128 block encryption.
// ===========================================================================

/// One full middle round (rounds 1..=9): SubBytes, ShiftRows, MixColumns,
/// AddRoundKey.
fn round<const EK: usize>(s: [[Field; 8]; 16], ek: [[Field; 8]; EK], k: usize) -> [[Field; 8]; 16] {
    add_round_key(mix_columns(shift_rows(sub_bytes(s))), ek, k)
}

/// Encrypt one 128-bit block (10 rounds).
/// `pt` and `key` are 16 bytes each (LE-bit `[Field; 8]`); returns 16 ciphertext
/// bytes. Round 0: AddRoundKey. Rounds 1-9: full round. Round 10: SubBytes,
/// ShiftRows, AddRoundKey (no MixColumns).
pub fn aes128_encrypt(pt: [[Field; 8]; 16], key: [[Field; 8]; 16]) -> [[Field; 8]; 16] {
    let ek = key_expansion(key);
    let s = add_round_key(pt, ek, 0);
    let s = round(s, ek, 1);
    let s = round(s, ek, 2);
    let s = round(s, ek, 3);
    let s = round(s, ek, 4);
    let s = round(s, ek, 5);
    let s = round(s, ek, 6);
    let s = round(s, ek, 7);
    let s = round(s, ek, 8);
    let s = round(s, ek, 9);
    add_round_key(shift_rows(sub_bytes(s)), ek, 10)
}

// ===========================================================================
// AES-256 block encryption (14 rounds, 32-byte key, 240-byte expanded key).
// ===========================================================================

/// Expand the 32-byte AES-256 key into the 240-byte (60-word) key schedule.
/// `Nk = 8`, `Nr = 14`. Word `w` (`w >= 8`): `temp = W[w-1]`; if `w % 8 == 0`,
/// `temp = SubWord(RotWord(temp)) ⊕ Rcon[w/8]`; else if `w % 8 == 4`,
/// `temp = SubWord(temp)` (the extra AES-256 SubWord); then `W[w] = W[w-8] ⊕ temp`.
fn key_expansion_256(key: [[Field; 8]; 32]) -> [[Field; 8]; 240] {
    let mut ek = [[Field::from(0u8); 8]; 240];
    // Words 0..7 = the key verbatim (32 bytes).
    let mut i = 0usize;
    while i < 32usize {
        let kb = rdn(key, i);
        let mut j = 0usize;
        while j < 8usize {
            ek[i][j] = kb[j];
            j += 1;
        }
        i += 1;
    }

    // Words 8..59.
    let mut w = 8usize;
    while w < 60usize {
        let base = 4usize * w; // byte index of word w
        // temp = W[w-1] = bytes (base-4 .. base).
        let t0 = rdn(ek, base - 4usize);
        let t1 = rdn(ek, base - 3usize);
        let t2 = rdn(ek, base - 2usize);
        let t3 = rdn(ek, base - 1usize);
        // Transform temp based on the word position (const `w`, so const branch).
        let (s0, s1, s2, s3) = if w % 8usize == 0usize {
            // RotWord [t0,t1,t2,t3] -> [t1,t2,t3,t0]; SubWord; Rcon on byte 0.
            (
                bxor(sbox(t1), rcon(w / 8usize)),
                sbox(t2),
                sbox(t3),
                sbox(t0),
            )
        } else if w % 8usize == 4usize {
            // AES-256: an extra SubWord (no RotWord/Rcon) at the mid-group word.
            (sbox(t0), sbox(t1), sbox(t2), sbox(t3))
        } else {
            (t0, t1, t2, t3)
        };
        // W[w] = W[w-8] ⊕ temp. W[w-8] = bytes (base-32 .. base-28).
        let w0 = bxor(rdn(ek, base - 32usize), s0);
        let w1 = bxor(rdn(ek, base - 31usize), s1);
        let w2 = bxor(rdn(ek, base - 30usize), s2);
        let w3 = bxor(rdn(ek, base - 29usize), s3);
        let mut j = 0usize;
        while j < 8usize {
            ek[base][j] = w0[j];
            ek[base + 1usize][j] = w1[j];
            ek[base + 2usize][j] = w2[j];
            ek[base + 3usize][j] = w3[j];
            j += 1;
        }
        w += 1;
    }
    ek
}

/// Encrypt one 128-bit block under a 256-bit key (14 rounds). `pt` is 16 bytes,
/// `key` is 32 bytes (LE-bit `[Field; 8]`). Round 0: AddRoundKey; rounds 1-13: full
/// round; round 14: SubBytes, ShiftRows, AddRoundKey (no MixColumns).
pub fn aes256_encrypt(pt: [[Field; 8]; 16], key: [[Field; 8]; 32]) -> [[Field; 8]; 16] {
    let ek = key_expansion_256(key);
    let s = add_round_key(pt, ek, 0);
    let s = round(s, ek, 1);
    let s = round(s, ek, 2);
    let s = round(s, ek, 3);
    let s = round(s, ek, 4);
    let s = round(s, ek, 5);
    let s = round(s, ek, 6);
    let s = round(s, ek, 7);
    let s = round(s, ek, 8);
    let s = round(s, ek, 9);
    let s = round(s, ek, 10);
    let s = round(s, ek, 11);
    let s = round(s, ek, 12);
    let s = round(s, ek, 13);
    add_round_key(shift_rows(sub_bytes(s)), ek, 14)
}

// ===========================================================================
// Convenience wrappers operating on `Field` bytes in [0, 256) (range-checked
// via `to_bits8`). These are what circuit authors call.
// ===========================================================================

/// Encrypt 16 plaintext bytes under 16 key bytes, returning 16 ciphertext bytes.
/// Each input `Field` is decomposed via `to_bits8` (which range-checks < 256);
/// each output is recomposed with `from_bits8`.
pub fn aes128_encrypt_bytes(pt: [Field; 16], key: [Field; 16]) -> [Field; 16] {
    let mut ptb = [[Field::from(0u8); 8]; 16];
    let mut keyb = [[Field::from(0u8); 8]; 16];
    let mut i = 0usize;
    while i < 16usize {
        let pb = pt[i].to_bits::<8>();
        let kb = key[i].to_bits::<8>();
        let mut j = 0usize;
        while j < 8usize {
            ptb[i][j] = pb[j];
            keyb[i][j] = kb[j];
            j += 1;
        }
        i += 1;
    }
    let ct = aes128_encrypt(ptb, keyb);
    let mut out = [Field::from(0u8); 16];
    let mut i = 0usize;
    while i < 16usize {
        out[i] = Field::from_bits::<8>(rd16(ct, i));
        i += 1;
    }
    out
}

/// AES-256 counterpart of [`aes128_encrypt_bytes`]: 16 plaintext bytes under a
/// 32-byte key → 16 ciphertext bytes.
pub fn aes256_encrypt_bytes(pt: [Field; 16], key: [Field; 32]) -> [Field; 16] {
    let mut ptb = [[Field::from(0u8); 8]; 16];
    let mut i = 0usize;
    while i < 16usize {
        let pb = pt[i].to_bits::<8>();
        let mut j = 0usize;
        while j < 8usize {
            ptb[i][j] = pb[j];
            j += 1;
        }
        i += 1;
    }
    let mut keyb = [[Field::from(0u8); 8]; 32];
    let mut i = 0usize;
    while i < 32usize {
        let kb = key[i].to_bits::<8>();
        let mut j = 0usize;
        while j < 8usize {
            keyb[i][j] = kb[j];
            j += 1;
        }
        i += 1;
    }
    let ct = aes256_encrypt(ptb, keyb);
    let mut out = [Field::from(0u8); 16];
    let mut i = 0usize;
    while i < 16usize {
        out[i] = Field::from_bits::<8>(rd16(ct, i));
        i += 1;
    }
    out
}

/// Encrypt (AES-256) and `require_eq` each ciphertext byte to the public output.
pub fn aes256_constrain(pt: [Field; 16], key: [Field; 32], ct: [Field; 16]) {
    let out = aes256_encrypt_bytes(pt, key);
    require_eq(out, ct);
}

/// Test/introspection helper: expand `key` and return expanded-key byte `idx`
/// (byte `4*word + b` at index `idx`) as a `Field`. Lets tests pin the key
/// schedule against the FIPS-197 known expansion.
pub fn key_schedule_byte(key: [Field; 16], idx: usize) -> Field {
    let mut keyb = [[Field::from(0u8); 8]; 16];
    let mut i = 0usize;
    while i < 16usize {
        let kb = key[i].to_bits::<8>();
        let mut j = 0usize;
        while j < 8usize {
            keyb[i][j] = kb[j];
            j += 1;
        }
        i += 1;
    }
    let ek = key_expansion(keyb);
    Field::from_bits::<8>(rd176(ek, idx))
}

/// Encrypt and `require_eq` each ciphertext byte to the provided public
/// output bytes.
pub fn aes128_constrain(pt: [Field; 16], key: [Field; 16], ct: [Field; 16]) {
    let out = aes128_encrypt_bytes(pt, key);
    require_eq(out, ct);
}

/// AES-128 in **counter (CTR) mode** over an arbitrary `N`-byte message.
///
/// CTR is **forward-only** — encryption and decryption are the same XOR against a
/// keystream, so this reuses [`aes128_encrypt`] with no inverse-cipher cost (no
/// inverse S-box / `InvMixColumns`). It is the confidentiality layer of AES-GCM.
///
/// The keystream is produced block-by-block: the counter block for message block
/// `b` (0-indexed) is the 96-bit `nonce` concatenated with the 32-bit **big-endian**
/// block counter `b` — i.e. `nonce(12 bytes) ‖ be_u32(b)` — and the keystream is
/// `AES_enc(key, counter_block)`. The output is `msg XOR keystream` byte-wise, with
/// the final block truncated to the `N mod 16` remaining bytes. Because `N` is a
/// compile-time constant, the block count and every counter suffix are constants —
/// **no in-circuit counter arithmetic**.
///
/// Matches a reference computed as `AES_enc(key, nonce ‖ be_u32(b))` XOR `msg`
/// (standard 96-bit-nonce CTR with the counter starting at 0; the same construction
/// AES-GCM uses for confidentiality, minus the GHASH authentication).
///
/// `key` is 16 bytes, `nonce` is 12 bytes; each input `Field` is range-checked to a
/// byte via `to_bits::<8>`.
pub fn aes128_ctr<const N: usize>(
    msg: [Field; N],
    key: [Field; 16],
    nonce: [Field; 12],
) -> [Field; N] {
    // Key + nonce as bytes-of-bits (LE, range-checked `< 256` by `to_bits::<8>`).
    let mut key_bits = [[Field::from(0u8); 8]; 16];
    let mut i = 0usize;
    while i < 16usize {
        let kb = key[i].to_bits::<8>();
        let mut j = 0usize;
        while j < 8usize {
            key_bits[i][j] = kb[j];
            j += 1;
        }
        i += 1;
    }
    let mut nonce_bits = [[Field::from(0u8); 8]; 12];
    let mut i = 0usize;
    while i < 12usize {
        let nb = nonce[i].to_bits::<8>();
        let mut j = 0usize;
        while j < 8usize {
            nonce_bits[i][j] = nb[j];
            j += 1;
        }
        i += 1;
    }

    let nblocks = (N + 15usize) / 16usize;
    let mut out = [Field::from(0u8); N];
    let mut b = 0usize;
    while b < nblocks {
        // Counter block = nonce (12 bytes) ‖ big-endian u32(b). The 4 counter
        // bytes are compile-time constants (`b` is const in the unrolled loop),
        // so no counter arithmetic is emitted into the circuit.
        let mut ctr = [[Field::from(0u8); 8]; 16];
        let mut t = 0usize;
        while t < 12usize {
            let mut j = 0usize;
            while j < 8usize {
                ctr[t][j] = nonce_bits[t][j];
                j += 1;
            }
            t += 1;
        }
        let mut k = 0usize;
        while k < 4usize {
            // Counter byte `12+k` = the (3-k)-th byte of the big-endian `u32(b)`.
            let byte = (b >> (8usize * (3usize - k))) & 0xffusize;
            let mut j = 0usize;
            while j < 8usize {
                ctr[12usize + k][j] = Field::from(((byte >> j) & 1usize) as u8);
                j += 1;
            }
            k += 1;
        }

        // Keystream for this block (the forward cipher on the counter block).
        let ks = aes128_encrypt(ctr, key_bits);

        // XOR the keystream into this block's (up to 16) message bytes. `idx` and
        // `N` are compile-time constants, so `if idx < N` is resolved at compile
        // time — the tail block simply produces fewer bytes (same pattern as
        // `sha256::<N>`'s padded-byte selection).
        let mut j = 0usize;
        while j < 16usize {
            let idx = b * 16usize + j;
            if idx < N {
                let mb = msg[idx].to_bits::<8>();
                let ksj = rd16(ks, j);
                let mut xbits = [Field::from(0u8); 8];
                let mut t = 0usize;
                while t < 8usize {
                    xbits[t] = mb[t].xor(ksj[t]);
                    t += 1;
                }
                out[idx] = Field::from_bits::<8>(xbits);
            }
            j += 1;
        }
        b += 1;
    }
    out
}

// ===========================================================================
// GF(2^128) multiplication in the GCM field — the core of GHASH (AES-GCM auth).
// ===========================================================================

/// Multiply two 128-bit blocks in the GCM GF(2^128) field (NIST SP 800-38D §6.3).
///
/// Blocks are in **GCM bit order**: `bit[0]` is the *leftmost* / most-significant
/// bit (bit 7 of byte 0), `bit[127]` is the rightmost (bit 0 of byte 15). The
/// reduction polynomial is `R = 11100001 ‖ 0¹²⁰` (`0xe1` then 120 zeros), i.e.
/// `x¹²⁸ + x⁷ + x² + x + 1`.
///
/// Bit-serial (Algorithm 1) done **arithmetically** so there is no
/// witness-dependent branching: each step does `Z ^= x[i]·V` (the `x[i]=1`
/// conditional add of `V`, as a product) and `V = (V>>1) ^ (V[127]·R)` (the
/// `lsb(V)=1` conditional reduction). `x`/`y` bits must be boolean (they come from
/// byte decompositions); all intermediates stay boolean by construction.
///
/// Cost: 128 steps × (128 AND + 128 XOR for `Z`, + 4 XOR for `V`) ≈ 33k mult gates.
pub fn gf128_mul(x: [Field; 128], y: [Field; 128]) -> [Field; 128] {
    let zero = Field::from(0u8);
    let mut z = [zero; 128];
    let mut v = y;
    let mut i = 0usize;
    while i < 128usize {
        // Z ^= x[i] · V  (arithmetized conditional add of V when x[i] = 1).
        let mut k = 0usize;
        while k < 128usize {
            let p = x[i] * v[k]; // x[i] AND v[k]
            z[k] = z[k].xor(p);
            k += 1;
        }
        // V = (V >> 1) ^ (V[127] · R). Right shift toward higher index: newV[0]=0,
        // newV[k]=V[k-1]. `carry = V[127]` is the bit shifted out (the LSB).
        let carry = v[127];
        let mut nv = [zero; 128];
        let mut k = 1usize;
        while k < 128usize {
            nv[k] = v[k - 1];
            k += 1;
        }
        // XOR the reduction poly R (set bits at GCM indices {0,1,2,7}) when carry=1.
        nv[0] = nv[0].xor(carry);
        nv[1] = nv[1].xor(carry);
        nv[2] = nv[2].xor(carry);
        nv[7] = nv[7].xor(carry);
        v = nv;
        i += 1;
    }
    z
}

/// Convert 16 bytes (`[Field; 16]`, each a byte in `[0,256)`) to a 128-bit block in
/// **GCM bit order**: `bit[8·byte + k]` = bit `7-k` of byte `byte` (MSB-first within
/// each byte). `to_bits::<8>` range-checks each input to a byte.
pub fn bytes_to_gf128(bytes: [Field; 16]) -> [Field; 128] {
    let mut out = [Field::from(0u8); 128];
    let mut byte = 0usize;
    while byte < 16usize {
        let le = bytes[byte].to_bits::<8>(); // le[i] = bit i (LSB-first)
        let mut k = 0usize;
        while k < 8usize {
            out[8usize * byte + k] = le[7usize - k]; // GCM bit = MSB-first
            k += 1;
        }
        byte += 1;
    }
    out
}

/// Inverse of [`bytes_to_gf128`]: a 128-bit GCM-order block back to 16 bytes.
pub fn gf128_to_bytes(bits: [Field; 128]) -> [Field; 16] {
    let mut out = [Field::from(0u8); 16];
    let mut byte = 0usize;
    while byte < 16usize {
        let mut le = [Field::from(0u8); 8];
        let mut k = 0usize;
        while k < 8usize {
            le[7usize - k] = bits[8usize * byte + k];
            k += 1;
        }
        out[byte] = Field::from_bits::<8>(le);
        byte += 1;
    }
    out
}

// ===========================================================================
// AES-128-GCM (empty AAD).
// ===========================================================================

/// XOR two 128-bit blocks bit-wise.
fn xor128(a: [Field; 128], b: [Field; 128]) -> [Field; 128] {
    let mut out = [Field::from(0u8); 128];
    let mut i = 0usize;
    while i < 128usize {
        out[i] = a[i].xor(b[i]);
        i += 1;
    }
    out
}

/// An AES bit-byte block (`[[Field; 8]; 16]`, LE bits per byte) → a GCM-order
/// 128-bit block (`bit[8·byte + k]` = bit `7-k` of the byte, MSB-first).
fn bitbytes_to_gf128(bb: [[Field; 8]; 16]) -> [Field; 128] {
    let mut out = [Field::from(0u8); 128];
    let mut byte = 0usize;
    while byte < 16usize {
        let b = rd16(bb, byte);
        let mut k = 0usize;
        while k < 8usize {
            out[8usize * byte + k] = b[7usize - k];
            k += 1;
        }
        byte += 1;
    }
    out
}

/// `M` `Field` bytes → AES bit-bytes (`[[Field; 8]; M]`, `to_bits::<8>` per byte,
/// which range-checks `< 256`). Generic over the length (key 16/32, nonce 12).
fn bytes_to_bitbytes<const M: usize>(b: [Field; M]) -> [[Field; 8]; M] {
    let mut out = [[Field::from(0u8); 8]; M];
    let mut i = 0usize;
    while i < M {
        let bits = b[i].to_bits::<8>();
        let mut k = 0usize;
        while k < 8usize {
            out[i][k] = bits[k];
            k += 1;
        }
        i += 1;
    }
    out
}

/// A GCM counter block as AES bit-bytes: `nonce(12 bytes) ‖ be_u32(ctr)`. `ctr` is
/// a compile-time constant, so the 4 counter bytes are constant bits.
fn gcm_counter(nonce_bb: [[Field; 8]; 12], ctr: u32) -> [[Field; 8]; 16] {
    let mut out = [[Field::from(0u8); 8]; 16];
    let mut t = 0usize;
    while t < 12usize {
        let mut k = 0usize;
        while k < 8usize {
            out[t][k] = nonce_bb[t][k];
            k += 1;
        }
        t += 1;
    }
    let mut c = 0usize;
    while c < 4usize {
        let byte = ((ctr >> (8u32 * (3u32 - c as u32))) & 0xffu32) as usize;
        let mut k = 0usize;
        while k < 8usize {
            out[12usize + c][k] = Field::from(((byte >> k) & 1usize) as u8);
            k += 1;
        }
        c += 1;
    }
    out
}

/// GHASH-absorb `M` bytes (zero-padded to 16-byte blocks) into accumulator `x`:
/// for each block `B` (in GCM bit order), `x ← (x ⊕ B) · H`. Key-size-independent,
/// so it is shared by every GCM variant.
fn ghash_update<const M: usize>(
    mut x: [Field; 128],
    bytes: [Field; M],
    h: [Field; 128],
) -> [Field; 128] {
    let nblk = (M + 15usize) / 16usize;
    let mut b = 0usize;
    while b < nblk {
        let mut blk = [Field::from(0u8); 128];
        let mut j = 0usize;
        while j < 16usize {
            let idx = b * 16usize + j;
            if idx < M {
                let le = bytes[idx].to_bits::<8>();
                let mut k = 0usize;
                while k < 8usize {
                    blk[8usize * j + k] = le[7usize - k];
                    k += 1;
                }
            }
            j += 1;
        }
        x = gf128_mul(xor128(x, blk), h);
        b += 1;
    }
    x
}

/// The GCM length block: `[len(AAD) in bits]₆₄ ‖ [len(C) in bits]₆₄`, big-endian, as
/// a GCM-order 128-bit block. `A`/`N` are const generics so the whole block is a
/// compile-time constant (no witness arithmetic).
fn gcm_len_block<const A: usize, const N: usize>() -> [Field; 128] {
    let mut out = [Field::from(0u8); 128];
    let aad_bits = 8u64 * (A as u64);
    let c_bits = 8u64 * (N as u64);
    let mut i = 0usize;
    while i < 8usize {
        let a_byte = ((aad_bits >> (8u64 * (7u64 - i as u64))) & 0xffu64) as usize;
        let c_byte = ((c_bits >> (8u64 * (7u64 - i as u64))) & 0xffu64) as usize;
        let mut k = 0usize;
        while k < 8usize {
            out[8usize * i + k] = Field::from(((a_byte >> (7usize - k)) & 1usize) as u8);
            out[8usize * (8usize + i) + k] = Field::from(((c_byte >> (7usize - k)) & 1usize) as u8);
            k += 1;
        }
        i += 1;
    }
    out
}

/// AES-128 in **Galois/Counter Mode** over an `N`-byte plaintext with `A` bytes of
/// additional authenticated data (AAD) and a 96-bit `nonce`. Returns
/// `(ciphertext[N], tag[16])`.
///
/// Full NIST SP 800-38D construction: the hash subkey `H = AES_enc(key, 0¹²⁸)`; the
/// pre-counter `J0 = nonce ‖ 0x00000001`; the ciphertext is CTR encryption of the
/// plaintext starting at `inc32(J0)` (counter `2, 3, …`); the authentication tag is
/// `GHASH_H(A ‖ pad ‖ C ‖ pad ‖ [len(A)]₆₄ ‖ [len(C)]₆₄) XOR AES_enc(key, J0)`,
/// where GHASH accumulates `X ← (X ⊕ block)·H` over the GF(2¹²⁸) field
/// ([`gf128_mul`]) — the AAD is authenticated but not encrypted (as with a TLS
/// record header). Set `A = 0` for no AAD.
///
/// A `#[circuit]` proving `(aad, pt, key, nonce) → (ct, tag)` shows the prover knows
/// a key + plaintext that GCM-encrypt+authenticate to a public `(ciphertext, tag)`
/// under the public `aad`.
pub fn aes128_gcm<const A: usize, const N: usize>(
    aad: [Field; A],
    pt: [Field; N],
    key: [Field; 16],
    nonce: [Field; 12],
) -> ([Field; N], [Field; 16]) {
    let key_bits = bytes_to_bitbytes(key);
    let nonce_bb = bytes_to_bitbytes(nonce);

    // Hash subkey H = AES(key, 0^128), and E(J0) for the tag (J0 = nonce ‖ 1).
    let h = bitbytes_to_gf128(aes128_encrypt([[Field::from(0u8); 8]; 16], key_bits));
    let ej0 = bitbytes_to_gf128(aes128_encrypt(gcm_counter(nonce_bb, 1u32), key_bits));

    // Ciphertext: CTR from counter 2 = inc32(J0).
    let nblocks = (N + 15usize) / 16usize;
    let mut ct = [Field::from(0u8); N];
    let mut b = 0usize;
    while b < nblocks {
        let ks = aes128_encrypt(gcm_counter(nonce_bb, (b as u32) + 2u32), key_bits);
        let mut j = 0usize;
        while j < 16usize {
            let idx = b * 16usize + j;
            if idx < N {
                let mb = pt[idx].to_bits::<8>();
                let ksj = rd16(ks, j);
                let mut xb = [Field::from(0u8); 8];
                let mut t = 0usize;
                while t < 8usize {
                    xb[t] = mb[t].xor(ksj[t]);
                    t += 1;
                }
                ct[idx] = Field::from_bits::<8>(xb);
            }
            j += 1;
        }
        b += 1;
    }

    // GHASH over AAD blocks, then ciphertext blocks, then the length block.
    let mut x = [Field::from(0u8); 128];
    x = ghash_update::<A>(x, aad, h);
    x = ghash_update::<N>(x, ct, h);
    x = gf128_mul(xor128(x, gcm_len_block::<A, N>()), h);

    // Tag = GHASH ⊕ E(J0), as 16 bytes.
    let tag = gf128_to_bytes(xor128(x, ej0));
    (ct, tag)
}

// ===========================================================================
// AES-256 modes (CTR / GCM). Identical to the AES-128 modes except the block
// cipher is `aes256_encrypt` with a 32-byte key; the GF(2^128)/GHASH/counter
// helpers are shared verbatim.
// ===========================================================================

/// AES-256 in counter (CTR) mode over an `N`-byte message. See [`aes128_ctr`] — the
/// only difference is the 32-byte key and `aes256_encrypt` block cipher.
pub fn aes256_ctr<const N: usize>(
    msg: [Field; N],
    key: [Field; 32],
    nonce: [Field; 12],
) -> [Field; N] {
    let key_bits = bytes_to_bitbytes(key);
    let nonce_bb = bytes_to_bitbytes(nonce);
    let nblocks = (N + 15usize) / 16usize;
    let mut out = [Field::from(0u8); N];
    let mut b = 0usize;
    while b < nblocks {
        let ks = aes256_encrypt(gcm_counter(nonce_bb, b as u32), key_bits);
        let mut j = 0usize;
        while j < 16usize {
            let idx = b * 16usize + j;
            if idx < N {
                let mb = msg[idx].to_bits::<8>();
                let ksj = rd16(ks, j);
                let mut xbits = [Field::from(0u8); 8];
                let mut t = 0usize;
                while t < 8usize {
                    xbits[t] = mb[t].xor(ksj[t]);
                    t += 1;
                }
                out[idx] = Field::from_bits::<8>(xbits);
            }
            j += 1;
        }
        b += 1;
    }
    out
}

/// AES-256 in Galois/Counter Mode with `A` bytes of AAD. See [`aes128_gcm`] — the
/// only difference is the 32-byte key and `aes256_encrypt` block cipher.
pub fn aes256_gcm<const A: usize, const N: usize>(
    aad: [Field; A],
    pt: [Field; N],
    key: [Field; 32],
    nonce: [Field; 12],
) -> ([Field; N], [Field; 16]) {
    let key_bits = bytes_to_bitbytes(key);
    let nonce_bb = bytes_to_bitbytes(nonce);

    let h = bitbytes_to_gf128(aes256_encrypt([[Field::from(0u8); 8]; 16], key_bits));
    let ej0 = bitbytes_to_gf128(aes256_encrypt(gcm_counter(nonce_bb, 1u32), key_bits));

    let nblocks = (N + 15usize) / 16usize;
    let mut ct = [Field::from(0u8); N];
    let mut b = 0usize;
    while b < nblocks {
        let ks = aes256_encrypt(gcm_counter(nonce_bb, (b as u32) + 2u32), key_bits);
        let mut j = 0usize;
        while j < 16usize {
            let idx = b * 16usize + j;
            if idx < N {
                let mb = pt[idx].to_bits::<8>();
                let ksj = rd16(ks, j);
                let mut xb = [Field::from(0u8); 8];
                let mut t = 0usize;
                while t < 8usize {
                    xb[t] = mb[t].xor(ksj[t]);
                    t += 1;
                }
                ct[idx] = Field::from_bits::<8>(xb);
            }
            j += 1;
        }
        b += 1;
    }

    let mut x = [Field::from(0u8); 128];
    x = ghash_update::<A>(x, aad, h);
    x = ghash_update::<N>(x, ct, h);
    x = gf128_mul(xor128(x, gcm_len_block::<A, N>()), h);
    let tag = gf128_to_bytes(xor128(x, ej0));
    (ct, tag)
}

/// Bring the gadget's public API into scope alongside the xark circuit
/// essentials (`Field`, `Public`/`Private`, `require_eq`, `#[circuit]`), so a
/// circuit crate needs a single `use xark_aes::prelude::*;`.
pub mod prelude {
    pub use crate::*;
    pub use xark::prelude::*;
}
