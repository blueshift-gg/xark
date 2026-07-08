//! `xark-aes`: an AES-128 (single 128-bit block, 10 rounds) encryption gadget
//! written entirely in the `xark` `Field` subset, building on the VERIFIED
//! bit layer in `xark-bits`.
//!
//! ## Byte / state representation
//!
//! A byte is a `[Field; 8]` of little-endian bits (bit `i` has weight `2^i`,
//! i.e. bit `i` is the coefficient of `x^i` in the GF(2^8) polynomial basis).
//! The AES state and round keys are flat `[[Field; 8]; N]` arrays of bytes:
//!   * state  = `[[Field; 8]; 16]`, byte index `= row + 4*col` (FIPS-197 column
//!     major; the input block loads directly, no permutation).
//!   * key    = `[[Field; 8]; 16]`.
//!   * expanded key = `[[Field; 8]; 176]`, byte index `= 4*word + byte_in_word`,
//!     so round `k`'s round-key byte at state position `i` is `ek[16*k + i]`.
//!
//! ## S-box approach: GF(2^8) inverse via x^254 (approach A)
//!
//! The AES S-box is `affine(inv(b))` where `inv` is the GF(2^8) multiplicative
//! inverse with `inv(0) = 0`. Since the multiplicative group has order 255,
//! `b^254 = b^-1` for `b != 0`, and `0^254 = 0`, so **`b^254` IS the S-box
//! inverse for all 256 bytes** — no zero special-case, no advice/hint needed.
//! We compute `b^254` with an Itoh–Tsujii addition chain (4 general GF muls + 7
//! GF squares). GF squaring is a *linear* (Frobenius) map over GF(2), so it uses
//! only XOR gates (no AND / R1CS mult gates) and is cheap; the 4 general muls
//! (64 AND gates each) dominate. The fixed GF(2)-affine map is XOR-only.
//!
//! Everything is straight-line: no data-dependent control flow; every `while`
//! loop has a literal bound and is fully unrolled; selection is pure index
//! arithmetic. All additions here are GF(2) XORs — never modular field adds.
//!
//! ## Cost model (only `var * var` products emit an R1CS mult gate)
//!
//! * `gf_mul` = 64 AND (mult) + 64 XOR + 28 reduction XOR.
//! * `gf_square` = 13 XOR (closed-form linear map), 0 AND.
//! * `gf_inv`   = 4 `gf_mul` + 7 `gf_square`.
//! * `sbox`     = `gf_inv` + 32 XOR affine.
//! * `xtime` = 3 XOR; MixColumns / AddRoundKey / ShiftRows are XOR-only / rewiring.

#![no_std]

use xark::{assert_eq, Field};

// ===========================================================================
// GF(2^8) arithmetic on `[Field; 8]` little-endian bit vectors.
// Irreducible polynomial m(x) = x^8 + x^4 + x^3 + x + 1  (AES, 0x11B).
// ===========================================================================

/// Reduce a 15-coefficient GF(2) polynomial (product of two bytes) modulo the
/// AES irreducible `m(x)`, returning the 8 low bits. Uses `x^8 ≡ x^4+x^3+x+1`:
/// a coefficient at position `pos >= 8` folds (XORs) into positions
/// `pos-8, pos-7, pos-5, pos-4`. Folding high→low so cascaded carries settle.
fn gf_reduce(p_in: [Field; 15]) -> [Field; 8] {
    let mut p = [Field::from(0u8); 15];
    let mut i = 0usize;
    while i < 15usize {
        p[i] = p_in[i];
        i += 1;
    }
    let mut step = 0usize;
    while step < 7usize {
        let pos = 14usize - step; // 14,13,...,8
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
            p[i + j] = p[i + j].xor(prod); // XOR into the (i+j) coefficient
            j += 1;
        }
        i += 1;
    }
    gf_reduce(p)
}

/// GF(2^8) squaring: in characteristic 2 this is the linear Frobenius map
/// `(Σ a_i x^i)^2 = Σ a_i x^{2i}` (cross terms vanish), so it is XOR-only (no AND
/// gates). Closed form after reduction mod `m(x)` (derived once, validated
/// against `gf_mul(a,a)` via the S-box table test):
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

// ===========================================================================
// Whole-byte reads from flat nested arrays (rebuilt bit-by-bit — reading a whole
// inner `[Field; 8]` out of a nested array is not supported by the subset).
// ===========================================================================

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

// ===========================================================================
// AES round operations. Each returns a fresh state (no in-place mutation of a
// borrowed array; arrays are Copy and passed by value).
// ===========================================================================

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
fn add_round_key(s: [[Field; 8]; 16], ek: [[Field; 8]; 176], round: usize) -> [[Field; 8]; 16] {
    let mut o = [[Field::from(0u8); 8]; 16];
    let mut i = 0usize;
    while i < 16usize {
        let kb = rd176(ek, 16usize * round + i);
        let mut j = 0usize;
        while j < 8usize {
            o[i][j] = s[i][j].xor(kb[j]);
            j += 1;
        }
        i += 1;
    }
    o
}

// ===========================================================================
// Key expansion: 44 words (176 bytes) from the 16-byte key.
// ===========================================================================

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
fn round(s: [[Field; 8]; 16], ek: [[Field; 8]; 176], k: usize) -> [[Field; 8]; 16] {
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

/// Encrypt and `assert_eq` each ciphertext byte to the provided public
/// output bytes.
pub fn aes128_constrain(pt: [Field; 16], key: [Field; 16], ct: [Field; 16]) {
    let out = aes128_encrypt_bytes(pt, key);
    let mut i = 0usize;
    while i < 16usize {
        assert_eq(out[i], ct[i]);
        i += 1;
    }
}
