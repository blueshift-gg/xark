//! `xark-bits`: word-level bit gadgets written entirely in the `Field` subset.
//! Single-element primitives (booleanity, `to_bits`/`from_bits`, and the boolean
//! AND/OR/XOR/NOT) now live as methods on [`xark::Field`]; this crate keeps
//! only the WORD-level layers (`[Field; N]` arrays), built on those methods.
//!
//! Build with `-Zalways-encode-mir` so the compiler can read this crate's MIR
//! across the crate boundary (the workspace `.cargo/config.toml` sets this).

#![no_std]
// Circuit-lowered gadget code: the xark compiler rejects compound assignment on
// `Field` (`+=`/`-=`/`*=`), so `x = x + y` is required — not a clippy oversight.
#![allow(clippy::assign_op_pattern)]

use xark::{assert_eq, Field};

// ===========================================================================
// 32-bit word layer (little-endian bit index: bits[i] has weight 2^i).
//
// This is the building block for word-oriented hashes like SHA-256. Bitwise
// ops work bit-by-bit on `[Field; 32]`; rotations/shifts are pure re-wiring
// (zero gates/constraints); `add32` is modular addition via carry decomposition.
// ===========================================================================

pub fn and32(a: [Field; 32], b: [Field; 32]) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = a[i].and(b[i]);
        i += 1;
    }
    out
}

pub fn xor32(a: [Field; 32], b: [Field; 32]) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = a[i].xor(b[i]);
        i += 1;
    }
    out
}

pub fn or32(a: [Field; 32], b: [Field; 32]) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = a[i].or(b[i]);
        i += 1;
    }
    out
}

pub fn not32(a: [Field; 32]) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = a[i].not();
        i += 1;
    }
    out
}

/// Rotate-right by `n` bits (pure re-wiring, zero gates): `out[i] = a[(i+n) % 32]`.
pub fn rotr32(a: [Field; 32], n: usize) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = a[(i + n) % 32];
        i += 1;
    }
    out
}

/// Shift-right by `n` bits, zero-filling (pure re-wiring, zero gates):
/// `out[i] = a[i+n]` for `i+n < 32`, else `0`.
pub fn shr32(a: [Field; 32], n: usize) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        if i + n < 32 {
            out[i] = a[i + n];
        }
        i += 1;
    }
    out
}

/// Modular addition mod 2^32.
///
/// Adds the two words as field elements (a sum `< 2^33`), decomposes the sum
/// into 33 bits (32 result bits + 1 carry), and returns the low 32 bits. Cost:
/// 33 booleanity gates + 1 recomposition equality.
pub fn add32(a: [Field; 32], b: [Field; 32]) -> [Field; 32] {
    let sum = Field::from_bits::<32>(a) + Field::from_bits::<32>(b);

    // Decompose the 33-bit sum.
    let mut bits = [Field::from(0u8); 33];
    let mut i = 0usize;
    while i < 33 {
        bits[i] = Field::hint_bit(sum, i); // witness-gen: bits[i] = bit(sum, i)
        i += 1;
    }
    let mut i = 0usize;
    while i < 33 {
        bits[i].assert_bool();
        i += 1;
    }
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 33 {
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, sum);

    // Return the low 32 bits (the carry, bits[32], is discarded).
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = bits[i];
        i += 1;
    }
    out
}

/// `(a + b + c) mod 2^32` — a three-input modular add done as a SINGLE 34-bit
/// range-check instead of two chained [`add32`]s.
///
/// The three words sum to `< 3·2^32 < 2^34`, so decomposing the field sum into
/// 34 bits (32 result + 2 carry) and returning the low 32 pins `(a+b+c) mod
/// 2^32` in one gadget. Cost: 34 booleanity gates + 1 recomposition, vs the
/// chain's `2×(33+1) = 68`. Soundness: `formal/Formal/Blake.lean`
/// `add3Mod32_bit_sound` (with `add3Mod32_eq_nested` bridging it to the
/// `addMod32 (addMod32 a b) c` the BLAKE `G` spec uses).
pub fn add3(a: [Field; 32], b: [Field; 32], c: [Field; 32]) -> [Field; 32] {
    let sum = Field::from_bits::<32>(a) + Field::from_bits::<32>(b) + Field::from_bits::<32>(c);

    // Decompose the 34-bit sum.
    let mut bits = [Field::from(0u8); 34];
    let mut i = 0usize;
    while i < 34 {
        bits[i] = Field::hint_bit(sum, i); // witness-gen: bits[i] = bit(sum, i)
        i += 1;
    }
    let mut i = 0usize;
    while i < 34 {
        bits[i].assert_bool();
        i += 1;
    }
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 34 {
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, sum);

    // Return the low 32 bits (the 2 carry bits, bits[32..34], are discarded).
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = bits[i];
        i += 1;
    }
    out
}

// ===========================================================================
// 64-bit word layer (for Keccak-f[1600] and other 64-bit-lane primitives).
// Same conventions as the 32-bit layer: little-endian bit index (bits[i] has
// weight 2^i). Keccak uses only XOR / AND / NOT / rotations (no additions).
// ===========================================================================

/// Decompose `x` into its 64 little-endian bits (boolean-constrained + pinned).
pub fn to_bits64(x: Field) -> [Field; 64] {
    let mut bits = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 64 {
        bits[i] = Field::hint_bit(x, i);
        i += 1;
    }
    let mut i = 0usize;
    while i < 64 {
        bits[i].assert_bool();
        i += 1;
    }
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 64 {
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, x);
    bits
}

/// Recompose 64 little-endian bits into a field element (no gates).
pub fn from_bits64(bits: [Field; 64]) -> Field {
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 64 {
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    acc
}

pub fn and64(a: [Field; 64], b: [Field; 64]) -> [Field; 64] {
    let mut out = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 64 {
        out[i] = a[i].and(b[i]);
        i += 1;
    }
    out
}

pub fn xor64(a: [Field; 64], b: [Field; 64]) -> [Field; 64] {
    let mut out = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 64 {
        out[i] = a[i].xor(b[i]);
        i += 1;
    }
    out
}

pub fn not64(a: [Field; 64]) -> [Field; 64] {
    let mut out = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 64 {
        out[i] = a[i].not();
        i += 1;
    }
    out
}

/// Rotate-left by `n` bits (pure re-wiring, zero gates): in little-endian,
/// `out[i] = a[(i + 64 - (n % 64)) % 64]`. This is Keccak's rho rotation.
pub fn rotl64(a: [Field; 64], n: usize) -> [Field; 64] {
    let m = n % 64;
    let mut out = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 64 {
        out[i] = a[(i + 64 - m) % 64];
        i += 1;
    }
    out
}

/// Rotate-right by `n` bits (pure re-wiring): `out[i] = a[(i + n) % 64]`.
pub fn rotr64(a: [Field; 64], n: usize) -> [Field; 64] {
    let mut out = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 64 {
        out[i] = a[(i + n) % 64];
        i += 1;
    }
    out
}

// ===========================================================================
// Word-array helpers shared by the SHA-256-family hashes (SHA-256/BLAKE2s/BLAKE3).
// ===========================================================================

/// Read the `t`-th 32-bit word out of an `N`-word array (a constant-indexed
/// copy of `arr[t]`).
pub fn read_n<const N: usize>(arr: [[Field; 32]; N], t: usize) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut j = 0usize;
    while j < 32usize {
        out[j] = arr[t][j];
        j += 1;
    }
    out
}

/// The SHA-256 initialization vector (8 words), reused as the BLAKE2s/BLAKE3
/// chaining IV.
pub fn sha256_iv() -> [Field; 8] {
    [
        Field::from(1779033703u32), // 0x6A09E667
        Field::from(3144134277u32), // 0xBB67AE85
        Field::from(1013904242u32), // 0x3C6EF372
        Field::from(2773480762u32), // 0xA54FF53A
        Field::from(1359893119u32), // 0x510E527F
        Field::from(2600822924u32), // 0x9B05688C
        Field::from(528734635u32),  // 0x1F83D9AB
        Field::from(1541459225u32), // 0x5BE0CD19
    ]
}
