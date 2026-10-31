//! `xark-bits`: word-level bit gadgets written entirely in the `Field` subset.
//! Single-element primitives (booleanity, `to_bits`/`from_bits`, and the boolean
//! AND/OR/XOR/NOT) now live as methods on [`xark::Field`]; this crate keeps
//! only the WORD-level layers (`[Field; N]` arrays), built on those methods.

#![no_std]
// Gadget code keeps the `x = x + y` style it was written in (the old compiler
// rejected `+=` on `Field`; the wasm frontend accepts both).
#![allow(clippy::assign_op_pattern)]

use xark::{Field, gadget, require_eq};

// 32-bit word layer (little-endian bit index: bits[i] has weight 2^i), the
// building block for SHA-256-style hashes. Bitwise ops are bit-by-bit on
// `[Field; 32]`; rotations/shifts are pure re-wiring (zero gates); `add32` is
// modular addition via carry decomposition.

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
/// 33 booleanity gates + 1 recomposition equality. The rows it emits on fresh
/// inputs are proven sound and complete in `formal/Formal/Add32.lean`
/// (`cargo xtask lean-export add32`).
#[gadget]
pub fn add32(a: [Field; 32], b: [Field; 32]) -> [Field; 32] {
    let sum = Field::from_bits::<32>(a) + Field::from_bits::<32>(b);

    // Decompose the 33-bit sum.
    let mut bits = [Field::from(0u8); 33];
    let mut i = 0usize;
    while i < 33 {
        bits[i] = Field::hint_bit(sum, i);
        i += 1;
    }
    let mut i = 0usize;
    while i < 33 {
        bits[i].require_bool();
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
    require_eq(acc, sum);

    // Return the low 32 bits (the carry, bits[32], is discarded).
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = bits[i];
        i += 1;
    }
    out
}

/// `(a + b + c) mod 2^32`: the three words' field sum (`< 3·2^32 < 2^34`) reduced
/// once by [`reduce::<34>`](reduce), 34 rows, against two chained [`add32`]s' 68.
pub fn add3(a: [Field; 32], b: [Field; 32], c: [Field; 32]) -> [Field; 32] {
    reduce::<34>(Field::from_bits::<32>(a) + Field::from_bits::<32>(b) + Field::from_bits::<32>(c))
}

/// The low 32 bits of `sum`, requiring `sum < 2^N` (`33 ≤ N ≤ 253`): the modular
/// reduction of a sum of `k` words of bits, `N = 32 + ⌈log₂ k⌉`. Bits `0..N−1` are
/// hinted and pinned boolean, and the top carry is what they leave,
/// `t = sum − Σᵢ<N−1 2ⁱ·bᵢ`, pinned by the one row `t·(t − 2^(N−1)) = 0`: `N` rows
/// and `N − 1` variables, one of each fewer than a full decomposition and its
/// recomposition row (zkGolf 650c4497 / 3e1e47a3, "fused carry"). `2^N < r` makes
/// the bits unique. Proven sound with no input assumption and complete for
/// `sum < 2^N` in `formal/Formal/Reduce.lean`.
#[gadget]
pub fn reduce<const N: usize>(sum: Field) -> [Field; 32] {
    // 2^N < r (bug checklist 3, 9); the output bits are all hinted (N − 1 ≥ 32).
    const { assert!(N >= 33 && N <= 253, "reduce::<N>: need 33 <= N <= 253") };
    let mut bits = [Field::from(0u8); 252];
    let mut i = 0usize;
    while i < N - 1 {
        bits[i] = Field::hint_bit(sum, i);
        i += 1;
    }
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < N - 1 {
        bits[i].require_bool();
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    // `pow` is 2^(N−1): the top carry is 0 or that.
    let top = sum - acc;
    require_eq(top * (top - pow), Field::from(0u8));
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = bits[i];
        i += 1;
    }
    out
}

// Single-row three-input bit functions (zkGolf T1/T2, Verified-zkEVM/clean PR #395,
// https://github.com/Verified-zkEVM/clean/pull/395, and zkGolf f8fd1e03 for χ). On
// bits `a, b, c` each row `(z + L)·M = R` is linear in the hinted `z`, with a
// multiplier `M` that is nonzero (±1…±4) on {0,1}³, so it has one root: the target
// bit. Proven in `formal/Formal/HashOps.lean`. The inputs must be bits (callers pass
// `to_bits`/`reduce` outputs or earlier bit gadgets' results): on other inputs the
// row may have no root (`xor3`, `maj3`) or leave `z` free (`chi` at `(0, 0, 3)`).

/// `a ⊕ b ⊕ c` in one row `(z + 2a + 2b + 7c)·(a + b − 4c + 1) = 6a + 6b − 24c`.
#[gadget]
pub fn xor3(a: Field, b: Field, c: Field) -> Field {
    let z = Field::hint_bit(a + b + c, 0);
    let k = |n: u8| Field::from(n);
    require_eq(
        (z + k(2) * a + k(2) * b + k(7) * c) * (a + b - k(4) * c + k(1)),
        k(6) * a + k(6) * b - k(24) * c,
    );
    z
}

/// `maj(a, b, c)` in one row `(z + a + b − 9c + 3)·(a + b + 6c − 4) = −12`.
#[gadget]
pub fn maj3(a: Field, b: Field, c: Field) -> Field {
    let z = Field::hint_bit(a + b + c, 1);
    let k = |n: u8| Field::from(n);
    require_eq(
        (z + a + b - k(9) * c + k(3)) * (a + b + k(6) * c - k(4)),
        k(0) - k(12),
    );
    z
}

/// Keccak's χ bit `a ⊕ (¬b ∧ c)` in one row `(z + 3a − b − c)·(4a + b + c − 3) = 4a + 2b`.
/// `a`, `b` and `c` must be bits: at `(0, 0, 3)` the row leaves `z` free.
#[gadget]
pub fn chi(a: Field, b: Field, c: Field) -> Field {
    let k = |n: u8| Field::from(n);
    let z = Field::hint_bit(k(2) * a + k(1) - b + c, 1);
    require_eq(
        (z + k(3) * a - b - c) * (k(4) * a + b + c - k(3)),
        k(4) * a + k(2) * b,
    );
    z
}

/// SHA-256's choice bit `e ? f : g` as `g + e·(f − g)`: one product, the output a
/// linear form (zkGolf T3; bellman `Boolean::sha256_ch`, "a(b−c) = ch−c",
/// https://github.com/zkcrypto/bellman/blob/b726862a4ece8a627e7fea486d77b502a6edbb0b/src/gadgets/boolean.rs#L511-L615).
#[gadget]
pub fn ch(e: Field, f: Field, g: Field) -> Field {
    g + e * (f - g)
}

/// [`xor3`] bit by bit.
pub fn xor3_32(a: [Field; 32], b: [Field; 32], c: [Field; 32]) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = xor3(a[i], b[i], c[i]);
        i += 1;
    }
    out
}

/// [`xor3`] bit by bit, on 64-bit lanes.
pub fn xor3_64(a: [Field; 64], b: [Field; 64], c: [Field; 64]) -> [Field; 64] {
    let mut out = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 64 {
        out[i] = xor3(a[i], b[i], c[i]);
        i += 1;
    }
    out
}

// 64-bit word layer (Keccak-f[1600] and other 64-bit lanes). Same little-endian
// conventions as the 32-bit layer. Keccak uses only XOR/AND/NOT/rotations.

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
        bits[i].require_bool();
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
    require_eq(acc, x);
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

// Word-array helpers shared by the SHA-256-family hashes (SHA-256/BLAKE2s/BLAKE3).

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
