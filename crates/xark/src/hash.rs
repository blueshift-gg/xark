//! [`Hash`] — a 256-bit hash carried as **two field elements**, for use as a
//! compact public input.
//!
//! A SHA-256 digest is 256 bits. Exposing it as a [`Digest`](crate::Digest) makes
//! all 256 bits *public inputs* — one field element each, carrying a single bit —
//! which is enormous for a verifier (a scalar-mul per public input) and on-chain
//! (≈32 bytes of calldata each). BN254's scalar field holds ~254 bits, so a
//! 256-bit hash packs losslessly into **2** field elements: the high 16 bytes and
//! the low 16 bytes of the hash read big-endian. `Hash` is that packed pair, so a
//! `Public<Hash>` expected hash is **2** public inputs instead of 256.
//!
//! The gadget's output bits stay internal witnesses (still booleanity-constrained
//! by `sha256`); comparing `sha256(msg)` against a `Hash` recomposes those bits
//! into the two 128-bit halves (`Field::from_bits`, purely linear) and pins each
//! to the corresponding public field — two equality constraints, no new bits.

use crate::lang::{assert_eq, AssertEqCircuit, Field};

/// A 256-bit hash as two field elements: `hi` = the top 16 bytes, `lo` = the low
/// 16 bytes, each read big-endian (so the hash is `hi · 2¹²⁸ + lo`). Used as a
/// **public input** (`Public<Hash>`) so a digest costs 2 public inputs, not 256.
///
/// `#[circuit]` maps a `Public<[u8; 32]>` / `Private<[u8; 32]>` parameter to this,
/// and the host side supplies the two halves (or a 32-byte hex value the CLI
/// packs). The two leaves flatten to `<param>.hi` and `<param>.lo`.
#[derive(Clone, Copy)]
pub struct Hash {
    hi: Field,
    lo: Field,
}

/// Pack a raw `sha256` output (`[[Field; 32]; 8]`, 8 words × 32 little-endian
/// bits) into `(hi, lo)` — the same two 128-bit halves the host derives from the
/// 32-byte hash. Digest bit `bits[w][j]` is bit `j` of word `w`, i.e. hash byte
/// `4w + (3 - j/8)` bit `j%8`, which has weight `2^(224 - 32w + j)` in the hash
/// read as a big-endian integer; bits `0..128` form `lo`, `128..256` form `hi`.
/// `from_bits` is a pure linear recomposition (the bits are already boolean).
fn pack(bits: [[Field; 32]; 8]) -> (Field, Field) {
    let zero = Field::from(0u8);
    let mut packed = [zero; 256];
    let mut w = 0usize;
    while w < 8usize {
        let mut j = 0usize;
        while j < 32usize {
            packed[224usize - 32usize * w + j] = bits[w][j];
            j += 1;
        }
        w += 1;
    }
    let mut lo_bits = [zero; 128];
    let mut hi_bits = [zero; 128];
    let mut i = 0usize;
    while i < 128usize {
        lo_bits[i] = packed[i];
        hi_bits[i] = packed[128usize + i];
        i += 1;
    }
    (
        Field::from_bits::<128>(hi_bits),
        Field::from_bits::<128>(lo_bits),
    )
}

/// Let a `#[circuit]` body write `assert_eq(sha256(msg), expected)` where
/// `expected: Public<Hash>` (2 public inputs): pack the gadget output into its two
/// 128-bit halves and pin each to the expected field. Two equality constraints.
impl AssertEqCircuit<Hash> for [[Field; 32]; 8] {
    #[inline]
    fn assert_eq_circuit(self, rhs: Hash) {
        let (hi, lo) = pack(self);
        assert_eq(hi, rhs.hi);
        assert_eq(lo, rhs.lo);
    }
}

/// Compare two `Hash`es (e.g. both already packed).
impl AssertEqCircuit<Hash> for Hash {
    #[inline]
    fn assert_eq_circuit(self, rhs: Hash) {
        assert_eq(self.hi, rhs.hi);
        assert_eq(self.lo, rhs.lo);
    }
}

/// Pack a Keccak-256 output (`[[Field; 64]; 4]`, 4 lanes × 64 little-endian bits)
/// into `(hi, lo)`. Keccak serializes each 64-bit lane **little-endian**, so lane
/// `w`, bit `i` is bit `i % 8` of hash byte `8w + i/8`, which has weight
/// `2^(8·(31 − (8w + i/8)) + i%8)` in the hash read as a big-endian integer — the
/// same two 128-bit halves the host derives from the 32-byte digest.
fn pack_keccak(lanes: [[Field; 64]; 4]) -> (Field, Field) {
    let zero = Field::from(0u8);
    let mut packed = [zero; 256];
    let mut w = 0usize;
    while w < 4usize {
        let mut i = 0usize;
        while i < 64usize {
            let byte = 8usize * w + i / 8usize;
            packed[8usize * (31usize - byte) + i % 8usize] = lanes[w][i];
            i += 1;
        }
        w += 1;
    }
    let mut lo_bits = [zero; 128];
    let mut hi_bits = [zero; 128];
    let mut i = 0usize;
    while i < 128usize {
        lo_bits[i] = packed[i];
        hi_bits[i] = packed[128usize + i];
        i += 1;
    }
    (
        Field::from_bits::<128>(hi_bits),
        Field::from_bits::<128>(lo_bits),
    )
}

/// Let a `#[circuit]` body write `assert_eq(keccak256(msg), expected)` where
/// `expected: Public<Hash>` — pack the Keccak output's four lanes into the two
/// 128-bit halves and pin each to the expected field.
impl AssertEqCircuit<Hash> for [[Field; 64]; 4] {
    #[inline]
    fn assert_eq_circuit(self, rhs: Hash) {
        let (hi, lo) = pack_keccak(self);
        assert_eq(hi, rhs.hi);
        assert_eq(lo, rhs.lo);
    }
}

/// A BLAKE-family 256-bit digest — 8 words × 32 little-endian bits, whose canonical
/// bytes serialize each word **little-endian** (BLAKE2s and BLAKE3 both do this).
///
/// The raw `[[Field; 32]; 8]` type is shared with SHA-256, which serializes its
/// words **big-endian** — and Rust allows only one `AssertEqCircuit<Hash>` impl per
/// type. So a BLAKE hash output is wrapped in `Blake256` to select the LE packing:
/// `assert_eq(Blake256(blake3(msg)), expected)`.
pub struct Blake256(pub [[Field; 32]; 8]);

/// Pack a BLAKE-family output (`[[Field; 32]; 8]`, LE-serialized words) into
/// `(hi, lo)`. Word `w`, bit `i` is bit `i % 8` of hash byte `4w + i/8`, weight
/// `2^(8·(31 − (4w + i/8)) + i%8)` in the big-endian hash integer.
fn pack_le(words: [[Field; 32]; 8]) -> (Field, Field) {
    let zero = Field::from(0u8);
    let mut packed = [zero; 256];
    let mut w = 0usize;
    while w < 8usize {
        let mut i = 0usize;
        while i < 32usize {
            let byte = 4usize * w + i / 8usize;
            packed[8usize * (31usize - byte) + i % 8usize] = words[w][i];
            i += 1;
        }
        w += 1;
    }
    let mut lo_bits = [zero; 128];
    let mut hi_bits = [zero; 128];
    let mut i = 0usize;
    while i < 128usize {
        lo_bits[i] = packed[i];
        hi_bits[i] = packed[128usize + i];
        i += 1;
    }
    (
        Field::from_bits::<128>(hi_bits),
        Field::from_bits::<128>(lo_bits),
    )
}

/// Let a `#[circuit]` body write `assert_eq(Blake256(blake3(msg)), expected)` where
/// `expected: Public<Hash>` — pack the LE-serialized words into the two 128-bit
/// halves and pin each to the expected field.
impl AssertEqCircuit<Hash> for Blake256 {
    #[inline]
    fn assert_eq_circuit(self, rhs: Hash) {
        let (hi, lo) = pack_le(self.0);
        assert_eq(hi, rhs.hi);
        assert_eq(lo, rhs.lo);
    }
}
