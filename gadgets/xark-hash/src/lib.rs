//! `xark-hash` — shared 256-bit digest types for the hash gadgets.
//!
//! [`Hash`] packs a 256-bit digest into two field elements (a compact 2-input
//! public form); [`Digest`] keeps all 256 bits (bit-exact). Both, and the
//! `RequireEqCircuit<…>` impls comparing a raw gadget output against them, live
//! here (not in the `xark` core) because coherence requires them where `Hash` is
//! defined. BLAKE's little-endian wrapper is a local type, so it lives in the
//! blake crates, built on the public [`Hash::pack`] primitive.
#![no_std]

use xark::{Field, RequireEqCircuit, require_eq};

pub mod digest;
pub use digest::Digest;

/// A 256-bit hash as two field elements: `hi` = the top 16 bytes, `lo` = the low
/// 16 bytes, each read big-endian (so the hash is `hi · 2¹²⁸ + lo`). Used as a
/// `Public<Hash>` so a digest costs 2 public inputs, not 256. The two fields
/// flatten to `<param>.hi` / `<param>.lo`.
#[derive(Clone, Copy)]
pub struct Hash {
    hi: Field,
    lo: Field,
}

impl Hash {
    /// Recompose 256 weighted bits into the packed pair `hi · 2¹²⁸ + lo`: `bits[i]`
    /// is bit `i` of the hash as a big-endian integer (weight `2ⁱ`), so bits
    /// `0..128` form `lo` and `128..256` form `hi`. Pure linear recomposition; each
    /// gadget permutes its raw output into this weight order before calling `pack`.
    pub fn pack(bits: [Field; 256]) -> Hash {
        let zero = Field::from(0u8);
        let mut lo_bits = [zero; 128];
        let mut hi_bits = [zero; 128];
        let mut i = 0usize;
        while i < 128usize {
            lo_bits[i] = bits[i];
            hi_bits[i] = bits[128usize + i];
            i += 1;
        }
        Hash {
            hi: Field::from_bits::<128>(hi_bits),
            lo: Field::from_bits::<128>(lo_bits),
        }
    }
}

/// Compare two `Hash`es (both already packed) — two equality constraints.
impl RequireEqCircuit<Hash> for Hash {
    #[inline]
    fn require_eq_circuit(self, rhs: Hash) {
        require_eq(self.hi, rhs.hi);
        require_eq(self.lo, rhs.lo);
    }
}

/// `require_eq(sha256(msg), expected: Public<Hash>)`. SHA-256 serializes each
/// 32-bit word **big-endian**, so word `w` bit `j` (`bits[w][j]`, LSB-first) has
/// weight `2^(224 − 32w + j)` in the big-endian hash integer. Permute to that
/// order and pack into the two 128-bit halves.
impl RequireEqCircuit<Hash> for [[Field; 32]; 8] {
    #[inline]
    fn require_eq_circuit(self, rhs: Hash) {
        let mut bits = [Field::from(0u8); 256];
        let mut w = 0usize;
        while w < 8usize {
            let mut j = 0usize;
            while j < 32usize {
                bits[224usize - 32usize * w + j] = self[w][j];
                j += 1;
            }
            w += 1;
        }
        Hash::pack(bits).require_eq_circuit(rhs);
    }
}

/// `require_eq(keccak256(msg), expected: Public<Hash>)`. Keccak serializes each
/// 64-bit lane **little-endian**, so lane `w` bit `i` is bit `i % 8` of hash byte
/// `8w + i/8`, weight `2^(8·(31 − (8w + i/8)) + i%8)` in the big-endian hash integer.
impl RequireEqCircuit<Hash> for [[Field; 64]; 4] {
    #[inline]
    fn require_eq_circuit(self, rhs: Hash) {
        let mut bits = [Field::from(0u8); 256];
        let mut w = 0usize;
        while w < 4usize {
            let mut i = 0usize;
            while i < 64usize {
                let byte = 8usize * w + i / 8usize;
                bits[8usize * (31usize - byte) + i % 8usize] = self[w][i];
                i += 1;
            }
            w += 1;
        }
        Hash::pack(bits).require_eq_circuit(rhs);
    }
}

// Host-side `NativeInput`: a `Hash` input is a 32-byte hash split into its two
// 128-bit halves `hi`/`lo` (big-endian) as `<name>.hi` / `<name>.lo` leaves.
// `std` is pulled in inside an anonymous const because this crate is `#![no_std]`.
#[cfg(not(xark))]
const _: () = {
    extern crate std;
    use std::string::{String, ToString};
    use std::vec::Vec;
    impl xark_prover::NativeInput for Hash {
        type Native = [u8; 32];
        fn leaves(native: &Self::Native, prefix: &str) -> Vec<(String, String)> {
            let mut hi = 0u128;
            let mut k = 0usize;
            while k < 16usize {
                hi = (hi << 8) | (native[k] as u128);
                k += 1;
            }
            let mut lo = 0u128;
            while k < 32usize {
                lo = (lo << 8) | (native[k] as u128);
                k += 1;
            }
            std::vec![
                (std::format!("{prefix}.hi"), hi.to_string()),
                (std::format!("{prefix}.lo"), lo.to_string()),
            ]
        }
    }
};
