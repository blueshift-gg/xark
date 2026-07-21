//! An ergonomic 256-bit SHA-256 digest wrapper.
//!
//! [`Digest`] hides SHA-256's word/byte/bit bookkeeping so a circuit can compare
//! `sha256(bytes)` against a known value directly:
//!
//! ```rust,ignore
//! use xark_sha256::prelude::*; // re-exports `Digest`
//!
//! const EXPECTED: [u8; 32] = [/* known hash */];
//!
//! #[circuit]
//! pub fn circuit(msg: Private<[u8; N]>) {
//!     let expected: Digest = EXPECTED.into();
//!     Digest::from(sha256(msg)).require_eq(expected);
//! }
//! ```
//!
//! Unlike [`Hash`](crate::Hash), a `Digest` keeps all 256 bits, so a
//! `Public<Digest>` is 256 public inputs — use it for a **constant** expected hash
//! baked into the circuit, and [`Hash`](crate::Hash) for a runtime public digest.
//!
//! ## Layout (must match [`xark_sha256::sha256`])
//!
//! The gadget returns the hash as 8 words. Word `w` covers digest bytes `4w..4w+4`
//! **big-endian**: byte slot `k` (`k = 0` most-significant) occupies word bits
//! `(3-k)*8 .. (3-k)*8+8`, and within a byte the 8 bits are **LSB-first** (matching
//! [`Field::to_bits`]). So hex byte `idx` lands in word `idx/4`, slot `idx%4`, bit
//! `j` at word bit `(3 - idx%4)*8 + j`. [`From<[u8; 32]>`] places bytes there; the
//! KAT test `sha256("abc")` confirms it.

use xark::{CircuitInput, Field, RequireEqCircuit};

/// A 256-bit SHA-256 digest in [`xark_sha256::sha256`]'s native output layout:
/// 8 words × 32 little-endian bits (`[[Field; 32]; 8]`). Build from the gadget
/// output (`Digest::from(sha256(msg))`) or a known constant (`EXPECTED.into()`),
/// then pin them with [`Digest::require_eq`].
///
/// `#[derive(CircuitInput)]` generates `Into<[Field; 256]>` in structural-flatten
/// order (`bits[w][j]` → index `w*32 + j`), so a host input builder's leaf order is
/// guaranteed — not merely disciplined — to match the circuit's.
#[derive(Clone, Copy, CircuitInput)]
pub struct Digest {
    /// 8 words × 32 little-endian bits, identical to the `sha256` gadget output.
    bits: [[Field; 32]; 8],
}

impl Digest {
    /// Constrain this digest equal to `other`, bit-for-bit (256 equality
    /// constraints). Both share the same layout, so it is an element-wise compare.
    pub fn require_eq(self, other: Digest) {
        let mut w = 0usize;
        while w < 8usize {
            let mut j = 0usize;
            while j < 32usize {
                self.bits[w][j].require_eq_circuit(other.bits[w][j]);
                j += 1;
            }
            w += 1;
        }
    }
}

/// Wrap the raw [`xark_sha256::sha256`] output directly — it is already in this
/// type's storage layout, so this is a zero-constraint move.
impl From<[[Field; 32]; 8]> for Digest {
    fn from(bits: [[Field; 32]; 8]) -> Digest {
        Digest { bits }
    }
}

/// `require_eq(sha256(msg), expected: Digest)`: wrap the raw gadget output and
/// compare bit-for-bit against `expected`.
impl RequireEqCircuit<Digest> for [[Field; 32]; 8] {
    #[inline]
    fn require_eq_circuit(self, rhs: Digest) {
        Digest::from(self).require_eq(rhs);
    }
}

/// Compare two digests (e.g. `require_eq(a, b)` where both are already `Digest`).
impl RequireEqCircuit<Digest> for Digest {
    #[inline]
    fn require_eq_circuit(self, rhs: Digest) {
        self.require_eq(rhs);
    }
}

// Pin the derived `Into<[Field; 256]>` arity at compile time — a wrong length
// would fail to resolve here.
const _: fn(Digest) -> [Field; 256] = <Digest as core::convert::Into<[Field; 256]>>::into;

/// Build a **constant** digest from a known 32-byte hash. Each byte is placed into
/// the `sha256` gadget's word/byte/bit slot as `Field` `0`/`1` constants — no
/// witnesses, no constraints. See the module docs for the layout.
impl From<[u8; 32]> for Digest {
    fn from(bytes: [u8; 32]) -> Digest {
        let zero = [Field::from(0u8); 32];
        let mut bits = [zero; 8];
        let mut idx = 0usize;
        while idx < 32usize {
            let b = bytes[idx];
            // Digest byte `idx` → word `idx/4`, big-endian slot `idx%4` (slot 0 is
            // the most-significant), which occupies word bits `(3 - idx%4)*8 ..`.
            let w = idx / 4usize;
            let off = (3usize - (idx % 4usize)) * 8usize;
            // The 8 byte bits are LSB-first (matching `Field::to_bits::<8>`).
            let mut j = 0usize;
            while j < 8usize {
                bits[w][off + j] = Field::from((b >> j) & 1u8);
                j += 1;
            }
            idx += 1;
        }
        Digest { bits }
    }
}
