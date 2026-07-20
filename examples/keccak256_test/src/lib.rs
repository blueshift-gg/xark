//! Native-typed `#[circuit]` inputs over Keccak-256 — prove knowledge of a
//! pre-image of an Ethereum `keccak256` digest.
//!
//! The expected digest is computed with the `sha3` crate's `Keccak256` (the
//! Ethereum-flavour Keccak that `xark-keccak` implements), like the SHA-256
//! example checks against `sha2` — no hardcoded value. `[u8; 32]` maps to a packed
//! `Hash` (2 field public inputs), and the Keccak output's four 64-bit lanes are
//! packed into the same two halves via each lane's little-endian byte order.

#![cfg_attr(xark, no_std)]

use xark::{circuit, Private, Public};
use xark_keccak::keccak256;

#[circuit]
pub fn keccak256_test(input: Private<[u8; 3]>, result: Public<[u8; 32]>) {
    assert_eq(keccak256(input), result);
}

#[cfg(test)]
mod tests {
    use super::keccak256_test;
    use sha3::{Digest, Keccak256};

    #[test]
    fn accepts_valid() {
        let result: [u8; 32] = Keccak256::digest("abc").into();
        keccak256_test(*b"abc", result).unwrap();
    }

    #[test]
    fn rejects_invalid() {
        let mut result: [u8; 32] = Keccak256::digest("abc").into();
        result[0] ^= 1;
        assert!(keccak256_test(*b"abc", result).is_err());
    }
}
