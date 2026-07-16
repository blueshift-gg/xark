//! Native-typed `#[circuit]` inputs over BLAKE2s — prove knowledge of a pre-image
//! of a BLAKE2s-256 digest, validated against the `blake2` crate (no hardcoded
//! value).
//!
//! BLAKE2s serializes its 8 output words **little-endian**, so its `[[Field;32];8]`
//! output is wrapped in [`xark::Blake256`] to select the LE `Hash` packing.

#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Blake256, Private, Public};
use xark_blake2s::blake2s;

#[circuit]
pub fn blake2s_test(input: Private<[u8; 3]>, result: Public<[u8; 32]>) {
    assert_eq(Blake256(blake2s(input)), result);
}

#[cfg(test)]
mod tests {
    use super::blake2s_test;
    use blake2::{Blake2s256, Digest};

    fn reference(msg: &[u8]) -> [u8; 32] {
        Blake2s256::digest(msg).into()
    }

    #[test]
    fn accepts_valid() {
        blake2s_test(*b"abc", reference(b"abc")).unwrap();
    }

    #[test]
    fn rejects_invalid() {
        let mut wrong = reference(b"abc");
        wrong[0] ^= 1;
        assert!(blake2s_test(*b"abc", wrong).is_err());
    }
}
