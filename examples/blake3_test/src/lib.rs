//! Native-typed `#[circuit]` inputs over BLAKE3 — prove knowledge of a pre-image
//! of a BLAKE3 digest, validated against the `blake3` crate (no hardcoded value).
//!
//! BLAKE3 serializes its 8 output words **little-endian**, so its `[[Field;32];8]`
//! output is wrapped in [`xark::Blake256`] to select the LE `Hash` packing (vs
//! SHA-256's big-endian).

#![cfg_attr(xark, no_std)]

use xark::{circuit, Blake256, Private, Public};
use xark_blake3::blake3;

#[circuit]
pub fn blake3_test(input: Private<[u8; 3]>, result: Public<[u8; 32]>) {
    assert_eq(Blake256(blake3(input)), result);
}

#[cfg(test)]
mod tests {
    use super::blake3_test;

    fn reference(msg: &[u8]) -> [u8; 32] {
        *::blake3::hash(msg).as_bytes()
    }

    #[test]
    fn accepts_valid() {
        blake3_test(*b"abc", reference(b"abc")).unwrap();
    }

    #[test]
    fn rejects_invalid() {
        let mut wrong = reference(b"abc");
        wrong[0] ^= 1;
        assert!(blake3_test(*b"abc", wrong).is_err());
    }
}
