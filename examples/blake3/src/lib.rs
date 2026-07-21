//! Prove knowledge of a private message whose BLAKE3 root hash equals a public
//! 256-bit `Hash` (packed into two field halves → 2 public inputs). The gadget
//! result is wrapped in `Blake256` to select the little-endian `Hash` packing
//! that BLAKE's LE word output requires.
#![cfg_attr(xark, no_std)]

use xark_blake3::prelude::*;

#[circuit]
pub fn blake3(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Entry fn shares the gadget's name, so call it by path.
    require_eq(Blake256(xark_blake3::blake3(msg)), digest);
}

#[cfg(test)]
mod tests {
    use super::blake3;

    const MSG: [u8; 3] = *b"abc";

    #[test]
    fn accepts_valid() {
        let digest: [u8; 32] = *blake3_ref::hash(&MSG).as_bytes();
        blake3(MSG, digest).unwrap();
    }

    #[test]
    fn rejects_wrong_digest() {
        let mut digest: [u8; 32] = *blake3_ref::hash(&MSG).as_bytes();
        digest[0] ^= 1;
        assert!(blake3(MSG, digest).is_err());
    }
}
