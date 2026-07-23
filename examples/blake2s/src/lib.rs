//! Prove knowledge of a private message whose unkeyed BLAKE2s-256 digest equals
//! a public 256-bit `Hash` (packed into two field halves → 2 public inputs).
//! The gadget result is wrapped in `Blake256` to select the little-endian `Hash`
//! packing that BLAKE's LE word output requires.

use xark_blake2s::prelude::*;

#[circuit]
pub fn blake2s(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Entry fn shares the gadget's name, so call it by path.
    require_eq(Blake256(xark_blake2s::blake2s(msg)), digest);
}

#[cfg(test)]
mod tests {
    use super::blake2s;
    use blake2::{Blake2s256, Digest};

    const MSG: [u8; 3] = *b"abc";

    #[test]
    fn accepts_valid() {
        let digest: [u8; 32] = Blake2s256::digest(MSG).into();
        blake2s(MSG, digest).unwrap();
    }

    #[test]
    fn rejects_wrong_digest() {
        let mut digest: [u8; 32] = Blake2s256::digest(MSG).into();
        digest[0] ^= 1;
        assert!(blake2s(MSG, digest).is_err());
    }
}
