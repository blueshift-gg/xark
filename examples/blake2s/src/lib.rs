//! Prove knowledge of a private message whose unkeyed BLAKE2s-256 digest equals
//! a public 256-bit hash — the ergonomic form.
//!
//! The message is a byte array (`[u8; N]`) and the digest a `Hash` — a 256-bit
//! digest packed into two field halves (`xark-hash`), so the circuit exposes just
//! **2 public inputs**. The host still supplies a plain `[u8; 32]`. BLAKE outputs
//! little-endian words, so the gadget result is wrapped in `Blake256` (a
//! blake-crate type) to select the LE `Hash` packing.
#![cfg_attr(xark, no_std)]

use xark_blake2s::prelude::*;

#[circuit]
pub fn blake2s(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Qualified call: the entry fn shares the gadget's name, so name it by path.
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
