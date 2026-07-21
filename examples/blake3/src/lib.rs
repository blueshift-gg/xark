//! Prove knowledge of a private message whose BLAKE3 root hash equals a public
//! 256-bit hash — the ergonomic form.
//!
//! The message is a byte array (`[u8; N]`) and the digest a `Hash` — a 256-bit
//! digest packed into two field halves (`xark-hash`), so the circuit exposes just
//! **2 public inputs**. The host still supplies a plain `[u8; 32]`. BLAKE outputs
//! little-endian words, so the gadget result is wrapped in `Blake256` (a
//! blake-crate type) to select the LE `Hash` packing.
#![cfg_attr(xark, no_std)]

use xark_blake3::prelude::*;

#[circuit]
pub fn blake3(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Qualified call: the entry fn shares the gadget's name, so name it by path.
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
