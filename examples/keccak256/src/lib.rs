//! Prove knowledge of a private message whose Keccak-256 (Ethereum `keccak256`)
//! digest equals a public 256-bit hash. The digest is a `Hash` — 256 bits packed
//! into two field halves (`xark-hash`), so the circuit exposes just 2 public
//! inputs; the host still supplies a plain `[u8; 32]`.
#![cfg_attr(xark, no_std)]

use xark_keccak::prelude::*;

#[circuit]
pub fn keccak256(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Qualified call: the entry fn shares the gadget's name, so name it by path.
    require_eq(xark_keccak::keccak256(msg), digest);
}

#[cfg(test)]
mod tests {
    use super::keccak256;
    use sha3::{Digest, Keccak256};

    const MSG: [u8; 3] = *b"abc";

    #[test]
    fn accepts_valid() {
        let digest: [u8; 32] = Keccak256::digest(MSG).into();
        keccak256(MSG, digest).unwrap();
    }

    #[test]
    fn rejects_wrong_digest() {
        let mut digest: [u8; 32] = Keccak256::digest(MSG).into();
        digest[0] ^= 1;
        assert!(keccak256(MSG, digest).is_err());
    }
}
