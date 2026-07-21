//! Prove knowledge of a private message whose SHA-256 digest equals a public
//! 256-bit hash — the ergonomic form.
//!
//! The message is a byte array (`[u8; N]`) and the digest a `Hash` — a 256-bit
//! digest packed into two 128-bit field halves (`xark-hash`), so the whole circuit
//! exposes just **2 public inputs** instead of eight 32-bit words. The host still
//! supplies a plain `[u8; 32]` (`Hash`'s native form). `require_eq` compares the
//! gadget's raw bit output against that packed `Hash` directly.
#![cfg_attr(xark, no_std)]

use xark_sha256::prelude::*;

#[circuit]
pub fn sha256(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Qualified call: the entry fn shares the gadget's name, so name it by path.
    require_eq(xark_sha256::sha256(msg), digest);
}

#[cfg(test)]
mod tests {
    use super::sha256;
    use sha2::{Digest, Sha256};

    const MSG: [u8; 3] = *b"abc";

    #[test]
    fn accepts_valid() {
        let digest: [u8; 32] = Sha256::digest(MSG).into();
        sha256(MSG, digest).unwrap();
    }

    #[test]
    fn rejects_wrong_digest() {
        let mut digest: [u8; 32] = Sha256::digest(MSG).into();
        digest[0] ^= 1;
        assert!(sha256(MSG, digest).is_err());
    }
}
