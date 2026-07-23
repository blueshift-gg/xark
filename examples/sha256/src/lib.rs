//! Prove knowledge of a private message whose SHA-256 digest equals a public
//! 256-bit hash. The digest is a `Hash` — packed into two 128-bit field halves
//! (`xark-hash`), so the circuit exposes just 2 public inputs instead of eight
//! 32-bit words. The host supplies a plain `[u8; 32]` (`Hash`'s native form).

use xark_sha256::prelude::*;

#[circuit]
pub fn sha256(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Qualified: the entry fn shares the gadget's name.
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
