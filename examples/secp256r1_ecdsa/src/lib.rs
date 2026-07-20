//! secp256r1 (NIST P-256) ECDSA verification as a `#[circuit]`, over the shared
//! 3×86-bit Weierstrass gadget. Inputs are transparent compound types you pass
//! straight through — no limbs, no plumbing:
//!
//! ```ignore
//! pubkey.verify(sig, digest);
//! ```
//!
//! `Point` = compact uncompressed public key (`[u8; 64]` `x ‖ y`), `Signature` =
//! `(r, s)` (`[u8; 64]` `r ‖ s`), `Scalar` = the message digest `int(hash(msg)) mod n`
//! (`[u8; 32]`) — the exact bytes `p256` emits.
#![cfg_attr(xark, no_std)]

use xark_secp256r1::prelude::*;

#[circuit]
pub fn secp256r1_ecdsa(pubkey: Public<Point>, sig: Public<Signature>, digest: Public<Scalar>) {
    pubkey.verify(sig, digest);
}

#[cfg(test)]
mod tests {
    use super::secp256r1_ecdsa;
    use p256::ecdsa::{signature::Signer, Signature as P256Sig, SigningKey};
    use sha2::{Digest, Sha256};
    use xark_secp256r1::reduce_scalar;

    /// A real p256 signature as the native `(pubkey, sig, digest)` byte forms:
    /// `Point` = `[u8; 64]` (`x ‖ y`), `Signature` = `[u8; 64]` (`r ‖ s`), `Scalar`
    /// = `[u8; 32]`.
    fn parts() -> ([u8; 64], [u8; 64], [u8; 32]) {
        let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
        let vk = sk.verifying_key();
        let msg = b"xark secp256r1 ecdsa vector";
        let sig: P256Sig = sk.sign(msg);
        let enc = vk.to_encoded_point(false);
        let pubkey: [u8; 64] = enc.as_bytes()[1..].try_into().unwrap(); // drop 0x04 tag
        let sig_bytes: [u8; 64] = sig.to_bytes().as_slice().try_into().unwrap(); // r ‖ s
        let digest = reduce_scalar(&Sha256::digest(msg));
        (pubkey, sig_bytes, digest)
    }

    #[test]
    fn accepts_valid() {
        let (pubkey, sig, digest) = parts();
        secp256r1_ecdsa(pubkey, sig, digest).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let (pubkey, mut sig, digest) = parts();
        sig[0] ^= 1; // corrupt r
        assert!(secp256r1_ecdsa(pubkey, sig, digest).is_err());
    }
}
