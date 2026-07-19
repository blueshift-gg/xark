//! secp256r1 (NIST P-256) ECDSA verification as a `#[circuit]`, over the shared
//! 3×86-bit Weierstrass gadget. The public key and signature are transparent
//! types (`Point` = compact uncompressed `[u8; 64]` `x ‖ y`, `Fq` = `[u8; 32]`),
//! so a test/prover calls `ecdsa_verify_r1(q, r, s, e)` with the exact bytes
//! `p256` emits — no limb splitting, no input JSON.
#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Public};
use xark_secp256r1::{ecdsa_verify as verify_gadget, Fq, Point};

#[circuit]
pub fn ecdsa_verify_r1(q: Public<Point>, r: Public<Fq>, s: Public<Fq>, e: Public<Fq>) {
    verify_gadget(q, r, s, e);
}

#[cfg(test)]
mod tests {
    use super::ecdsa_verify_r1;
    use p256::ecdsa::{signature::Signer, Signature, SigningKey};
    use sha2::{Digest, Sha256};
    use xark_secp256r1::reduce_scalar;

    fn parts() -> ([u8; 64], [u8; 32], [u8; 32], [u8; 32]) {
        let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
        let vk = sk.verifying_key();
        let msg = b"xark secp256r1 ecdsa vector";
        let sig: Signature = sk.sign(msg);
        let enc = vk.to_encoded_point(false);
        let q: [u8; 64] = enc.as_bytes()[1..].try_into().unwrap(); // drop 0x04 tag
        let sb = sig.to_bytes();
        let (r, s): ([u8; 32], [u8; 32]) =
            (sb[..32].try_into().unwrap(), sb[32..].try_into().unwrap());
        let e = reduce_scalar(&Sha256::digest(msg));
        (q, r, s, e)
    }

    #[test]
    fn accepts_valid() {
        let (q, r, s, e) = parts();
        ecdsa_verify_r1(q, r, s, e).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let (q, _r, s, e) = parts();
        let mut bad_r = [0u8; 32];
        bad_r[31] = 1; // wrong r
        assert!(ecdsa_verify_r1(q, bad_r, s, e).is_err());
    }
}
