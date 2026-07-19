//! secp256k1 ECDSA verification as a `#[circuit]` — the GLV gadget (128-window
//! 4-dim Shamir via the λ-endomorphism), secp256k1's single `ecdsa_verify`
//! (~1.64M constraints). The public key/signature are transparent types (`Point4`
//! = compact uncompressed `[u8; 64]` `x ‖ y`, `Fq4` = `[u8; 32]`).
//!
//! The endomorphism decomposition the GLV algorithm needs is **derived inside the
//! circuit** — the gadget runs the lattice reduction in a `witness_only` region
//! (zero constraint cost) and pins the result with its `glv_decomp` check. So the
//! caller supplies only the signature `(q, r, s, e)`; there are no hint inputs to
//! pass, and nothing derivable leaks into the public statement.
#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Public};
use xark_secp256k1::{ecdsa_verify as verify_gadget, Fq4, Point4};

#[circuit]
pub fn secp256k1_ecdsa(q: Public<Point4>, r: Public<Fq4>, s: Public<Fq4>, e: Public<Fq4>) {
    verify_gadget(q.x.limbs, q.y.limbs, r.limbs, s.limbs, e.limbs);
}

#[cfg(test)]
mod tests {
    use super::secp256k1_ecdsa;
    use k256::ecdsa::{signature::Signer, Signature, SigningKey};
    use sha2::{Digest, Sha256};
    use xark_secp256k1::reduce_scalar;

    fn parts() -> ([u8; 64], [u8; 32], [u8; 32], [u8; 32]) {
        let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
        let vk = sk.verifying_key();
        let msg = b"xark secp256k1 ecdsa vector";
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
        secp256k1_ecdsa(q, r, s, e).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let (q, _r, s, e) = parts();
        let mut bad_r = [0u8; 32];
        bad_r[31] = 1; // wrong r
        assert!(secp256k1_ecdsa(q, bad_r, s, e).is_err());
    }

    #[test]
    fn rejects_off_curve_pubkey() {
        // The gadget's internal on-curve check must reject a public key that isn't
        // on secp256k1 (perturb a y-coordinate byte). This is the coverage the old
        // standalone `on_curve_k1` example gave, but on the gadget's real 4×64 check.
        let (mut q, r, s, e) = parts();
        q[63] ^= 1;
        assert!(secp256k1_ecdsa(q, r, s, e).is_err());
    }
}
