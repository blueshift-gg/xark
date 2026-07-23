//! secp256k1 ECDSA verification as a `#[circuit]` via the GLV gadget (128-window
//! 4-dim Shamir over the λ-endomorphism), ~1.64M constraints. Inputs are
//! transparent compound types: `Point` = `[u8; 64]` `x ‖ y`, `Signature` = `[u8;
//! 64]` `r ‖ s`, `Scalar` = digest `int(hash(msg)) mod n` (`[u8; 32]`). The GLV
//! endomorphism decomposition is derived inside the circuit (a `witness_only`
//! region at zero constraint cost, pinned by `glv_decomp`), so the caller supplies
//! only the signature.

use xark_secp256k1::prelude::*;

#[circuit]
pub fn secp256k1_ecdsa(pubkey: Public<Point>, sig: Public<Signature>, digest: Public<Scalar>) {
    pubkey.verify(sig, digest);
}

#[cfg(test)]
mod tests {
    use super::secp256k1_ecdsa;
    use k256::ecdsa::{Signature as K256Sig, SigningKey, signature::Signer};
    use sha2::{Digest, Sha256};
    use xark_secp256k1::reduce_scalar;

    /// A real k256 signature as native `(pubkey, sig, digest)` bytes.
    fn parts() -> ([u8; 64], [u8; 64], [u8; 32]) {
        let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
        let vk = sk.verifying_key();
        let msg = b"xark secp256k1 ecdsa vector";
        let sig: K256Sig = sk.sign(msg);
        let enc = vk.to_encoded_point(false);
        let pubkey: [u8; 64] = enc.as_bytes()[1..].try_into().unwrap(); // drop 0x04 tag
        let sig_bytes: [u8; 64] = sig.to_bytes().into();
        let digest = reduce_scalar(&Sha256::digest(msg));
        (pubkey, sig_bytes, digest)
    }

    #[test]
    fn accepts_valid() {
        let (pubkey, sig, digest) = parts();
        secp256k1_ecdsa(pubkey, sig, digest).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let (pubkey, mut sig, digest) = parts();
        sig[0] ^= 1;
        assert!(secp256k1_ecdsa(pubkey, sig, digest).is_err());
    }

    #[test]
    fn rejects_off_curve_pubkey() {
        // The gadget's internal on-curve check must reject an off-curve pubkey.
        let (mut pubkey, sig, digest) = parts();
        pubkey[63] ^= 1;
        assert!(secp256k1_ecdsa(pubkey, sig, digest).is_err());
    }
}
