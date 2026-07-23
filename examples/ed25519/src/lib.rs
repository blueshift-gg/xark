//! Ed25519 signature verification as a `#[circuit]`: a succinct proof that the
//! EdDSA equation `[S]·B == R + [k]·A` holds, via a sound lazy extended-coordinate
//! path (~2.36M constraints vs the affine gadget's 4.55M). Inputs pass straight
//! through: `PointL` = compressed 32-byte pubkey `A`, `Signature` = `(R, S)` as
//! `[u8; 64]` (compressed `R ‖ big-endian S`), `Scalar` = the challenge
//! `k = SHA-512(R ‖ A ‖ M) mod L` (a prover-supplied witness).

use xark_ed25519::prelude::*;

#[circuit]
pub fn ed25519(pubkey: Public<PointL>, sig: Public<Signature>, digest: Public<Scalar>) {
    pubkey.verify(sig, digest);
}

#[cfg(test)]
mod tests {
    use super::ed25519;
    use ed25519_dalek::{Signer, SigningKey};
    use xark_ed25519::{challenge, scalar_le_to_be};

    const MSG: &[u8] = b"xark ed25519 eddsa vector";

    /// `(pubkey, sig)` from a real signature: compressed `A` and `[u8; 64]`
    /// (compressed `R ‖ big-endian S`).
    fn parts() -> ([u8; 32], [u8; 64]) {
        let sk = SigningKey::from_bytes(&[0x42u8; 32]);
        let pubkey = sk.verifying_key().to_bytes();
        let raw = sk.sign(MSG).to_bytes(); // R(32) ‖ S(32, little-endian)
        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(&raw[..32]); // compressed R
        sig[32..].copy_from_slice(&scalar_le_to_be(&raw[32..].try_into().unwrap())); // S big-endian
        (pubkey, sig)
    }

    #[test]
    fn accepts_valid() {
        let (pubkey, sig) = parts();
        let r: [u8; 32] = sig[..32].try_into().unwrap();
        let k = challenge(&r, &pubkey, MSG);
        ed25519(pubkey, sig, k).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let (pubkey, sig) = parts();
        let r: [u8; 32] = sig[..32].try_into().unwrap();
        // Challenge for a different message → the EdDSA equation fails while `S`
        // stays canonical (so this exercises the equation, not the range check).
        let bad_k = challenge(&r, &pubkey, b"tampered message");
        assert!(ed25519(pubkey, sig, bad_k).is_err());
    }
}
