//! Ed25519 signature verification as a `#[circuit]`: a succinct proof that a
//! signature satisfies the EdDSA equation `[S]·B == R + [k]·A` (sound lazy
//! extended-coordinate path, ~2.36M constraints vs the affine gadget's 4.55M).
//!
//! The transparent types take the exact bytes `ed25519-dalek` emits: `PointL` is
//! the **compressed** 32-byte point `A`/`R` (decompressed to `x`/`y` 3×85-bit
//! limbs on the host), `Fq` a 32-byte scalar. The challenge `k = SHA-512(R‖A‖M)
//! mod L` is a prover-supplied witness derived from the signature by
//! `xark_ed25519::challenge`, so a test/prover still provides only the signature.
#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Public};
use xark_bignum::scalar_to_bits;
use xark_ed25519::{eddsa_verify, Fq, PointL};

#[circuit]
pub fn ed25519(a: Public<PointL>, r: Public<PointL>, s: Public<Fq>, k: Public<Fq>) {
    eddsa_verify(
        a.x.limbs,
        a.y.limbs,
        r.x.limbs,
        r.y.limbs,
        scalar_to_bits(s.limbs),
        scalar_to_bits(k.limbs),
    );
}

#[cfg(test)]
mod tests {
    use super::ed25519;
    use ed25519_dalek::{Signer, SigningKey};
    use xark_ed25519::{challenge, scalar_le_to_be};

    const MSG: &[u8] = b"xark ed25519 eddsa vector";

    /// `(A, R, S, msg)` from a real signature: `A` = compressed pubkey, `R` =
    /// compressed commitment, `S` = signature scalar (converted to big-endian).
    fn parts() -> ([u8; 32], [u8; 32], [u8; 32]) {
        let sk = SigningKey::from_bytes(&[0x42u8; 32]);
        let a = sk.verifying_key().to_bytes();
        let sig = sk.sign(MSG).to_bytes();
        let r: [u8; 32] = sig[..32].try_into().unwrap();
        let s = scalar_le_to_be(&sig[32..].try_into().unwrap());
        (a, r, s)
    }

    #[test]
    fn accepts_valid() {
        let (a, r, s) = parts();
        let k = challenge(&r, &a, MSG);
        ed25519(a, r, s, k).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let (a, r, s) = parts();
        // Challenge for a different message → the EdDSA equation fails while `S`
        // stays canonical (so this exercises the equation, not the range check).
        let bad_k = challenge(&r, &a, b"tampered message");
        assert!(ed25519(a, r, s, bad_k).is_err());
    }
}
