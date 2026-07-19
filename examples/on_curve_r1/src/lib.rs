//! Assert a secp256r1 (P-256) point `q = (x, y)` lies on the curve
//! `y² = x³ − 3x + b`, as a `#[circuit]`. This is the `enforce_on_curve` check
//! the ECDSA gadget runs on its public-key input (the `a = −3` curve). `Point`
//! is the transparent compact uncompressed `[u8; 64]` (`x ‖ y`) type, so the test
//! passes the raw coordinate bytes `p256` emits.
#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Public};
use xark_secp256r1::{enforce_on_curve, Point};

#[circuit]
pub fn on_curve_r1(q: Public<Point>) {
    enforce_on_curve(q);
}

#[cfg(test)]
mod tests {
    use super::on_curve_r1;
    use p256::ecdsa::SigningKey;

    fn point() -> [u8; 64] {
        let vk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
        let enc = vk.verifying_key().to_encoded_point(false);
        enc.as_bytes()[1..].try_into().unwrap() // x ‖ y, drop 0x04 tag
    }

    #[test]
    fn accepts_on_curve() {
        on_curve_r1(point()).unwrap();
    }

    #[test]
    fn rejects_off_curve() {
        let mut q = point();
        q[63] ^= 1; // perturb y → off the curve
        assert!(on_curve_r1(q).is_err());
    }
}
