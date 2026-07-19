//! Ed25519 scalar multiplication as a `#[circuit]`: constrain `[k]·P == R` on the
//! twisted-Edwards gadget. `Point` is the transparent compact uncompressed
//! `[u8; 64]` (`x ‖ y`) type and `Fq` the `[u8; 32]` scalar, so the test passes
//! the basepoint `P = B`, a scalar `k`, and `R = [k]·B` as raw bytes.
#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{assert_eq, circuit, Public};
use xark_bignum::scalar_to_bits;
use xark_ed25519::{scalar_mul, Fq, Point};

#[circuit]
pub fn ed25519_smul(k: Public<Fq>, p: Public<Point>, r: Public<Point>) {
    let out = scalar_mul(scalar_to_bits(k.limbs), p);
    let mut i = 0;
    while i < 3 {
        assert_eq(out.x.limbs[i], r.x.limbs[i]);
        i += 1;
    }
    let mut i = 0;
    while i < 3 {
        assert_eq(out.y.limbs[i], r.y.limbs[i]);
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::ed25519_smul;
    use xark_ed25519::{base_be, base_mul_be};

    fn k() -> [u8; 32] {
        let mut b = [0u8; 32];
        b[31] = 7; // k = 7 (big-endian scalar)
        b
    }

    #[test]
    fn accepts_valid() {
        let k = k();
        ed25519_smul(k, base_be(), base_mul_be(&k)).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let k = k();
        let mut r = base_mul_be(&k);
        r[63] ^= 1; // wrong R
        assert!(ed25519_smul(k, base_be(), r).is_err());
    }
}
