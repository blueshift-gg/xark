#![cfg_attr(xark, no_std)]

//! A scalar-field element `s` must be *canonical* (`< n`, not merely
//! limb-bounded `< 2^258`) and nonzero, i.e. `s ∈ [1, n-1]` — this is what makes
//! ECDSA signatures non-malleable. Solving proves knowledge of such an `s`; a
//! non-canonical or zero `s` makes the circuit unsatisfiable.

use xark::{circuit, Field, Private};
use xark_secp256k1::affine::Fq;

#[circuit]
pub fn scalar_range(s0: Private<Field>, s1: Private<Field>, s2: Private<Field>) {
    let s = Fq::new([s0, s1, s2]);
    s.assert_canonical(); // 0 <= s < n
    s.assert_nonzero(); // s != 0
}

#[cfg(test)]
mod tests {
    use super::scalar_range;

    #[test]
    fn accepts_valid() {
        // scalar 1 (limbs [1,0,0]): canonical and nonzero
        scalar_range("1".into(), "0".into(), "0".into()).unwrap();
    }

    #[test]
    fn rejects_zero() {
        // scalar 0 fails `assert_nonzero`
        assert!(scalar_range("0".into(), "0".into(), "0".into()).is_err());
    }
}
