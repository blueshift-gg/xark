#![cfg_attr(xark, no_std)]

//! A scalar `s` must be canonical (`< n`, not merely limb-bounded `< 2^258`) and
//! nonzero, i.e. `s ∈ [1, n-1]` — this is what makes ECDSA signatures
//! non-malleable. A non-canonical or zero `s` makes the circuit unsatisfiable.

use xark::{circuit, Field, Private};
use xark_secp256k1::affine::Fq;

#[circuit]
pub fn scalar_range(s0: Private<Field>, s1: Private<Field>, s2: Private<Field>) {
    let s = Fq::new([s0, s1, s2]);
    s.assert_canonical();
    s.assert_nonzero();
}

#[cfg(test)]
mod tests {
    use super::scalar_range;

    #[test]
    fn accepts_valid() {
        scalar_range("1".into(), "0".into(), "0".into()).unwrap();
    }

    #[test]
    fn rejects_zero() {
        assert!(scalar_range("0".into(), "0".into(), "0".into()).is_err());
    }
}
