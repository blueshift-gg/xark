//! The width-generic `Bignum<LIMBS, BITS>` wrapper: a zero-cost newtype over
//! `[Field; LIMBS]` forwarding to the non-native modular-arithmetic free functions.
//! Here a 256-bit prime field as `Bignum<3, 86>` (the secp256k1 shape). Each
//! `Private<Fp>`/`Public<Fp>` is a typed circuit input — a single whole number on
//! the host, split into its 3 limbs automatically; the caller never thinks in limbs.
#![cfg_attr(xark, no_std)]

use xark_bignum::prelude::*;

type Fp = Bignum<3, 86>;

#[circuit]
pub fn bignum(
    a: Private<Fp>,
    b: Private<Fp>,
    m: Public<Fp>,  // modulus
    m1: Public<Fp>, // modulus − 1
    o: Public<Fp>,  // expected (a · b) mod m
) {
    let r = a.mul(b, m, m1); // (a · b) mod m, wrapper-style
    require_eq(r.limbs[0], o.limbs[0]);
    require_eq(r.limbs[1], o.limbs[1]);
    require_eq(r.limbs[2], o.limbs[2]);
}

#[cfg(test)]
mod tests {
    use super::bignum;

    // secp256k1 base field p = 2^256 − 2^32 − 977, and p − 1. Small operands (2, 3)
    // give (2·3) mod p = 6. Values are passed as whole numbers — no limb-splitting.
    const P: &str = "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
    const P_M1: &str = "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e";

    #[test]
    fn accepts_valid() {
        bignum("2".into(), "3".into(), P.into(), P_M1.into(), "6".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(bignum("2".into(), "3".into(), P.into(), P_M1.into(), "7".into()).is_err());
    }
}
