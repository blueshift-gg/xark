//! The width-generic `Bignum<LIMBS, BITS>` wrapper: a zero-cost newtype over
//! `[Field; LIMBS]` whose methods forward to the non-native modular-arithmetic
//! free functions. Callers alias a concrete width — here a 256-bit prime field
//! as `Bignum<3, 86>` (3 limbs × 86 bits, the secp256k1 shape).
//!
//! Each `Private<Fp>`/`Public<Fp>` is a first-class **typed circuit input**: on
//! the host it is a single whole number (a decimal or `0x`-hex string), split into
//! its 3 limbs (`a.limbs[0..2]`) automatically — the caller never thinks in limbs.
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
    // (a · b) mod m, wrapper-style.
    let r = a.mul(b, m, m1);
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
