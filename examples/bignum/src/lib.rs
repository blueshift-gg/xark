//! The width-generic `Bignum<LIMBS, BITS>` wrapper: a zero-cost newtype over
//! `[Field; LIMBS]` whose methods forward to the non-native modular-arithmetic
//! free functions. Callers alias a concrete width — here a 256-bit prime field
//! as `Bignum<3, 86>` (3 limbs × 86 bits, the secp256k1 shape).
//!
//! The field elements are passed **directly as aggregate circuit inputs**: each
//! `Private<Fp>`/`Public<Fp>` flattens to 3 `Field` inputs (`a.limbs[0..2]`, …).
#![no_std]
use xark_bignum::Bignum;
use xark::{assert_eq, Private, Public};

type Fp = Bignum<3, 86>;

pub fn circuit(
    a: Private<Fp>,
    b: Private<Fp>,
    m: Public<Fp>,  // modulus
    m1: Public<Fp>, // modulus − 1
    o: Public<Fp>,  // expected (a · b) mod m
) {
    // (a · b) mod m, wrapper-style.
    let r = a.mul(b, m, m1);
    assert_eq(r.limbs[0], o.limbs[0]);
    assert_eq(r.limbs[1], o.limbs[1]);
    assert_eq(r.limbs[2], o.limbs[2]);
}
