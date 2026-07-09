//! Isolated validation of the fused subtract (a-b-c) mod p over secp256k1's base field.
#![no_std]
use xark_bignum::sub2;
use xark::{assert_eq, Field, Private, Public};
pub fn circuit(
    a: Private<[Field; 3]>,
    b: Private<[Field; 3]>,
    c: Private<[Field; 3]>,
    r: Public<[Field; 3]>,
) {
    let p = [Field::constant("77371252455336262886226991"), Field::constant("77371252455336267181195263"), Field::constant("19342813113834066795298815")];
    let pm1 = [Field::constant("77371252455336262886226990"), Field::constant("77371252455336267181195263"), Field::constant("19342813113834066795298815")];
    let out = sub2::<3, 86>(a, b, c, p, pm1);
    assert_eq(out[0], r[0]); assert_eq(out[1], r[1]); assert_eq(out[2], r[2]);
}
