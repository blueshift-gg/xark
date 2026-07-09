//! Prototype: secp256k1 base-field multiply with 3 limbs of 86 bits, to measure
//! the constraint count vs the 4×64 representation. Pure `mod_mul::<3, 86>` (no input
//! range checks — the boundary check is ~identical (256 bits) for both widths).
#![no_std]
use xark_bignum::mod_mul;
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(
    a: Private<[Field; 3]>,
    b: Private<[Field; 3]>,
    c: Public<[Field; 3]>,
) {
    let p = [
        Field::constant("77371252455336262886226991"),
        Field::constant("77371252455336267181195263"),
        Field::constant("19342813113834066795298815"),
    ];
    let p_m1 = [
        Field::constant("77371252455336262886226990"),
        Field::constant("77371252455336267181195263"),
        Field::constant("19342813113834066795298815"),
    ];
    let prod = mod_mul::<3, 86>(a, b, p, p_m1);
    assert_eq(prod[0], c[0]);
    assert_eq(prod[1], c[1]);
    assert_eq(prod[2], c[2]);
}
