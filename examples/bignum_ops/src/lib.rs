//! Operator syntax for non-native fields. `xark_bignum::fp!` defines a field-element
//! type from just its modulus (limbs / `m − 1` / complement derived), with
//! `core::ops` (`+`, `-`, `*`, unary `-`) on it and `.inverse()`/`.sub2()`/… on it.
//! Zero-cost: the operators forward to the width-generic free functions.
//!
//! The field elements are passed **directly as aggregate circuit inputs**: each
//! `Private<El>` flattens to 3 `Field` inputs (`a.limbs[0..2]`, `b.limbs[0..2]`).
#![no_std]
use xark::{assert_eq, Field, Private, Public};

// A concrete 256-bit prime field (3 × 86-bit limbs), defined by its modulus alone.
xark_bignum::fp!(El, "41904174945551648470736051755806485464313947085173149");

pub fn circuit(a: Private<El>, b: Private<El>, out: Public<Field>) {
    // Natural operator syntax on non-native field elements.
    let r = a * b + a - b;
    assert_eq(r.limbs[0], out);
}
