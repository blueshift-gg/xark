//! Non-native `(a · b) mod m` over 24×86-bit limbs (2064 bits): the width an
//! RSA-2048 modulus needs, above the 16 limbs the decomposition buffers used to
//! stop at. `m` is a public input. The limbs are parameters, so the circuit
//! range-checks them (`mod_mul`'s relation holds only for limbs `< 2^86`).
#![cfg_attr(xark, no_std)]

use xark::{Field, Private, Public, circuit, require_eq};
use xark_bignum::{mod_mul, range_check_limbs};

#[circuit]
pub fn bignum_wide(
    a: Private<[Field; 24]>,
    b: Private<[Field; 24]>,
    m: Public<[Field; 24]>,
    c: Public<[Field; 24]>,
) {
    // Three limbs at a time: the width `range_check_limbs` is proven at.
    let mut i = 0usize;
    while i < 24usize {
        range_check_limbs::<3, 86>([a[i], a[i + 1], a[i + 2]]);
        range_check_limbs::<3, 86>([b[i], b[i + 1], b[i + 2]]);
        range_check_limbs::<3, 86>([m[i], m[i + 1], m[i + 2]]);
        i += 3;
    }
    let prod = mod_mul::<24, 86>(a, b, m);
    let mut i = 0usize;
    while i < 24usize {
        require_eq(prod[i], c[i]);
        i += 1;
    }
}
