//! Non-native `(a · b) mod m` over 24×86-bit limbs (2064 bits): the width an
//! RSA-2048 modulus needs, above the 16 limbs the decomposition buffers used to
//! stop at. `m` is a public input (odd, so `m − 1` only changes limb 0).
#![cfg_attr(xark, no_std)]

use xark::{Field, Private, Public, circuit, require_eq};
use xark_bignum::mod_mul;

#[circuit]
pub fn bignum_wide(
    a: Private<[Field; 24]>,
    b: Private<[Field; 24]>,
    m: Public<[Field; 24]>,
    c: Public<[Field; 24]>,
) {
    let mut m_m1 = m;
    m_m1[0] = m[0] - Field::from(1u8);
    let prod = mod_mul::<24, 86>(a, b, m, m_m1);
    let mut i = 0usize;
    while i < 24usize {
        require_eq(prod[i], c[i]);
        i += 1;
    }
}
