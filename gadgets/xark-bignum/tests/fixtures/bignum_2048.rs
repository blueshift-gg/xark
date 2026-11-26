//! `mod_mul` at 17×121-bit limbs: the width the zkGolf RSA-2048 reference uses
//! (17 × 121 = 2057 bits, enough for a 2048-bit modulus with a 112-bit top limb).
//!
//! A test fixture, not an example: it exists to exercise the width in
//! `tests/wide.rs` without adding a circuit to the stable-digest set.

use xark::{Field, Private, Public, circuit, require_eq};
use xark_bignum::{mod_mul, range_check_limbs};

#[circuit]
pub fn bignum_2048(
    a: Private<[Field; 17]>,
    b: Private<[Field; 17]>,
    m: Public<[Field; 17]>,
    c: Public<[Field; 17]>,
) {
    range_check_limbs::<17, 121>(a);
    range_check_limbs::<17, 121>(b);
    range_check_limbs::<17, 121>(m);
    let prod = mod_mul::<17, 121>(a, b, m);
    let mut i = 0usize;
    while i < 17usize {
        require_eq(prod[i], c[i]);
        i += 1;
    }
}
