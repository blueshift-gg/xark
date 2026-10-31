use xark::{Field, Private, circuit};

/// `xark_bignum::range_check_limbs::<4, 64>` on fresh limbs.
#[circuit]
pub fn range_check_limbs(x: Private<[Field; 4]>) {
    xark_bignum::range_check_limbs::<4, 64>(x);
}
