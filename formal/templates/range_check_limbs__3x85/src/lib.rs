use xark::{Field, Private, circuit};

/// `xark_bignum::range_check_limbs::<3, 85>` on fresh limbs.
#[circuit]
pub fn range_check_limbs(x: Private<[Field; 3]>) {
    xark_bignum::range_check_limbs::<3, 85>(x);
}
