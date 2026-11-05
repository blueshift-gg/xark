use xark::{Field, Private, circuit};

/// `xark_bignum::range_check_limbs::<8, 32>` on fresh limbs.
#[circuit]
pub fn range_check_limbs(x: Private<[Field; 8]>) {
    xark_bignum::range_check_limbs::<8, 32>(x);
}
