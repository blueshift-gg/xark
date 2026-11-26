use xark::{Field, Private, circuit};

/// The `range_check_limbs__17x121` harness on fresh inputs.
#[circuit]
pub fn range_check_limbs(x: Private<[Field; 17]>) {
    xark_bignum::range_check_limbs::<17, 121>(x);
}
