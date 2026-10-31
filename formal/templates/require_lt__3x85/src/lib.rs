use xark::{Field, Private, circuit};

/// `xark_bignum::require_lt::<3, 85>` on fresh limbs (`x` and `m − 1`).
#[circuit]
pub fn require_lt(x: Private<[Field; 3]>, m_minus_1: Private<[Field; 3]>) {
    xark_bignum::require_lt::<3, 85>(x, m_minus_1);
}
