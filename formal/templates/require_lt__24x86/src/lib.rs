use xark::{Field, Private, circuit};

/// `xark_bignum::require_lt::<24, 86>` on fresh limbs (`x` and `m − 1`).
#[circuit]
pub fn require_lt(x: Private<[Field; 24]>, m_minus_1: Private<[Field; 24]>) {
    xark_bignum::require_lt::<24, 86>(x, m_minus_1);
}
