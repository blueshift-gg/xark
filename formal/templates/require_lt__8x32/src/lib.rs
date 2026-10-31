use xark::{Field, Private, circuit};

/// `xark_bignum::require_lt::<8, 32>` on fresh limbs (`x` and `m − 1`).
#[circuit]
pub fn require_lt(x: Private<[Field; 8]>, m_minus_1: Private<[Field; 8]>) {
    xark_bignum::require_lt::<8, 32>(x, m_minus_1);
}
