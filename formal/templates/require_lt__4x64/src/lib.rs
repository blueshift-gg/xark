use xark::{Field, Private, circuit};

/// `xark_bignum::require_lt::<4, 64>` on fresh limbs (`x` and `m − 1`).
#[circuit]
pub fn require_lt(x: Private<[Field; 4]>, m_minus_1: Private<[Field; 4]>) {
    xark_bignum::require_lt::<4, 64>(x, m_minus_1);
}
