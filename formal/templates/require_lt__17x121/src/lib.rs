use xark::{Field, Private, circuit};

/// The `require_lt__17x121` harness on fresh inputs.
#[circuit]
pub fn require_lt(x: Private<[Field; 17]>, m_minus_1: Private<[Field; 17]>) {
    xark_bignum::require_lt::<17, 121>(x, m_minus_1);
}
