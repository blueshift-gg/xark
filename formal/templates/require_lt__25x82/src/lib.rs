use xark::{Field, Private, circuit};

/// The `require_lt__25x82` harness on fresh inputs.
#[circuit]
pub fn require_lt(x: Private<[Field; 25]>, m_minus_1: Private<[Field; 25]>) {
    xark_bignum::require_lt::<25, 82>(x, m_minus_1);
}
