//! Bignum unsigned less-than: prove `is_lt(a, b) == claim` for two 2-limb
//! 64-bit values. Demonstrates the `[Field; N]` circuit-input form — each limb
//! is a field value passed natively as a decimal string.
use xark_bignum::prelude::*;

#[circuit]
pub fn is_lt_check(a: Public<[Field; 2]>, b: Public<[Field; 2]>, claim: Public<Field>) {
    require_eq(is_lt::<2, 64>(a, b), claim);
}

#[cfg(test)]
mod tests {
    use super::is_lt_check;

    // Values are little-endian 64-bit limbs: `[lo, hi]`.
    #[test]
    fn less_than() {
        // 5 < 7 → 1
        is_lt_check(
            [5, 0],
            [7, 0],
            1,
        )
        .unwrap();
    }

    #[test]
    fn not_less_than() {
        // 7 < 5 is false → 0
        is_lt_check(
            [7, 0],
            [5, 0],
            0,
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong_claim() {
        assert!(is_lt_check(
            [5, 0],
            [7, 0],
            0
        )
        .is_err());
    }
}
