//! Non-native base-field multiply `(a · b) mod p` over secp256k1's base field
//! with 3×86-bit limbs (`mod_mul::<3, 86>`). Low-level bignum primitive demo: limbs
//! are field values passed natively as decimals, so the circuit range-checks them
//! (`mod_mul`'s relation holds only for limbs `< 2^86`).
use xark::{circuit, require_eq, Field, Private, Public};
use xark_bignum::{mod_mul, range_check_limbs};

#[circuit]
pub fn fp_mul(a: Private<[Field; 3]>, b: Private<[Field; 3]>, c: Public<[Field; 3]>) {
    let p = [
        Field::constant("77371252455336262886226991"),
        Field::constant("77371252455336267181195263"),
        Field::constant("19342813113834066795298815"),
    ];
    range_check_limbs::<3, 86>(a);
    range_check_limbs::<3, 86>(b);
    let prod = mod_mul::<3, 86>(a, b, p);
    require_eq(prod[0], c[0]);
    require_eq(prod[1], c[1]);
    require_eq(prod[2], c[2]);
}

#[cfg(test)]
mod tests {
    use super::fp_mul;

    #[test]
    fn accepts_valid() {
        // (2 · 3) mod p = 6 (both operands reduced, product < p)
        fp_mul([2, 0, 0], [3, 0, 0], [6, 0, 0]).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(fp_mul([2, 0, 0], [3, 0, 0], [7, 0, 0]).is_err());
    }
}
