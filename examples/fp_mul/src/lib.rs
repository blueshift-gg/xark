//! Non-native base-field multiply `(a · b) mod p` over secp256k1's base field
//! with 3×86-bit limbs (pure `mod_mul::<3, 86>`, no input range checks). Low-level
//! bignum primitive demo: limbs are ordinary host-side `Field` values.

use xark::prelude::*;
use xark_bignum::mod_mul;

#[circuit]
pub fn fp_mul(a: Private<[Field; 3]>, b: Private<[Field; 3]>, c: Public<[Field; 3]>) {
    let p = [
        Field::constant("77371252455336262886226991"),
        Field::constant("77371252455336267181195263"),
        Field::constant("19342813113834066795298815"),
    ];
    let p_m1 = [
        Field::constant("77371252455336262886226990"),
        Field::constant("77371252455336267181195263"),
        Field::constant("19342813113834066795298815"),
    ];
    let prod = mod_mul::<3, 86>(a, b, p, p_m1);
    require_eq(prod[0], c[0]);
    require_eq(prod[1], c[1]);
    require_eq(prod[2], c[2]);
}

#[cfg(test)]
mod tests {
    use super::fp_mul;
    use xark::Field;

    fn v(x: u64) -> [Field; 3] {
        [x.into(), 0u64.into(), 0u64.into()]
    }

    #[test]
    fn accepts_valid() {
        // (2 · 3) mod p = 6 (both operands reduced, product < p)
        fp_mul(v(2), v(3), v(6)).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(fp_mul(v(2), v(3), v(7)).is_err());
    }
}
