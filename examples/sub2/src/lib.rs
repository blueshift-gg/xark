//! Isolated validation of the fused non-native subtract `(a − b − c) mod p` over
//! secp256k1's base field (3×86-bit limbs). Inputs are field-valued limb arrays
//! passed as ordinary host-side `Field` values.

use xark::prelude::*;

#[circuit]
pub fn sub2(
    a: Private<[Field; 3]>,
    b: Private<[Field; 3]>,
    c: Private<[Field; 3]>,
    r: Public<[Field; 3]>,
) {
    let p = [
        Field::constant("77371252455336262886226991"),
        Field::constant("77371252455336267181195263"),
        Field::constant("19342813113834066795298815"),
    ];
    let pm1 = [
        Field::constant("77371252455336262886226990"),
        Field::constant("77371252455336267181195263"),
        Field::constant("19342813113834066795298815"),
    ];
    // Qualified: the entry fn shares the gadget's name.
    let out = xark_bignum::sub2::<3, 86>(a, b, c, p, pm1);
    require_eq(out[0], r[0]);
    require_eq(out[1], r[1]);
    require_eq(out[2], r[2]);
}

#[cfg(test)]
mod tests {
    use super::sub2;
    use xark::Field;

    // Limbs are little-endian (limb0 = low 86 bits); small values stay in limb0.
    fn v(x: u64) -> [Field; 3] {
        [x.into(), 0u64.into(), 0u64.into()]
    }

    #[test]
    fn accepts_valid() {
        // (10 - 3 - 2) mod p = 5
        sub2(v(10), v(3), v(2), v(5)).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(sub2(v(10), v(3), v(2), v(6)).is_err());
    }
}
