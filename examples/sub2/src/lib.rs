//! Isolated validation of the fused non-native subtract `(a − b − c) mod p` over
//! secp256k1's base field (3×86-bit limbs). Inputs are field-valued limb arrays
//! passed as decimal strings.
#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

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

    // Limbs are little-endian (limb0 = low 86 bits); small values stay in limb0.
    const fn v(x: &str) -> [&str; 3] {
        [x, "0", "0"]
    }
    fn a3(x: [&str; 3]) -> [String; 3] {
        [x[0].into(), x[1].into(), x[2].into()]
    }

    #[test]
    fn accepts_valid() {
        // (10 - 3 - 2) mod p = 5
        sub2(a3(v("10")), a3(v("3")), a3(v("2")), a3(v("5"))).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(sub2(a3(v("10")), a3(v("3")), a3(v("2")), a3(v("6"))).is_err());
    }
}
