#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};
use xark_bits::{and32, xor32};

// bitwise_basic: a,b: u32; require(a & b == and_out); require(a ^ b == xor_out).
// Each u32 is carried as a Field, decomposed to 32 bits (which range-checks it),
// combined bitwise, and recomposed to compare against the public outputs.
#[circuit]
pub fn bitwise_basic(
    a: Private<Field>,
    b: Private<Field>,
    and_out: Public<Field>,
    xor_out: Public<Field>,
) {
    let ab = a.to_bits::<32>();
    let bb = b.to_bits::<32>();
    require_eq(Field::from_bits::<32>(and32(ab, bb)), and_out);
    require_eq(Field::from_bits::<32>(xor32(ab, bb)), xor_out);
}

#[cfg(test)]
mod tests {
    use super::bitwise_basic;

    #[test]
    fn accepts_valid() {
        // 12&10=8, 12^10=6
        bitwise_basic("12".into(), "10".into(), "8".into(), "6".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(bitwise_basic("12".into(), "10".into(), "8".into(), "7".into()).is_err());
    }
}
