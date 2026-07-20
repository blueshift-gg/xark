#![cfg_attr(xark, no_std)]

use xark::{assert_eq, circuit, Field, Private, Public};

// range_basic: x: u8; assert(x as Field == out).
// `to_bits8` range-checks `x` to 8 bits (booleanity + recomposition); recomposing
// and constraining against `out` mirrors the `x as Field == out` assertion.
#[circuit]
pub fn range_basic(x: Private<Field>, out: Public<Field>) {
    let bits = x.to_bits::<8>();
    assert_eq(Field::from_bits::<8>(bits), out);
}

#[cfg(test)]
mod tests {
    use super::range_basic;

    #[test]
    fn accepts_valid() {
        // 8-bit value round-trips through to_bits/from_bits
        range_basic("200".into(), "200".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(range_basic("200".into(), "201".into()).is_err());
    }
}
