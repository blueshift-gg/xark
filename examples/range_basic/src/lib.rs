#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

// `to_bits::<8>` range-checks `x` to 8 bits (booleanity + recomposition);
// from_bits recomposes and constrains against `out`, mirroring `x as Field == out`.
#[circuit]
pub fn range_basic(x: Private<Field>, out: Public<Field>) {
    let bits = x.to_bits::<8>();
    require_eq(Field::from_bits::<8>(bits), out);
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
