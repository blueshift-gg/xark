#![no_std]

use xark::{assert_eq, Field, Private, Public};

// range_basic: x: u8; assert(x as Field == out).
// `to_bits8` range-checks `x` to 8 bits (booleanity + recomposition); recomposing
// and constraining against `out` mirrors the `x as Field == out` assertion.
pub fn circuit(x: Private<Field>, out: Public<Field>) {
    let bits = x.to_bits::<8>();
    assert_eq(Field::from_bits::<8>(bits), out);
}
