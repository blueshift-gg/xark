//! Numeric constants for `u8`..`u128` via both `Field::from(x)` and `x.into()`
//! (the public surface; the backing intrinsics are private). Values above `u128`
//! use `Field::constant("...")` with a decimal string.
#![no_std]
use xark::{assert_eq, Field, Private, Public};
pub fn circuit(a: Private<Field>, doubled: Public<Field>, plus_big: Public<Field>) {
    let two: Field = 2u8.into(); // `.into()` form (monomorphized blanket impl)
    assert_eq(a * two, doubled); // 2*a == doubled
    // full-width u128 constant via `Field::from`, kept standalone
    assert_eq(a + Field::from(123456789012345678901234567890u128), plus_big);
}
