//! Numeric constants for `u8`..`u128` via both `Field::from(x)` and `x.into()`
//! (the public surface; the backing intrinsics are private). Values above `u128`
//! use `Field::constant("...")` with a decimal string.
#![cfg_attr(xark, no_std)]
use xark::{assert_eq, circuit, Field, Private, Public};
#[circuit]
pub fn from_const(a: Private<Field>, doubled: Public<Field>, plus_big: Public<Field>) {
    let two: Field = 2u8.into(); // `.into()` form (monomorphized blanket impl)
    assert_eq(a * two, doubled); // 2*a == doubled
    // full-width u128 constant via `Field::from`, kept standalone
    assert_eq(a + Field::from(123456789012345678901234567890u128), plus_big);
}

#[cfg(test)]
mod tests {
    use super::from_const;

    #[test]
    fn accepts_valid() {
        // 2·5 = 10; 5 + 123456789012345678901234567890
        from_const("5".into(), "10".into(), "123456789012345678901234567895".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(from_const("5".into(), "11".into(), "123456789012345678901234567895".into()).is_err());
    }
}
