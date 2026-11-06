//! Numeric constants for `u8`..`u128` via both `Field::from(x)` and `x.into()`
//! (the public surface; the backing intrinsics are private). Values above `u128`
//! use `Field::constant("...")` with a decimal string.
use xark::{circuit, require_eq, Field, Private, Public};
#[circuit]
pub fn from_const(a: Private<Field>, doubled: Public<Field>, plus_big: Public<Field>) {
    let two: Field = 2u8.into(); // `.into()` form
    require_eq(a * two, doubled);
    // full-width u128 constant via `Field::from`
    require_eq(
        a + Field::from(123456789012345678901234567890u128),
        plus_big,
    );
}

#[cfg(test)]
mod tests {
    use super::from_const;

    #[test]
    fn accepts_valid() {
        // 2·5 = 10
        from_const(
            5,
            10,
            "123456789012345678901234567895",
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(from_const(
            5,
            11,
            "123456789012345678901234567895"
        )
        .is_err());
    }
}
