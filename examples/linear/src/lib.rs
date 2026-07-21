#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

/// Purely linear relation: `3*x + 2*y == z`.
///
/// Constant-by-variable products fold into linear-combination coefficients, so
/// this emits a single equality constraint and *no* multiplication gates.
#[circuit]
pub fn linear(x: Private<Field>, y: Private<Field>, z: Public<Field>) {
    let three = Field::constant("3");
    let two = Field::constant("2");
    require_eq(three * x + two * y, z);
}

#[cfg(test)]
mod tests {
    use super::linear;

    #[test]
    fn accepts_valid() {
        // 3·4 + 2·5 = 22
        linear("4".into(), "5".into(), "22".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(linear("4".into(), "5".into(), "23".into()).is_err());
    }
}
