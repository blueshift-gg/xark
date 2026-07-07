#![no_std]

use xark::{assert_eq, Field, Private, Public};

/// Purely linear relation: `3*x + 2*y == z`.
///
/// Constant-by-variable products fold into linear-combination coefficients, so
/// this emits a single equality constraint and *no* multiplication gates.
pub fn circuit(x: Private<Field>, y: Private<Field>, z: Public<Field>) {
    let three = Field::constant("3");
    let two = Field::constant("2");
    assert_eq(three * x + two * y, z);
}
