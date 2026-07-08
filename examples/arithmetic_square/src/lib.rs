#![no_std]

use xark::{assert_eq, Field, Private, Public};

// arithmetic_square: assert(x * x == y).
pub fn circuit(x: Private<Field>, y: Public<Field>) {
    assert_eq(x * x, y);
}
