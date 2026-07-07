#![no_std]

use xark::{assert_eq, Field, Private, Public};

// arithmetic_public_inputs: assert(x * y + x + y == out).
pub fn circuit(x: Private<Field>, y: Private<Field>, out: Public<Field>) {
    assert_eq(x * y + x + y, out);
}
