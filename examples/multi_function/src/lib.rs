#![no_std]

use xark::{assert_eq, Field, Private, Public};

// multi_function: assert(square(x) == y) with a separate helper
// function (xark inlines cross-function MIR).
#[inline(never)]
fn square(x: Field) -> Field {
    x * x
}

pub fn circuit(x: Private<Field>, y: Public<Field>) {
    assert_eq(square(x), y);
}
