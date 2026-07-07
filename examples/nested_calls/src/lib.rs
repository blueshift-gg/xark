#![no_std]

use xark::{assert_eq, Field, Private, Public};

// nested_calls: main asserts square_plus_one(x) == y, where
// square_plus_one calls square (two-level nested calls).
#[inline(never)]
fn square(x: Field) -> Field {
    x * x
}

#[inline(never)]
fn square_plus_one(x: Field) -> Field {
    square(x) + Field::constant("1")
}

pub fn circuit(x: Private<Field>, y: Public<Field>) {
    assert_eq(square_plus_one(x), y);
}
