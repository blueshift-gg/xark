#![no_std]

use xark::{assert_eq, Field, Private, Public};

// memory_const: arr = [x, x*2, x*3]; assert(arr sum == y),
// i.e. x + 2x + 3x == y  (== 6x).
pub fn circuit(x: Private<Field>, y: Public<Field>) {
    assert_eq(x + x * Field::constant("2") + x * Field::constant("3"), y);
}
