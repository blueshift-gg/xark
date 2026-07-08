#![no_std]

use xark::{assert_eq, Field, Private, Public};

/// Iterate a fixed-size array by value (`for x in arr`). Lowers byte-for-byte
/// identically to the equivalent `while i < N { let x = arr[i]; .. }`.
pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>) {
    let arr = [a, b, a];
    let mut acc = Field::constant("0");
    for x in arr {
        acc = acc + x;
    }
    assert_eq(acc, c);
}
