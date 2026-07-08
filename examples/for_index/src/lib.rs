#![no_std]

use xark::{assert_eq, Field, Private, Public};

/// Sum an array by indexing it with the `for` loop counter (`arr[i]`). Lowers
/// byte-for-byte identically to the equivalent `while i < 3` version.
pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>) {
    let arr = [a, b, a];
    let mut acc = Field::constant("0");
    for i in 0..3 {
        acc = acc + arr[i];
    }
    assert_eq(acc, c);
}
