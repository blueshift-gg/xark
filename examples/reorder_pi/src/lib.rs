#![no_std]

use xark::{assert_eq, Field, Private, Public};

// reorder_pi: main(a: pub, b: priv, c: pub) { assert(b*b == a+c) }.
pub fn circuit(a: Public<Field>, b: Private<Field>, c: Public<Field>) {
    assert_eq(b * b, a + c);
}
