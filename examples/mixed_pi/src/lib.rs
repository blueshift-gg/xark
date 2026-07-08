#![no_std]

use xark::{assert_eq, Field, Private, Public};

// mixed_pi: main(x: priv, y: pub) -> pub Field { x*y + x }.
// The return value is public, so `ret` is a public input equal to x*y + x.
pub fn circuit(x: Private<Field>, y: Public<Field>, ret: Public<Field>) {
    assert_eq(x * y + x, ret);
}
