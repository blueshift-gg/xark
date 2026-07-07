#![no_std]

use xark::{assert_eq, Field, Private, Public};

// return_values_only: main(x: priv) -> pub Field { x*x }.
pub fn circuit(x: Private<Field>, ret: Public<Field>) {
    assert_eq(x * x, ret);
}
