#![no_std]

use xark::{assert_eq, Field, Private, Public};

pub fn circuit(x: Private<Field>, y: Private<Field>, z: Public<Field>) {
    assert_eq((x + y) * (x - y), z);
}
