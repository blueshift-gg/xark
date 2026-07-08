#![no_std]

use xark::{assert_eq, Field, Private, Public};

pub fn circuit(secret: Private<Field>, result: Public<Field>) {
    assert_eq(secret ^ 3, result);
}
