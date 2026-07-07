//! Aggregate circuit inputs: an array of `Field` and a bare `Field` — the array
//! collapses to `n` inputs named by access path (`a[0]`, `a[1]`, `a[2]`).
#![no_std]
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(a: Private<[Field; 3]>, b: Public<Field>) {
    // b == a[0] + a[1] + a[2]
    assert_eq(a[0] + a[1] + a[2], b);
}
