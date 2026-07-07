//! Field arithmetic with native-integer constant operands (`a * 3 + 5`).
#![no_std]
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(a: Private<Field>, out: Public<Field>) {
    // out == a*3 + 5  (Mul<u64> then Add<u64>)
    assert_eq(a * 3u64 + 5u64, out);
}
