#![no_std]

use xark::{assert_eq, Field, Private, Public};

/// `a^3` via a compile-time-unrolled `for` loop. Lowers byte-for-byte identically
/// to the equivalent `let mut i = 0; while i < 2 { acc = acc * a; i += 1; }`.
pub fn circuit(a: Private<Field>, c: Public<Field>) {
    let mut acc = a;
    for _i in 0..2u64 {
        acc = acc * a;
    }
    assert_eq(acc, c);
}
