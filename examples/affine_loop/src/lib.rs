#![no_std]

use xark::{assert_eq, Field, Private, Public};

// One clean affine loop: `acc = acc * base` repeated. Each iteration emits a
// single multiplication constraint whose operands step by a fixed amount (the
// fresh product var), and the carried `acc` slot's var steps by one — the
// canonical affine loop for the reconstruction prototype.
pub fn circuit(base: Private<Field>, out: Public<Field>) {
    let mut acc = base;
    let mut i = 0;
    while i < 20000 {
        acc = acc * base;
        i += 1;
    }
    assert_eq(acc, out);
}
