#![no_std]
use xark::{assert_eq, Field, Private, Public};

// all-Field, called many times → gadget by default, UNLESS the user opts out.
#[inline(never)]
fn sq(x: Field) -> Field { x * x }

pub fn circuit(inp: Private<[Field; 8]>, out: Public<Field>) {
    let mut acc = inp[0];
    let mut i = 1;
    while i < 8 { acc = sq(acc) + inp[i]; i += 1; }
    assert_eq(acc, out);
}
