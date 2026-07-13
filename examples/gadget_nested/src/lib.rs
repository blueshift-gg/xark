#![no_std]
use xark::{assert_eq, Field, Private, Public};

// Inner gadget, called from BOTH outer gadgets — should be walked once globally.
#[no_mangle]
pub fn sq_prod(a: Field, b: Field) -> Field {
    let c = a * b;
    c * c
}
#[no_mangle]
pub fn outer_a(x: Field, y: Field) -> Field {
    let p = sq_prod(x, y);
    sq_prod(p, x)
}
#[no_mangle]
pub fn outer_b(x: Field, y: Field) -> Field {
    let q = sq_prod(y, x);
    q * y
}

pub fn circuit(inp: Private<[Field; 64]>, out: Public<Field>) {
    let mut acc = inp[0];
    let mut i = 1;
    while i < 64 {
        acc = if i % 2 == 0 { outer_a(acc, inp[i]) } else { outer_b(acc, inp[i]) };
        i += 1;
    }
    assert_eq(acc, out);
}
