#![no_std]
use xark::{assert_eq, Field, Private, Public};

// Multi-output gadget: two Field inputs, a [Field; 2] output.
#[no_mangle]
pub fn g(a: Field, b: Field) -> [Field; 2] {
    let c = a * b;
    let d = c * c;
    [d, c]
}

pub fn circuit(inp: Private<[Field; 64]>, out: Public<Field>) {
    let mut acc = inp[0];
    let mut i = 1;
    while i < 64 {
        let r = g(acc, inp[i]);
        acc = r[0] * r[1]; // use both outputs
        i += 1;
    }
    assert_eq(acc, out);
}
