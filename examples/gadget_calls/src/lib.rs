#![no_std]

use xark::{assert_eq, Field, Private, Public};

// Gadget with materialized single-var I/O (every value is a multiplication
// output — no free-addition threading), the realistic gadget shape (ed25519's
// field ops materialize their results too). Auto-identified as a cached function
// from its all-Field signature.
pub fn g(x: Field, y: Field) -> Field {
    let a = x * y;
    a * a
}

pub fn circuit(inp: Private<[Field; 512]>, out: Public<Field>) {
    let mut acc = inp[0];
    let mut i = 1;
    while i < 512 {
        acc = g(acc, inp[i]);
        i += 1;
    }
    assert_eq(acc, out);
}
