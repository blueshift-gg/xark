#![no_std]
use xark::{assert_eq, Field, Private, Public};

// Called EXACTLY ONCE — the prune/inline post-pass must inline it (0 defs in the
// artifact) rather than store it as a reusable def.
#[no_mangle]
pub fn once(a: Field, b: Field) -> Field {
    let c = a * b;
    c * c
}

pub fn circuit(a: Private<Field>, b: Private<Field>, out: Public<Field>) {
    assert_eq(once(a, b), out);
}
