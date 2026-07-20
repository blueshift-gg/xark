//! Variable-length hashing with the Poseidon **sponge** (`hash::<N>`). `N` is a
//! compile-time constant; here we hash 5 private inputs and expose the digest.
#![no_std]
use xark_poseidon::prelude::*;

pub fn circuit(
    a: Private<Field>, b: Private<Field>, c: Private<Field>,
    d: Private<Field>, e: Private<Field>, out: Public<Field>,
) {
    assert_eq(hash::<5>([a, b, c, d, e]), out);
}
