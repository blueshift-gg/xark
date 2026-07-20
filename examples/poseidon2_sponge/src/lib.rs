//! Variable-length hashing with the Poseidon2 **sponge** (`hash::<N>`). A circuit
//! is fixed-size, so the element count `N` is a compile-time constant and the
//! absorb loop unrolls. Here we hash 5 private inputs and expose the digest.
#![no_std]
use xark_poseidon2::prelude::*;

pub fn circuit(
    a: Private<Field>, b: Private<Field>, c: Private<Field>,
    d: Private<Field>, e: Private<Field>, out: Public<Field>,
) {
    assert_eq(hash::<5>([a, b, c, d, e]), out);
}
