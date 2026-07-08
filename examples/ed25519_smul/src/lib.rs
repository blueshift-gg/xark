//! Ed25519 scalar-multiplication example: given a scalar `k` (three 86-bit
//! limbs), a base point `P` and a claimed result `R`, constrain `[k]·P == R`
//! using the twisted-Edwards gadget.
//!
//! Inputs are passed **directly as aggregates**: the scalar flattens to
//! `k[0..2]`, and each `Point` to `<name>.x.limbs[0..2]`/`<name>.y.limbs[0..2]`.
#![no_std]

use xark_ed25519::{scalar_mul, Point};
use xark_ff::scalar_to_bits;
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(k: Private<[Field; 3]>, p: Public<Point>, r: Public<Point>) {
    let bits = scalar_to_bits(k);
    let out = scalar_mul(bits, p);
    let mut i = 0;
    while i < 3 {
        assert_eq(out.x.limbs[i], r.x.limbs[i]);
        i += 1;
    }
    let mut i = 0;
    while i < 3 {
        assert_eq(out.y.limbs[i], r.y.limbs[i]);
        i += 1;
    }
}
