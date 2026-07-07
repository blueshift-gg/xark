//! Grumpkin Pedersen hash example circuit.
//!
//! Hashes two private 128-bit message scalars `m0, m1` to a public Grumpkin
//! point `(hx, hy)` via `H = m0·G0 + m1·G1`, then constrains the computed point
//! to equal the claimed public output.
#![no_std]

use xark::{assert_eq, Field, Private, Public};
use xark_pedersen::pedersen_hash;

pub fn circuit(m0: Private<Field>, m1: Private<Field>, hx: Public<Field>, hy: Public<Field>) {
    let h = pedersen_hash([m0, m1]);
    assert_eq(h[0], hx);
    assert_eq(h[1], hy);
}
