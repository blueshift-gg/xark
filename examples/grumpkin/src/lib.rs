//! Grumpkin `MultiScalarMul` example circuit.
//!
//! Computes `R = s[0]·P[0] + s[1]·P[1]` for two private 128-bit scalars and two
//! private witness points, then constrains the computed point to equal the
//! claimed public output `R`.
//!
//! Inputs are passed **directly as aggregates**: the scalars flatten to
//! `scalars[0..1]`, the points to `points[0][0..1]`/`points[1][0..1]`, and the
//! claimed output to `r[0..1]`.
#![no_std]

use xark_grumpkin::multi_scalar_mul;
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(
    scalars: Private<[Field; 2]>,
    points: Private<[[Field; 2]; 2]>,
    r: Public<[Field; 2]>,
) {
    let out = multi_scalar_mul(scalars, points);
    assert_eq(out[0], r[0]);
    assert_eq(out[1], r[1]);
}
