//! A tiny circuit whose R1CS the Nova prover extracts, commits, and folds.
#![cfg_attr(xark, no_std)]

use xark::prelude::*;

#[circuit]
pub fn tiny(a: Public<Field>, b: Public<Field>, c: Public<Field>, d: Public<Field>) {
    require_eq(a * b, c);
    require_eq(c + a, d);
}
