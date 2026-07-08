//! Struct support: an elliptic-curve-style `Point` with 3-limb coordinates,
//! passed **directly as an aggregate circuit input** (it flattens to 6 `Field`
//! inputs — `p.x[0..2]`, `p.y[0..2]`). Field access `p.x[i]` and passing a
//! `Point` through a helper both work, and it lowers to the exact same R1CS as
//! the bare `[[Field; 3]; 2]` array form (zero-cost).
#![no_std]

use xark::{assert_eq, Field, Private, Public};

struct Point {
    x: [Field; 3],
    y: [Field; 3],
}

/// Return the first limb of `x + y` (linear) and of `x * y` (one mul gate).
fn combine(p: Point) -> (Field, Field) {
    (p.x[0] + p.y[0], p.x[0] * p.y[0])
}

pub fn circuit(p: Private<Point>, sum: Public<Field>, prod: Public<Field>) {
    let (s, m) = combine(p);
    assert_eq(s, sum);
    assert_eq(m, prod);
}
