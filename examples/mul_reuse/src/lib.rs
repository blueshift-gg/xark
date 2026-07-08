#![no_std]

//! A multiplication result reused across two `assert_eq`s must stay bound to
//! `a*b` in BOTH assertions. If the first `assert_eq` were to fold the product's
//! defining row and detach `t`, the second `assert_eq` would pin a *free*
//! witness — letting a prover satisfy the circuit with `c != d`. The compiled
//! circuit must enforce `a*b == c` AND `a*b == d` (hence `c == d`).

use xark::{assert_eq, Field, Private, Public};

pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>, d: Public<Field>) {
    let t = a * b;
    assert_eq(t, c);
    assert_eq(t, d);
}
