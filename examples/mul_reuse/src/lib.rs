#![no_std]

//! Regression for audit finding #02 (assert_eq/mul merge under-constraint).
//!
//! A multiplication result reused across two `assert_eq`s must stay bound to
//! `a*b` in BOTH assertions. Before the fix, the first `assert_eq` folded the
//! product's defining row and detached `t`, so the second `assert_eq` pinned a
//! *free* witness — letting a malicious prover satisfy the circuit with
//! `c != d`. The compiled circuit must enforce `a*b == c` AND `a*b == d` (hence
//! `c == d`).

use xark::{assert_eq, Field, Private, Public};

pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>, d: Public<Field>) {
    let t = a * b;
    assert_eq(t, c);
    assert_eq(t, d);
}
