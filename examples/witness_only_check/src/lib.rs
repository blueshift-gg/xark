//! Exercises `witness_only` regions. `x⁴` is derived inside
//! `witness_begin()`/`witness_end()` — the two muls emit witness-gen but no
//! constraints, and the intermediate `x²` is unreferenced scratch (testing the
//! `check_pinning` exemption). `d` is then pinned to a constrained `x·x·x·x`, a
//! mergeable `require_eq` that must not fold into the witness-only `d`. So the
//! witness-only muls cost zero constraints yet a wrong `claim` is rejected.
#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, witness_begin, witness_end, Field, Public};

#[circuit]
pub fn witness_only_check(x: Public<Field>, claim: Public<Field>) {
    witness_begin();
    let x2 = x * x; // scratch: unreferenced by any constraint (exemption path)
    let d = x2 * x2;
    witness_end();
    require_eq(d, x * x * x * x); // mergeable pin — must not fold the last mul into `d`
    require_eq(d, claim);
}

#[cfg(test)]
mod tests {
    use super::witness_only_check;

    #[test]
    fn accepts_valid() {
        witness_only_check("2".into(), "16".into()).unwrap(); // 2⁴ = 16
    }

    #[test]
    fn rejects_wrong() {
        assert!(witness_only_check("2".into(), "17".into()).is_err());
    }
}
