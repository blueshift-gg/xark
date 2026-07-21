//! Exercises `witness_only` regions. `x⁴` is *derived* inside
//! `witness_begin()`/`witness_end()` — the two multiplications emit witness-gen
//! but **no constraints**, and the intermediate `x²` is unreferenced scratch
//! (testing the `check_pinning` exemption). The result `d` is pinned to a normal
//! (constrained) `x·x·x·x`, which binds it to the real input `x` — a mergeable
//! `require_eq` that must *not* fold into the witness-only `d`. So the witness-only
//! muls cost zero constraints yet a wrong `claim` is rejected.
#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, witness_begin, witness_end, Field, Public};

#[circuit]
pub fn witness_only_check(x: Public<Field>, claim: Public<Field>) {
    witness_begin();
    let x2 = x * x; // scratch: unreferenced by any constraint (exemption path)
    let d = x2 * x2; // scratch: pinned below
    witness_end();
    require_eq(d, x * x * x * x); // mergeable pin — must not fold the last mul into `d`
    require_eq(d, claim);
}

#[cfg(test)]
mod tests {
    use super::witness_only_check;

    #[test]
    fn accepts_valid() {
        // 2⁴ = 16
        witness_only_check("2".into(), "16".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(witness_only_check("2".into(), "17".into()).is_err());
    }
}
