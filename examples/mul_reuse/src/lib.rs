#![cfg_attr(xark, no_std)]

//! A multiplication result reused across two `require_eq`s must stay bound to
//! `a*b` in BOTH assertions. If the first `require_eq` were to fold the product's
//! defining row and detach `t`, the second `require_eq` would pin a *free*
//! witness — letting a prover satisfy the circuit with `c != d`. The compiled
//! circuit must enforce `a*b == c` AND `a*b == d` (hence `c == d`).

use xark::{circuit, require_eq, Field, Private, Public};

#[circuit]
pub fn mul_reuse(a: Private<Field>, b: Private<Field>, c: Public<Field>, d: Public<Field>) {
    let t = a * b;
    require_eq(t, c);
    require_eq(t, d);
}

#[cfg(test)]
mod tests {
    use super::mul_reuse;

    #[test]
    fn accepts_valid() {
        // t = 3·4 = 12, bound to both c and d
        mul_reuse("3".into(), "4".into(), "12".into(), "12".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(mul_reuse("3".into(), "4".into(), "12".into(), "13".into()).is_err());
    }
}
