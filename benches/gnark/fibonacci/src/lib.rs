//! The benchmark's Fibonacci: from private `a0`, `a1`, a thousand steps of
//! `a[n+1] = a[n] + a[n-1]` (in the field) reach the public `result`. The
//! recurrence is linear, so it costs no multiplication gate: the steps fold into
//! one linear combination and the circuit is the closing equality.
use xark::{circuit, require_eq, Field, Private, Public};

/// The number of steps; `pure/main.go` takes the same.
const STEPS: usize = 1000;

#[circuit]
pub fn fibonacci(a0: Private<Field>, a1: Private<Field>, result: Public<Field>) {
    let (mut a, mut b) = (a0, a1);
    for _ in 0..STEPS {
        (a, b) = (b, a + b);
    }
    require_eq(b, result);
}

#[cfg(test)]
mod tests {
    use super::fibonacci;

    /// `inputs.json`: F(1002) mod the BN254 scalar field.
    const RESULT: &str =
        "5941060202189947978439506637397717374054592606469262979160774138296130293158";

    #[test]
    fn accepts_valid() {
        fibonacci(1, 1, RESULT).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(fibonacci(1, 2, RESULT).is_err());
    }
}
