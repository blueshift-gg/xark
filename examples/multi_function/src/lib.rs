#![cfg_attr(xark, no_std)]

use xark::{assert_eq, circuit, Field, Private, Public};

// multi_function: assert(square(x) == y) with a separate helper
// function (xark inlines cross-function MIR).
#[inline(never)]
fn square(x: Field) -> Field {
    x * x
}

#[circuit]
pub fn multi_function(x: Private<Field>, y: Public<Field>) {
    assert_eq(square(x), y);
}

#[cfg(test)]
mod tests {
    use super::multi_function;

    #[test]
    fn accepts_valid() {
        // square(6) = 36
        multi_function("6".into(), "36".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(multi_function("6".into(), "37".into()).is_err());
    }
}
