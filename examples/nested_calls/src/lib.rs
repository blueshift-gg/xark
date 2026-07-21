#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

// require(square_plus_one(x) == y); square_plus_one calls square (two-level nesting).
#[inline(never)]
fn square(x: Field) -> Field {
    x * x
}

#[inline(never)]
fn square_plus_one(x: Field) -> Field {
    square(x) + Field::constant("1")
}

#[circuit]
pub fn nested_calls(x: Private<Field>, y: Public<Field>) {
    require_eq(square_plus_one(x), y);
}

#[cfg(test)]
mod tests {
    use super::nested_calls;

    #[test]
    fn accepts_valid() {
        nested_calls("6".into(), "37".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(nested_calls("6".into(), "38".into()).is_err());
    }
}
