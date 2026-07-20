#![cfg_attr(xark, no_std)]

use xark::{assert_eq, circuit, Field, Private, Public};

// nested_calls: main asserts square_plus_one(x) == y, where
// square_plus_one calls square (two-level nested calls).
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
    assert_eq(square_plus_one(x), y);
}

#[cfg(test)]
mod tests {
    use super::nested_calls;

    #[test]
    fn accepts_valid() {
        // 6² + 1 = 37
        nested_calls("6".into(), "37".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(nested_calls("6".into(), "38".into()).is_err());
    }
}
