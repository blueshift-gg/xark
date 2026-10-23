use xark::{circuit, require_eq, Field, Private, Public};

// require(square(x) == y) via a helper (xark inlines calls across functions).
#[inline(never)]
fn square(x: Field) -> Field {
    x * x
}

#[circuit]
pub fn multi_function(x: Private<Field>, y: Public<Field>) {
    require_eq(square(x), y);
}

#[cfg(test)]
mod tests {
    use super::multi_function;

    #[test]
    fn accepts_valid() {
        multi_function(6, 36).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(multi_function(6, 37).is_err());
    }
}
