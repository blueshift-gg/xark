#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

#[circuit]
pub fn arithmetic_square(x: Private<Field>, y: Public<Field>) {
    require_eq(x * x, y);
}

#[cfg(test)]
mod tests {
    use super::arithmetic_square;

    #[test]
    fn accepts_valid() {
        // 7² = 49
        arithmetic_square("7".into(), "49".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(arithmetic_square("7".into(), "50".into()).is_err());
    }
}
