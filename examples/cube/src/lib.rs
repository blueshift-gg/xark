#![cfg_attr(xark, no_std)]

use xark::{assert_eq, circuit, Field, Private, Public};

#[circuit]
pub fn cube(secret: Private<Field>, result: Public<Field>) {
    assert_eq(secret.pow(3), result);
}

#[cfg(test)]
mod tests {
    use super::cube;

    #[test]
    fn accepts_valid() {
        cube("3".into(), "27".into()).unwrap(); // 3³ = 27
    }

    #[test]
    fn rejects_wrong_result() {
        assert!(cube("3".into(), "28".into()).is_err());
    }
}
