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
        arithmetic_square(7, 49).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(arithmetic_square(7, 50).is_err());
    }
}
