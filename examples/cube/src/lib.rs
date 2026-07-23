
use xark::prelude::*;

#[circuit]
pub fn cube(secret: Private<Field>, result: Public<Field>) {
    require_eq(secret.pow(3), result);
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
