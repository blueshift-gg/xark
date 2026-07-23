
use xark::prelude::*;

#[circuit]
pub fn arithmetic_public_inputs(x: Private<Field>, y: Private<Field>, out: Public<Field>) {
    require_eq(x * y + x + y, out);
}

#[cfg(test)]
mod tests {
    use super::arithmetic_public_inputs;

    #[test]
    fn accepts_valid() {
        // 3·4 + 3 + 4 = 19
        arithmetic_public_inputs("3".into(), "4".into(), "19".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(arithmetic_public_inputs("3".into(), "4".into(), "20".into()).is_err());
    }
}
