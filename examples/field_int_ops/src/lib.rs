//! Field arithmetic with native-integer constant operands (`a * 3 + 5`).
use xark::prelude::*;

#[circuit]
pub fn field_int_ops(a: Private<Field>, out: Public<Field>) {
    // out == a*3 + 5  (Mul<u64> then Add<u64>)
    require_eq(a * 3u64 + 5u64, out);
}

#[cfg(test)]
mod tests {
    use super::field_int_ops;

    #[test]
    fn accepts_valid() {
        // 10·3 + 5 = 35
        field_int_ops("10".into(), "35".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(field_int_ops("10".into(), "36".into()).is_err());
    }
}
