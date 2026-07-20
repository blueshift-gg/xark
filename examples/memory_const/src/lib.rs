#![cfg_attr(xark, no_std)]

use xark::{assert_eq, circuit, Field, Private, Public};

// memory_const: arr = [x, x*2, x*3]; assert(arr sum == y),
// i.e. x + 2x + 3x == y  (== 6x).
#[circuit]
pub fn memory_const(x: Private<Field>, y: Public<Field>) {
    assert_eq(x + x * Field::constant("2") + x * Field::constant("3"), y);
}

#[cfg(test)]
mod tests {
    use super::memory_const;

    #[test]
    fn accepts_valid() {
        // 6·5 = 30
        memory_const("5".into(), "30".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(memory_const("5".into(), "31".into()).is_err());
    }
}
