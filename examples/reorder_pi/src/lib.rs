#![cfg_attr(xark, no_std)]

use xark::{assert_eq, circuit, Field, Private, Public};

// reorder_pi: main(a: pub, b: priv, c: pub) { assert(b*b == a+c) }.
#[circuit]
pub fn reorder_pi(a: Public<Field>, b: Private<Field>, c: Public<Field>) {
    assert_eq(b * b, a + c);
}

#[cfg(test)]
mod tests {
    use super::reorder_pi;

    #[test]
    fn accepts_valid() {
        // 5² = 25 = 10 + 15
        reorder_pi("10".into(), "5".into(), "15".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(reorder_pi("10".into(), "5".into(), "16".into()).is_err());
    }
}
