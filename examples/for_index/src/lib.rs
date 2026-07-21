#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

/// Sum an array by indexing it with the `for` loop counter (`arr[i]`). Lowers
/// byte-for-byte identically to the equivalent `while i < 3` version.
#[circuit]
pub fn for_index(a: Private<Field>, b: Private<Field>, c: Public<Field>) {
    let arr = [a, b, a];
    let mut acc = Field::constant("0");
    for i in 0..3 {
        acc = acc + arr[i];
    }
    require_eq(acc, c);
}

#[cfg(test)]
mod tests {
    use super::for_index;

    #[test]
    fn accepts_valid() {
        // [3,4,3] sum = 10
        for_index("3".into(), "4".into(), "10".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(for_index("3".into(), "4".into(), "11".into()).is_err());
    }
}
