#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

/// Iterate a fixed-size array by value (`for x in arr`). Lowers byte-for-byte
/// identically to the equivalent `while i < N { let x = arr[i]; .. }`.
#[circuit]
pub fn for_array(a: Private<Field>, b: Private<Field>, c: Public<Field>) {
    let arr = [a, b, a];
    let mut acc = Field::constant("0");
    for x in arr {
        acc = acc + x;
    }
    require_eq(acc, c);
}

#[cfg(test)]
mod tests {
    use super::for_array;

    #[test]
    fn accepts_valid() {
        // [3,4,3] sum = 10
        for_array("3".into(), "4".into(), "10".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(for_array("3".into(), "4".into(), "11".into()).is_err());
    }
}
