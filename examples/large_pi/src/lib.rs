#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Public};

// large_pi: 16 public inputs; enforces `xs[0] + xs[15] == 30`. The running sum
// references every element so all 16 stay allocated as public inputs.
#[allow(clippy::too_many_arguments)]
#[circuit]
pub fn large_pi(
    x0: Public<Field>,
    x1: Public<Field>,
    x2: Public<Field>,
    x3: Public<Field>,
    x4: Public<Field>,
    x5: Public<Field>,
    x6: Public<Field>,
    x7: Public<Field>,
    x8: Public<Field>,
    x9: Public<Field>,
    x10: Public<Field>,
    x11: Public<Field>,
    x12: Public<Field>,
    x13: Public<Field>,
    x14: Public<Field>,
    x15: Public<Field>,
) {
    require_eq(x0 + x15, Field::constant("30"));
    // reference every element so all 16 stay allocated as public inputs
    let sum = x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15;
    require_eq(sum, Field::constant("44"));
}

#[cfg(test)]
mod tests {
    use super::large_pi;

    #[test]
    fn accepts_valid() {
        // x0+x15 = 30, total sum = 44
        large_pi(
            "10".into(),
            "14".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "20".into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(large_pi(
            "10".into(),
            "14".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "0".into(),
            "21".into()
        )
        .is_err());
    }
}
