#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

// mixed_pi: main(x: priv, y: pub) -> pub Field { x*y + x }.
// The return value is public, so `ret` is a public input equal to x*y + x.
#[circuit]
pub fn mixed_pi(x: Private<Field>, y: Public<Field>, ret: Public<Field>) {
    require_eq(x * y + x, ret);
}

#[cfg(test)]
mod tests {
    use super::mixed_pi;

    #[test]
    fn accepts_valid() {
        // 3·4 + 3 = 15
        mixed_pi("3".into(), "4".into(), "15".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(mixed_pi("3".into(), "4".into(), "16".into()).is_err());
    }
}
