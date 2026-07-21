#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

// return_values_only: main(x: priv) -> pub Field { x*x }.
#[circuit]
pub fn return_values_only(x: Private<Field>, ret: Public<Field>) {
    require_eq(x * x, ret);
}

#[cfg(test)]
mod tests {
    use super::return_values_only;

    #[test]
    fn accepts_valid() {
        // 6² = 36
        return_values_only("6".into(), "36".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(return_values_only("6".into(), "37".into()).is_err());
    }
}
