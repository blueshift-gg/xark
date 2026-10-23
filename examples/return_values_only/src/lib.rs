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
        return_values_only(6, 36).unwrap(); // 6² = 36
    }

    #[test]
    fn rejects_wrong() {
        assert!(return_values_only(6, 37).is_err());
    }
}
