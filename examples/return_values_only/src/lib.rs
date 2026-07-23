
use xark::prelude::*;

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
        return_values_only("6".into(), "36".into()).unwrap(); // 6² = 36
    }

    #[test]
    fn rejects_wrong() {
        assert!(return_values_only("6".into(), "37".into()).is_err());
    }
}
