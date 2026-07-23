//! Aggregate circuit inputs: an array of `Field` and a bare `Field` — the array
//! collapses to `n` inputs named by access path (`a[0]`, `a[1]`, `a[2]`).
use xark::prelude::*;

#[circuit]
pub fn agg_input(a: Private<[u8; 3]>, b: Public<Field>) {
    require_eq(a[0] + a[1] + a[2], b);
}

#[cfg(test)]
mod tests {
    use super::agg_input;

    #[test]
    fn accepts_valid() {
        agg_input([1, 2, 3], "6".into()).unwrap(); // 1 + 2 + 3 = 6
    }

    #[test]
    fn rejects_wrong() {
        assert!(agg_input([1, 2, 3], "7".into()).is_err());
    }
}
