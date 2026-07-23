
use xark::prelude::*;

/// `a^3` via a compile-time-unrolled `for` loop. Lowers byte-for-byte identically
/// to the equivalent `let mut i = 0; while i < 2 { acc = acc * a; i += 1; }`.
#[circuit]
pub fn for_cube(a: Private<Field>, c: Public<Field>) {
    let mut acc = a;
    for _i in 0..2u64 {
        acc = acc * a;
    }
    require_eq(acc, c);
}

#[cfg(test)]
mod tests {
    use super::for_cube;

    #[test]
    fn accepts_valid() {
        // 3³ = 27
        for_cube("3".into(), "27".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(for_cube("3".into(), "28".into()).is_err());
    }
}
