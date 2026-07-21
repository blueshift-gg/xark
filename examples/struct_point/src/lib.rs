//! Struct support: a `Point { x: [Field; 3], y: [Field; 3] }` built in-circuit and
//! passed through a helper returning a tuple, with field access `p.x[i]`. Exercises
//! `AggregateKind::Adt` and tuple lowering — zero-cost, same R1CS as bare fields.
#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

struct Point {
    x: [Field; 3],
    y: [Field; 3],
}

/// Return the first limb of `x + y` (linear) and of `x * y` (one mul gate).
fn combine(p: Point) -> (Field, Field) {
    (p.x[0] + p.y[0], p.x[0] * p.y[0])
}

#[circuit]
pub fn struct_point(
    x: Private<[Field; 3]>,
    y: Private<[Field; 3]>,
    sum: Public<Field>,
    prod: Public<Field>,
) {
    let p = Point { x, y };
    let (s, m) = combine(p);
    require_eq(s, sum);
    require_eq(m, prod);
}

#[cfg(test)]
mod tests {
    use super::struct_point;

    #[test]
    fn accepts_valid() {
        struct_point(
            ["3".into(), "0".into(), "0".into()],
            ["5".into(), "0".into(), "0".into()],
            "8".into(),
            "15".into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong_product() {
        assert!(struct_point(
            ["3".into(), "0".into(), "0".into()],
            ["5".into(), "0".into(), "0".into()],
            "8".into(),
            "16".into(),
        )
        .is_err());
    }
}
