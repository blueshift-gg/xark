//! Struct support: a `Point { x: [Field; 3], y: [Field; 3] }` built in-circuit and
//! passed through a helper returning a tuple, with field access `p.x[i]`. Exercises
//! `AggregateKind::Adt` and tuple lowering — zero-cost, same R1CS as bare fields.

use xark::prelude::*;

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
    use xark::Field;

    fn point_coord(value: u64) -> [Field; 3] {
        [value.into(), 0u64.into(), 0u64.into()]
    }

    #[test]
    fn accepts_valid() {
        struct_point(
            point_coord(3),
            point_coord(5),
            8u64.into(),
            15u64.into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong_product() {
        assert!(struct_point(
            point_coord(3),
            point_coord(5),
            8u64.into(),
            16u64.into(),
        )
        .is_err());
    }
}
