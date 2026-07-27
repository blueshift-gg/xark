//! `Field`'s `Debug` prints its decimal value, so the values are grab-able
//! straight out of a `{:?}` dump (of a bare `Field`, a `#[derive(CircuitInput)]`
//! struct, or a generated `<Fn>Inputs`) to feed `xark prove --inputs`.

use xark::Field;

#[test]
fn field_debug_is_decimal() {
    assert_eq!(format!("{:?}", Field::from_u64(19900101)), "Field(19900101)");
    assert_eq!(format!("{:?}", Field::zero()), "Field(0)");
    assert_eq!(format!("{:?}", Field::one()), "Field(1)");
    // A big (32-byte) constant still renders its full decimal.
    assert_eq!(
        format!("{:?}", Field::from_u128(340282366920938463463374607431768211455)),
        "Field(340282366920938463463374607431768211455)"
    );
}

#[test]
fn derived_struct_debug_shows_grabbable_decimals() {
    #[derive(Debug)]
    #[allow(dead_code)] // fields are read only through the derived `Debug`
    struct Pt {
        x: Field,
        y: Field,
    }
    assert_eq!(
        format!(
            "{:?}",
            Pt {
                x: Field::from_u8(3),
                y: Field::from_u16(9)
            }
        ),
        "Pt { x: Field(3), y: Field(9) }"
    );
}
