//! Untyped integer literals (`i32` to Rust) mix with `Field` on the host as in a
//! circuit (`tests/snapshot.rs`'s `integer_literals_mix_with_field`).

use xark::Field;

#[test]
fn literals_mix_with_field() {
    let x = Field::from(4);
    assert!(x * 2 + 1 == Field::from(9u8));
    assert!(2 * x - 1 == Field::from(7u8));
    assert!(1 - x == -Field::from(3u8));
    let mut y: Field = 0.into();
    y += 5;
    assert!(y == 5);
    assert!(x != 0);
}

#[test]
#[should_panic(expected = "integer -1 is negative")]
fn a_negative_literal_is_refused() {
    let _ = Field::from(-1);
}
