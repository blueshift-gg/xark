//! `Field::to_bits` / `from_bits`: bit decomposition as a first-class `Field`
//! operation (composed from `hint_bit` + arithmetic + `assert_eq`, no extra
//! crate). `to_bits::<N>()` pins each bit boolean and proves `self < 2^N`;
//! `from_bits` recomposes.
#![no_std]
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(x: Private<Field>, out: Public<Field>) {
    let bits = x.to_bits::<8>(); // decompose into 8 bits (proves x < 256)
    assert_eq(Field::from_bits::<8>(bits), out); // recompose == out == x
}
