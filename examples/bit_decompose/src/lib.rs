#![no_std]
use xark::{assert_eq, Field, Private, Public};

/// Decompose a private `x` into 8 bits and expose two of them publicly.
pub fn circuit(x: Private<Field>, bit0: Public<Field>, bit7: Public<Field>) {
    let bits = x.to_bits::<8>();
    assert_eq(bits[0], bit0);
    assert_eq(bits[7], bit7);
}
