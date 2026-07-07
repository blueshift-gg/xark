#![no_std]

use xark::{assert_eq, Field, Private, Public};

/// Field inverse as an *advice* gadget.
///
/// `1/x` cannot be computed with `+ - *`, so the prover supplies it as advice
/// and the circuit only verifies `x * w == 1`. This is the canonical shape for
/// every non-algebraic gadget (is_zero, bit-decomposition, range checks, ...).
fn inv(x: Field) -> Field {
    let w = Field::hint_inverse(x); // witness-gen records `w = 1/x`
    assert_eq(x * w, Field::constant("1"));
    w
}

/// Prove that the public `x_inv` really is the inverse of the private `x`.
pub fn circuit(x: Private<Field>, x_inv: Public<Field>) {
    assert_eq(inv(x), x_inv);
}
