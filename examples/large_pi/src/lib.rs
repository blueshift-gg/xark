#![no_std]

use xark::{assert_eq, Field, Public};

// large_pi: main(xs: pub [Field; 16]) { assert(xs[0] + xs[15] == 30) }.
// The 16 public inputs are all referenced (the running sum keeps every element
// allocated as a public input) and the faithful `xs[0] + xs[15] == 30`
// constraint is enforced.
#[allow(clippy::too_many_arguments)]
pub fn circuit(
    x0: Public<Field>,
    x1: Public<Field>,
    x2: Public<Field>,
    x3: Public<Field>,
    x4: Public<Field>,
    x5: Public<Field>,
    x6: Public<Field>,
    x7: Public<Field>,
    x8: Public<Field>,
    x9: Public<Field>,
    x10: Public<Field>,
    x11: Public<Field>,
    x12: Public<Field>,
    x13: Public<Field>,
    x14: Public<Field>,
    x15: Public<Field>,
) {
    // The circuit's constraint.
    assert_eq(x0 + x15, Field::constant("30"));
    // Reference every element so all 16 stay allocated as public inputs.
    let sum = x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15;
    assert_eq(sum, Field::constant("44"));
}
