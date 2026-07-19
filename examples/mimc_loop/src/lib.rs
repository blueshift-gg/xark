#![no_std]

use xark::{assert_eq, Field, Private, Public};

/// One MiMC round: `(state + key + round_constant)^3`.
fn round(state: Field, key: Field, c: Field) -> Field {
    let t = state + key + c;
    t.pow(3)
}

/// MiMC written idiomatically with a `while` loop over an array of round
/// constants. It lowers to *exactly the same* R1CS as the hand-unrolled
/// `examples/mimc` — arrays, bounded loops, and function inlining all compose.
///
/// The loop is unrolled at compile time (`while i < 3`), the round constants are
/// a fixed `[Field; 3]` array indexed by the loop counter, and `round` inlines
/// per iteration.
pub fn circuit(x: Private<Field>, k: Public<Field>, h: Public<Field>) {
    let cs = [
        Field::constant("0"),
        Field::constant(
            "7120861356467033611736373842526102177239622603558704633600844922174959859415",
        ),
        Field::constant(
            "5464731394973421946722394282035800941955447322641943688940765294088180338198",
        ),
    ];

    let mut s = x;
    let mut i = 0usize;
    while i < 3 {
        s = round(s, k, cs[i]);
        i += 1;
    }

    assert_eq(s + k, h);
}
