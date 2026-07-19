#![no_std]

use xark::{assert_eq, Field, Private, Public};

/// A small 3-round MiMC-structured permutation (exponent 3) with key addition,
/// hand-unrolled. This is a *compiler-feature demo*, not the real hash — for a
/// cryptographic MiMC-p/p (exponent 7, 91 rounds, matching `noir-lang/mimc`) use
/// the `xark-mimc` gadget crate (see `examples/mimc_gadget`).
///
/// `state ← (state + k + c_i)^3` per round (with `c_0 = 0`), finalized with a
/// key addition, then constrained to equal the public digest `h`. Round
/// constants are full BN254-field-sized values, exercising big-integer field
/// constants. (Compile with `--field bn254`.)
///
/// It is deliberately hand-unrolled so the snapshot suite can check that the
/// loop form (`examples/mimc_loop`) and cross-crate gadget inlining lower to the
/// exact same R1CS.
pub fn circuit(x: Private<Field>, k: Public<Field>, h: Public<Field>) {
    let c1 = Field::constant(
        "7120861356467033611736373842526102177239622603558704633600844922174959859415",
    );
    let c2 = Field::constant(
        "5464731394973421946722394282035800941955447322641943688940765294088180338198",
    );

    // round 0 (c_0 = 0)
    let mut s = x + k;
    s = s.pow(3);

    // round 1
    s = s + k + c1;
    s = s.pow(3);

    // round 2
    s = s + k + c2;
    s = s.pow(3);

    // finalize with a key addition and constrain to the public digest
    s = s + k;
    assert_eq(s, h);
}
