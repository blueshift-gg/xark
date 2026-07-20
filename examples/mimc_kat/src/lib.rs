#![no_std]

use xark_mimc::prelude::*;

/// Known-answer circuit for the real MiMC-BN254 hash (port of `noir-lang/mimc`).
///
/// Constrains the public output to `mimc_bn254([12, 45, 78, 41])`, whose Noir
/// KAT value is
/// `18226366069841799622585958305961373004333097209608110160936134895615261821931`.
/// Solving with that value must succeed; any other value must be rejected.
pub fn circuit(out: Public<Field>) {
    assert_eq(
        mimc_bn254([
            Field::from(12u8),
            Field::from(45u8),
            Field::from(78u8),
            Field::from(41u8),
        ]),
        out,
    );
}
