#![no_std]

use xark_poseidon::prelude::*;

/// Prove knowledge of a Poseidon(t=3, alpha=5) 2-to-1 preimage:
/// `hash2(a, b) == out`.
///
/// The whole permutation is imported from the `xark-poseidon` gadget crate and
/// inlined by the compiler. ARK (constant adds) and MDS (constant matrix mult)
/// fold into linear combinations for free; every R1CS multiplication gate comes
/// from an S-box (`x^5`).
pub fn circuit(a: Private<Field>, b: Private<Field>, out: Public<Field>) {
    assert_eq(hash2(a, b), out);
}
