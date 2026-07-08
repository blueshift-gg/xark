//! Poseidon2 permutation circuit (BN254, t = 3, alpha = 5, R_F = 8, R_P = 56).
//!
//! Proves knowledge of a private 3-element preimage `[in0, in1, in2]` whose
//! Poseidon2 permutation equals the public output `[out0, out1, out2]`.
//!
//! The whole permutation is imported from the `xark-poseidon2` gadget crate and
//! inlined by the compiler. ARK (constant adds) and both linear layers (`M_E`,
//! `M_I`, constant-matrix products) fold into linear combinations for free;
//! every R1CS multiplication gate comes from an S-box (`x^5`).
#![no_std]

use xark::{assert_eq, Field, Private, Public};
use xark_poseidon2::poseidon2_perm;

pub fn circuit(
    in0: Private<Field>,
    in1: Private<Field>,
    in2: Private<Field>,
    out0: Public<Field>,
    out1: Public<Field>,
    out2: Public<Field>,
) {
    let out = poseidon2_perm([in0, in1, in2]);
    assert_eq(out[0], out0);
    assert_eq(out[1], out1);
    assert_eq(out[2], out2);
}
