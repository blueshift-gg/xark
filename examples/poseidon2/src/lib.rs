//! Poseidon2 permutation circuit (BN254, t = 3, alpha = 5, R_F = 8, R_P = 56).
//!
//! Proves knowledge of a private 3-element preimage `[in0, in1, in2]` whose
//! Poseidon2 permutation equals the public output `[out0, out1, out2]`.
//!
//! The whole permutation is imported from the `xark-poseidon2` gadget crate and
//! inlined by the compiler. ARK (constant adds) and both linear layers (`M_E`,
//! `M_I`, constant-matrix products) fold into linear combinations for free;
//! every R1CS multiplication gate comes from an S-box (`x^5`).
#![cfg_attr(xark, no_std)]

use xark_poseidon2::prelude::*;

#[circuit]
pub fn poseidon2(
    in0: Private<Field>,
    in1: Private<Field>,
    in2: Private<Field>,
    out0: Public<Field>,
    out1: Public<Field>,
    out2: Public<Field>,
) {
    let out = poseidon2_perm([in0, in1, in2]);
    require_eq(out[0], out0);
    require_eq(out[1], out1);
    require_eq(out[2], out2);
}

#[cfg(test)]
mod tests {
    use super::poseidon2;

    #[test]
    fn accepts_valid() {
        // poseidon2_perm([1,2,3])
        poseidon2(
            "1".into(),
            "2".into(),
            "3".into(),
            "4737982494702600552753609419126955242994596445692557044681458296415162795880".into(),
            "9698155156890762076414037574068404457164720954413259397447872502075783415658".into(),
            "18259628997120261506554896720810362547891614655348127750921457211768261324825".into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(poseidon2(
            "1".into(),
            "2".into(),
            "3".into(),
            "1".into(),
            "9698155156890762076414037574068404457164720954413259397447872502075783415658".into(),
            "18259628997120261506554896720810362547891614655348127750921457211768261324825".into()
        )
        .is_err());
    }
}
