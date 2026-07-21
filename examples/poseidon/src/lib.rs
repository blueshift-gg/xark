#![cfg_attr(xark, no_std)]

use xark_poseidon::prelude::*;

/// Prove knowledge of a Poseidon(t=3, alpha=5) 2-to-1 preimage:
/// `hash2(a, b) == out`.
///
/// The whole permutation is imported from the `xark-poseidon` gadget crate and
/// inlined by the compiler. ARK (constant adds) and MDS (constant matrix mult)
/// fold into linear combinations for free; every R1CS multiplication gate comes
/// from an S-box (`x^5`).
#[circuit]
pub fn poseidon(a: Private<Field>, b: Private<Field>, out: Public<Field>) {
    require_eq(hash2(a, b), out);
}

#[cfg(test)]
mod tests {
    use super::poseidon;

    #[test]
    #[ignore = "heavy: original-Poseidon solve (big-coefficient MDS-fold LCs)"]
    fn accepts_valid() {
        // poseidon.hash2(3, 5)
        poseidon(
            "3".into(),
            "5".into(),
            "7003178825990875955236852857865616475160076985313430133088248668396799513116".into(),
        )
        .unwrap();
    }

    #[test]
    #[ignore = "heavy: original-Poseidon solve (big-coefficient MDS-fold LCs)"]
    fn rejects_wrong() {
        assert!(poseidon("3".into(), "5".into(), "1".into()).is_err());
    }
}
