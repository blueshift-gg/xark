//! Merkle-tree membership as a circuit: prove a `leaf` sits at position
//! `index_bits` in a depth-4 Poseidon Merkle tree with the public `root`, given
//! its authentication path `siblings`. [`merkle_verify`] folds the path (sibling
//! mux, boolean-constrained direction bits, Poseidon compression) and asserts the
//! computed root equals the public one.
#![cfg_attr(xark, no_std)]

use xark_merkle::prelude::*;

#[circuit]
pub fn merkle(
    leaf: Private<Field>,
    siblings: Private<[Field; 4]>,
    index_bits: Private<[Field; 4]>,
    root: Public<Field>,
) {
    merkle_verify(leaf, siblings, index_bits, root);
}

#[cfg(test)]
mod tests {
    use super::merkle;

    // Concrete leaf, path, and LSB-first position (0b0101). The Poseidon root was
    // derived once by solving the circuit (`xark-merkle`'s `vec` test), then pinned.
    const LEAF: &str = "7";
    const SIBLINGS: [&str; 4] = ["11", "22", "33", "44"];
    const INDEX_BITS: [&str; 4] = ["1", "0", "1", "0"];
    const ROOT: &str =
        "19217897426496189115890594488318047711322540293288184119629031241572428947159";

    fn path() -> ([String; 4], [String; 4]) {
        (SIBLINGS.map(String::from), INDEX_BITS.map(String::from))
    }

    #[test]
    fn accepts_valid_membership() {
        let (siblings, index_bits) = path();
        merkle(LEAF.into(), siblings, index_bits, ROOT.into()).unwrap();
    }

    #[test]
    fn rejects_wrong_root() {
        let (siblings, index_bits) = path();
        assert!(merkle(LEAF.into(), siblings, index_bits, "12345".into()).is_err());
    }
}
