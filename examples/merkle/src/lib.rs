//! Merkle-tree membership as a circuit: prove a `leaf` sits at position
//! `index_bits` in a depth-4 Poseidon Merkle tree with the public `root`, given
//! its authentication path `siblings`. [`merkle_verify`] folds the path (sibling
//! mux, boolean-constrained direction bits, Poseidon compression) and asserts the
//! computed root equals the public one.
use xark_merkle::prelude::*;

/// The tree's depth: a `const` sizes the path parameters.
pub const DEPTH: usize = 4;

#[circuit]
pub fn merkle(
    leaf: Private<Field>,
    siblings: Private<[Field; DEPTH]>,
    index_bits: Private<[Field; DEPTH]>,
    root: Public<Field>,
) {
    merkle_verify(leaf, siblings, index_bits, root);
}

#[cfg(test)]
mod tests {
    use super::{DEPTH, merkle};

    // Concrete leaf, path, and LSB-first position (0b0101). The Poseidon root was
    // derived once by solving the circuit (`xark-merkle`'s `vec` test), then pinned.
    const LEAF: u64 = 7;
    const SIBLINGS: [u64; DEPTH] = [11, 22, 33, 44];
    const INDEX_BITS: [u64; DEPTH] = [1, 0, 1, 0];
    const ROOT: &str =
        "19217897426496189115890594488318047711322540293288184119629031241572428947159";

    #[test]
    fn accepts_valid_membership() {
        merkle(LEAF, SIBLINGS, INDEX_BITS, ROOT).unwrap();
    }

    #[test]
    fn rejects_wrong_root() {
        assert!(merkle(LEAF, SIBLINGS, INDEX_BITS, 12345).is_err());
    }
}
