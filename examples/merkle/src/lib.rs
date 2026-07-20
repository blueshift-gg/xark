//! Merkle-tree membership as a circuit: prove a `leaf` sits at the position
//! `index_bits` in a depth-4 Poseidon Merkle tree with the public `root`, given
//! its authentication path `siblings`. The gadget folds the path and asserts the
//! computed root equals the public one — the whole plumbing (per-level sibling
//! mux, boolean-constrained direction bits, Poseidon compression) is hidden
//! behind [`merkle_verify`].
#![cfg_attr(xark, no_std)]

use xark_merkle::prelude::*;

const DEPTH: usize = 4;

pub fn circuit(
    leaf: Private<Field>,
    siblings: Private<[Field; DEPTH]>,
    index_bits: Private<[Field; DEPTH]>,
    root: Public<Field>,
) {
    merkle_verify(leaf, siblings, index_bits, root);
}
