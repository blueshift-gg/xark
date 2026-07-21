//! `xark-merkle`: in-circuit Merkle-tree membership verification.
//!
//! [`merkle_root`] folds an authentication path (`siblings`, leaf level first)
//! with the leaf position (`index_bits`, LSB-first: `0` = left child, `1` =
//! right child) through the Poseidon 2-to-1 compression ([`xark_poseidon::hash2`])
//! and returns the root. [`merkle_verify`] additionally asserts it equals an
//! expected root.
//!
//! Soundness: every `index_bits[i]` is boolean-constrained (`b·b == b`), so a
//! prover cannot smuggle a non-`{0,1}` selector; given a boolean bit the sibling
//! ordering is a sound linear mux, and the final `require_eq` pins the fold to
//! the claimed root.
#![no_std]

use xark::{Field, require_eq};
use xark_poseidon::hash2;

/// Boolean-gated select `bit ? if_true : if_false`. `bit` **must** already be
/// constrained boolean (callers do so once per level before selecting).
fn select(bit: Field, if_true: Field, if_false: Field) -> Field {
    if_false + bit * (if_true - if_false)
}

/// Fold an authentication path to its Merkle root.
///
/// `siblings[i]` is the sibling hash and `index_bits[i]` the position bit at
/// level `i` (`0` = running node is left child, `1` = right). Each bit is
/// boolean-constrained in place. Returns the computed root (use
/// [`merkle_verify`] for the common equality check).
pub fn merkle_root<const DEPTH: usize>(
    leaf: Field,
    siblings: [Field; DEPTH],
    index_bits: [Field; DEPTH],
) -> Field {
    let mut node = leaf;
    let mut i = 0usize;
    while i < DEPTH {
        let bit = index_bits[i];
        bit.require_bool();
        let sib = siblings[i];
        // bit selects child order: 0 → (node, sib), 1 → (sib, node).
        let left = select(bit, sib, node);
        let right = select(bit, node, sib);
        node = hash2(left, right);
        i += 1;
    }
    node
}

/// Assert `leaf` is a member of the Merkle tree with the given `root`, at the
/// position encoded by `index_bits`, with authentication path `siblings`.
/// Emits [`merkle_root`]'s constraints plus one equality against `root`.
pub fn merkle_verify<const DEPTH: usize>(
    leaf: Field,
    siblings: [Field; DEPTH],
    index_bits: [Field; DEPTH],
    root: Field,
) {
    require_eq(merkle_root::<DEPTH>(leaf, siblings, index_bits), root);
}

/// Gadget API plus the xark circuit essentials, for a single
/// `use xark_merkle::prelude::*;`.
pub mod prelude {
    pub use crate::{merkle_root, merkle_verify};
    pub use xark::prelude::*;
}
