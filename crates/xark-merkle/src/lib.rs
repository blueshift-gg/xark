//! `xark-merkle`: in-circuit Merkle-tree membership verification.
//!
//! Given a `leaf`, its authentication path (`siblings` — one sibling hash per
//! level, leaf level first) and the leaf's position (`index_bits`, LSB-first:
//! bit `i` is `0` when the running node is the **left** child at level `i` and
//! `1` when it is the **right** child), [`merkle_root`] folds the path with the
//! Poseidon 2-to-1 compression ([`xark_poseidon::hash2`]) and returns the
//! computed root. [`merkle_verify`] additionally asserts it equals an expected
//! root — the membership proof.
//!
//! Soundness: every `index_bits[i]` is boolean-constrained (`b·b == b`), so a
//! prover cannot smuggle a non-`{0,1}` selector to fold a different root; given a
//! boolean bit the sibling ordering at each level is a sound linear mux
//! (`if_false + bit·(if_true − if_false)`), and the final `assert_eq` pins the
//! fold to the claimed root. The path length is the const-generic `DEPTH`.
#![no_std]

use xark::{assert_eq, Field};
use xark_poseidon::hash2;

/// Boolean-gated select `bit ? if_true : if_false`, as the linear combination
/// `if_false + bit·(if_true − if_false)`. `bit` **must** already be constrained
/// boolean (the callers in this crate do so once per level before selecting).
fn select(bit: Field, if_true: Field, if_false: Field) -> Field {
    if_false + bit * (if_true - if_false)
}

/// Fold an authentication path to its Merkle root.
///
/// `siblings[i]` is the sibling hash at level `i` (leaf level first) and
/// `index_bits[i]` is the position bit at level `i` (`0` = the running node is
/// the left child, `1` = the right child). Each bit is boolean-constrained in
/// place. Returns the computed root (composable — a larger circuit can constrain
/// it however it likes; use [`merkle_verify`] for the common equality check).
pub fn merkle_root<const DEPTH: usize>(
    leaf: Field,
    siblings: [Field; DEPTH],
    index_bits: [Field; DEPTH],
) -> Field {
    let mut node = leaf;
    let mut i = 0usize;
    while i < DEPTH {
        let bit = index_bits[i];
        bit.assert_bool();
        let sib = siblings[i];
        // bit = 0: node is the left child  → (left, right) = (node, sib)
        // bit = 1: node is the right child → (left, right) = (sib, node)
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
    assert_eq(merkle_root::<DEPTH>(leaf, siblings, index_bits), root);
}

/// Bring the gadget's public API into scope alongside the xark circuit
/// essentials (`Field`, `Public`/`Private`, `assert_eq`, `#[circuit]`), so a
/// circuit crate needs a single `use xark_merkle::prelude::*;`.
pub mod prelude {
    pub use crate::{merkle_root, merkle_verify};
    pub use xark::prelude::*;
}
