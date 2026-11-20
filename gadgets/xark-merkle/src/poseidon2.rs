//! Merkle trees over Poseidon2: membership, appends, and non-membership in an
//! indexed tree.
//!
//! Nodes are the Poseidon2 2-to-1 compression [`xark_poseidon2::hash2`]; paths are
//! the crate root's shape (`siblings` leaf level first, `index_bits` least
//! significant first, `0` for a left child). Every level orders its pair with the
//! crate's [`cond_swap`], whose rows are proven in `formal/Formal/CondSwap.lean`, so
//! a non-boolean index bit is refused. Nothing here is a `#[gadget]` of its own: it
//! is `cond_swap` and Poseidon2 composed, with no rows of its own beyond one product
//! per level where a second node rides an already-checked bit (see [`merkle_append`]).
//!
//! The indexed tree is Aztec's nullifier tree (the Aztec protocol docs, "Indexed
//! Merkle Tree"): its leaves are a linked list sorted by value, each
//! [`IndexedLeaf`] naming the next larger value and where it is. A value `x` is
//! absent when some leaf has
//! `value < x < next_value`, or `value < x` and `next_value = 0` (the largest
//! leaf). [`indexed_insert`] adds a value and keeps the list sorted, so a tree only
//! ever changed by it (from the one-leaf tree [`crate::tree::IndexedTree::new`]
//! builds) stays one whose non-membership proofs mean what they say.

use xark::{Field, input, require, require_eq};
use xark_poseidon2::hash2;

use crate::cond_swap;

/// Fold an authentication path to its Merkle root, as [`crate::merkle_root`] does
/// with Poseidon2 nodes. Each bit is constrained boolean by [`cond_swap`].
pub fn merkle_root<const DEPTH: usize>(
    leaf: Field,
    siblings: [Field; DEPTH],
    index_bits: [Field; DEPTH],
) -> Field {
    let mut node = leaf;
    let mut i = 0usize;
    while i < DEPTH {
        let (left, right) = cond_swap(index_bits[i], node, siblings[i]);
        node = hash2(left, right);
        i += 1;
    }
    node
}

/// Assert `leaf` is in the Poseidon2 tree with this `root`, at `index_bits`.
pub fn merkle_verify<const DEPTH: usize>(
    leaf: Field,
    siblings: [Field; DEPTH],
    index_bits: [Field; DEPTH],
    root: Field,
) {
    require_eq(merkle_root::<DEPTH>(leaf, siblings, index_bits), root);
}

/// Fold two leaves up the same path: `first` through [`cond_swap`], which
/// constrains each bit boolean, and `second` through the same swap written out,
/// `l = node + bit·(sibling − node)`, one product, since its bit is already
/// boolean. The second fold is the one to give a constant leaf: a `cond_swap` with
/// a constant input is a different call for the Lean coverage check.
fn fold_two<const DEPTH: usize>(
    first: Field,
    second: Field,
    siblings: [Field; DEPTH],
    index_bits: [Field; DEPTH],
) -> (Field, Field) {
    let (mut a, mut b) = (first, second);
    let mut i = 0usize;
    while i < DEPTH {
        let (left, right) = cond_swap(index_bits[i], a, siblings[i]);
        a = hash2(left, right);
        let left = b + index_bits[i] * (siblings[i] - b);
        b = hash2(left, b + siblings[i] - left);
        i += 1;
    }
    (a, b)
}

/// Append `leaf` at `index_bits`, a slot holding `empty_leaf` in the tree rooted at
/// `old_root`, and return the new root. One path proves both: `empty_leaf` under
/// `old_root` and `leaf` under the returned root share every sibling, so the new
/// tree is the old one with that one slot written. Require the result equal to the
/// new root a caller publishes:
///
/// ```ignore
/// require_eq(merkle_append(old_root, EMPTY, leaf, siblings, bits), new_root);
/// ```
///
/// Which slot is the caller's to bind: a program that appends in order checks
/// `index_bits` spell its next index (`Field::from(index).to_bits::<DEPTH>()`). The
/// empty leaf must be a value no real leaf takes (a constant with no known preimage
/// under the leaf hash), or "the slot was empty" proves nothing.
pub fn merkle_append<const DEPTH: usize>(
    old_root: Field,
    empty_leaf: Field,
    leaf: Field,
    siblings: [Field; DEPTH],
    index_bits: [Field; DEPTH],
) -> Field {
    let (new_root, empty_root) = fold_two(leaf, empty_leaf, siblings, index_bits);
    require_eq(empty_root, old_root);
    new_root
}

/// The empty slot of an indexed tree. A leaf hashes three fields with the
/// Poseidon2 sponge, so no leaf is `0` unless someone finds a preimage of it.
pub const INDEXED_EMPTY_LEAF: u64 = 0;

/// A leaf of an indexed tree: a value, and the next larger value in the tree and
/// its index (`next_value = 0` for the largest; then `next_index` is `0` too).
#[input]
#[derive(PartialEq)]
pub struct IndexedLeaf {
    pub value: Field,
    pub next_index: Field,
    pub next_value: Field,
}

impl IndexedLeaf {
    /// The leaf's hash, what the tree holds: the Poseidon2 sponge over its three
    /// fields. The sponge's capacity starts at the length, 3, and a node's
    /// compression at 0, so a leaf and a node are different functions.
    pub fn hash(&self) -> Field {
        xark_poseidon2::hash([self.value, self.next_index, self.next_value])
    }
}

/// `low.value < x`, and `x < low.next_value` unless `low.next_value = 0`: `low`
/// is the leaf `x` would follow, so `x` is no leaf's value.
///
/// Both comparisons are on `BITS`-bit integers: `lt::<BITS>` range-checks both
/// sides below `2^BITS` (`BITS ≤ 252`, so `a − b + 2^BITS` can't wrap the field),
/// and a value at or above `2^BITS` fails the check rather than comparing wrong.
fn require_between<const BITS: usize>(low: IndexedLeaf, x: Field) {
    require(low.value.lt::<BITS>(x));
    let last = Field::from(low.next_value.is_zero());
    let below = Field::from(x.lt::<BITS>(low.next_value));
    // One of the two holds: the low leaf is the largest, or `x` is below its next.
    require_eq(
        (Field::one() - last) * (Field::one() - below),
        Field::zero(),
    );
}

/// Assert `x` is in no leaf of the indexed tree rooted at `root`, through its low
/// leaf `low` at `index_bits` with path `siblings`: `low` is in the tree and `x`
/// falls strictly between `low.value` and `low.next_value`.
///
/// Values are `BITS`-bit integers, `BITS ≤ 252`, and `0` is taken (the first leaf,
/// the list's head). A field element at or above `2^BITS`, as a hash can be, must
/// be reduced first; with `BITS = 252` about a third of uniform field elements fit.
pub fn indexed_non_membership<const DEPTH: usize, const BITS: usize>(
    x: Field,
    low: IndexedLeaf,
    siblings: [Field; DEPTH],
    index_bits: [Field; DEPTH],
    root: Field,
) {
    require_between::<BITS>(low, x);
    merkle_verify::<DEPTH>(low.hash(), siblings, index_bits, root);
}

/// Insert `x` into the indexed tree rooted at `old_root` and return the new root.
///
/// `x` is absent, through its low leaf `low` (as [`indexed_non_membership`]); the
/// low leaf is rewritten to point at `x` in place (same path); then the leaf
/// `(x, low.next_index, low.next_value)` is appended at `new_index_bits`, a slot
/// that was empty after that rewrite (`new_siblings` is its path then). So the
/// list stays sorted and `x` is in it once.
///
/// Like [`merkle_append`], which empty slot is the caller's to bind (to its next
/// index, normally); `Field::from_bits(new_index_bits)` is that index.
pub fn indexed_insert<const DEPTH: usize, const BITS: usize>(
    old_root: Field,
    x: Field,
    low: IndexedLeaf,
    low_siblings: [Field; DEPTH],
    low_index_bits: [Field; DEPTH],
    new_siblings: [Field; DEPTH],
    new_index_bits: [Field; DEPTH],
) -> Field {
    require_between::<BITS>(low, x);
    let updated = IndexedLeaf {
        value: low.value,
        next_index: Field::from_bits(new_index_bits),
        next_value: x,
    };
    let (low_root, mid_root) = fold_two(low.hash(), updated.hash(), low_siblings, low_index_bits);
    require_eq(low_root, old_root);
    let leaf = IndexedLeaf {
        value: x,
        next_index: low.next_index,
        next_value: low.next_value,
    };
    merkle_append(
        mid_root,
        Field::from(INDEXED_EMPTY_LEAF),
        leaf.hash(),
        new_siblings,
        new_index_bits,
    )
}

/// The Poseidon2 tree's API plus the xark circuit essentials, for a single
/// `use xark_merkle::poseidon2::prelude::*;`.
pub mod prelude {
    pub use super::{
        IndexedLeaf, indexed_insert, indexed_non_membership, merkle_append, merkle_root,
        merkle_verify,
    };
    pub use xark::prelude::*;
}
