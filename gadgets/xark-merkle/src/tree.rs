//! Host-side trees (not in a circuit build): the roots and paths a circuit in this
//! crate proves, computed the way it computes them, so a client, a distributor or
//! a test doesn't hand-roll its own copy.
//!
//! [`Tree`] is a fixed-depth tree filled from the left: leaves `0..len()` are
//! written, every slot after them holds the empty leaf. Its nodes are Poseidon2
//! ([`Tree::poseidon2`], for [`crate::poseidon2`]) or Poseidon ([`Tree::poseidon`],
//! for [`crate::merkle_root`]). [`IndexedTree`] is the indexed tree
//! [`crate::poseidon2::indexed_non_membership`] and
//! [`crate::poseidon2::indexed_insert`] prove against.
//!
//! ```
//! use xark::Field;
//! use xark_merkle::poseidon2::merkle_root;
//! use xark_merkle::tree::Tree;
//!
//! let mut tree = Tree::<20>::poseidon2(Field::from(0u64));
//! let index = tree.push(Field::from(7u64));
//! let path = tree.path(index);
//! assert_eq!(merkle_root(Field::from(7u64), path.siblings, path.index_bits()), tree.root());
//! ```

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use xark::Field;

use crate::poseidon2::{INDEXED_EMPTY_LEAF, IndexedLeaf};

/// A leaf's authentication path: its index, and its sibling at each height, leaf
/// level first. The circuits take `siblings` and [`Path::index_bits`].
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Path<const DEPTH: usize> {
    pub index: usize,
    pub siblings: [Field; DEPTH],
}

impl<const DEPTH: usize> Path<DEPTH> {
    /// `index` as `DEPTH` bits, least significant first: the circuits' `index_bits`.
    pub fn index_bits(&self) -> [Field; DEPTH] {
        core::array::from_fn(|i| Field::from(((self.index >> i) & 1) as u64))
    }
}

/// A Merkle tree of depth `DEPTH` filled from the left; see the module docs.
#[derive(Clone, Debug)]
pub struct Tree<const DEPTH: usize> {
    hash: fn(Field, Field) -> Field,
    /// `empty[h]` is the root of an empty subtree of height `h`, `0..=DEPTH`.
    empty: Vec<Field>,
    /// `levels[h]` holds the height-`h` nodes over the written leaves; a node past
    /// its end is `empty[h]`.
    levels: Vec<Vec<Field>>,
}

impl<const DEPTH: usize> Tree<DEPTH> {
    /// The empty tree with `hash` for its nodes and `empty_leaf` in every slot.
    pub fn new(hash: fn(Field, Field) -> Field, empty_leaf: Field) -> Self {
        // A host index is a `usize`, and a circuit's `from_bits` takes 253 bits at most.
        assert!(
            DEPTH < usize::BITS as usize,
            "a tree of depth {DEPTH} can't be indexed"
        );
        let mut empty = vec![empty_leaf];
        for h in 0..DEPTH {
            empty.push(hash(empty[h], empty[h]));
        }
        Tree {
            hash,
            empty,
            levels: vec![Vec::new(); DEPTH + 1],
        }
    }

    /// The empty Poseidon2 tree ([`xark_poseidon2::hash2`] nodes), as
    /// [`crate::poseidon2`] folds it.
    pub fn poseidon2(empty_leaf: Field) -> Self {
        Self::new(xark_poseidon2::hash2, empty_leaf)
    }

    /// The empty Poseidon tree ([`xark_poseidon::hash2`] nodes), as
    /// [`crate::merkle_root`] folds it.
    pub fn poseidon(empty_leaf: Field) -> Self {
        Self::new(xark_poseidon::hash2, empty_leaf)
    }

    /// How many leaves the tree has room for, `2^DEPTH`.
    pub fn capacity(&self) -> usize {
        1 << DEPTH
    }

    /// How many leaves are written: the next [`Tree::push`] goes at this index.
    pub fn len(&self) -> usize {
        self.levels[0].len()
    }

    /// Whether no leaf is written.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The roots of the empty subtrees, of heights `0..=DEPTH`: `[0]` is the empty
    /// leaf and `[DEPTH]` the empty tree's root. The first `DEPTH` are the empty
    /// tree's first path.
    pub fn empty_subtrees(&self) -> &[Field] {
        &self.empty
    }

    /// The node at height `h`, position `i` in its level.
    fn node(&self, h: usize, i: usize) -> Field {
        self.levels[h].get(i).copied().unwrap_or(self.empty[h])
    }

    /// The tree's root.
    pub fn root(&self) -> Field {
        self.node(DEPTH, 0)
    }

    /// The leaf at `index`: the empty leaf past [`Tree::len`].
    pub fn leaf(&self, index: usize) -> Field {
        self.node(0, index)
    }

    /// The path of the slot at `index`, written or not: the next free slot's
    /// path is what [`crate::poseidon2::merkle_append`] takes.
    pub fn path(&self, index: usize) -> Path<DEPTH> {
        assert!(
            index < self.capacity(),
            "index {index} is past the tree's {} slots",
            self.capacity()
        );
        Path {
            index,
            siblings: core::array::from_fn(|h| self.node(h, (index >> h) ^ 1)),
        }
    }

    /// Write `leaf` at the next free slot and return its index.
    pub fn push(&mut self, leaf: Field) -> usize {
        let index = self.len();
        self.extend([leaf]);
        index
    }

    /// Write `leaves` at the next free slots, in order. Each level is hashed once
    /// from the first changed node on, so building a tree this way costs one hash
    /// per node, not one path per leaf.
    pub fn extend(&mut self, leaves: impl IntoIterator<Item = Field>) {
        let mut from = self.len();
        self.levels[0].extend(leaves);
        assert!(self.len() <= self.capacity(), "the tree is full");
        for h in 0..DEPTH {
            from /= 2;
            let parents = self.levels[h].len().div_ceil(2);
            let fresh: Vec<Field> = (from..parents)
                .map(|i| (self.hash)(self.node(h, 2 * i), self.node(h, 2 * i + 1)))
                .collect();
            self.levels[h + 1].truncate(from);
            self.levels[h + 1].extend(fresh);
        }
    }

    /// Rewrite the written leaf at `index` (an indexed tree's low leaf, say).
    pub fn set(&mut self, index: usize, leaf: Field) {
        assert!(index < self.len(), "slot {index} isn't written; push to it");
        self.levels[0][index] = leaf;
        let mut i = index;
        for h in 0..DEPTH {
            i /= 2;
            self.levels[h + 1][i] = (self.hash)(self.node(h, 2 * i), self.node(h, 2 * i + 1));
        }
    }
}

/// A field element's value as a key that sorts as the integer does: its limbs,
/// most significant first. (On the host a `Field` holds its value in `[0, r)`.)
fn key(x: Field) -> [u64; 4] {
    let l = x.to_limbs();
    [l[3], l[2], l[1], l[0]]
}

/// Why [`IndexedTree::insert`] refused a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InsertError {
    /// The value is already a leaf's (`0` always is: the list's head).
    Present,
    /// Every slot is written.
    Full,
}

/// What [`crate::poseidon2::indexed_non_membership`] takes to prove a value absent.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct NonMembership<const DEPTH: usize> {
    /// The leaf the value would follow.
    pub low: IndexedLeaf,
    /// `low`'s path.
    pub path: Path<DEPTH>,
}

/// What [`crate::poseidon2::indexed_insert`] takes to prove an insertion, and the
/// roots before and after.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Insertion<const DEPTH: usize> {
    pub old_root: Field,
    pub new_root: Field,
    pub value: Field,
    /// The low leaf before the insertion, and its path then.
    pub low: IndexedLeaf,
    pub low_path: Path<DEPTH>,
    /// The new leaf's slot's path once the low leaf points at it: `new_path.index`
    /// is where the value went.
    pub new_path: Path<DEPTH>,
}

/// An indexed Merkle tree over Poseidon2: leaves are [`IndexedLeaf`] hashes, a
/// linked list sorted by value starting at the leaf `(0, 0, 0)` in slot 0, and
/// empty slots hold [`INDEXED_EMPTY_LEAF`]. Values compare as the integers in
/// `[0, r)`; a circuit compares them as `BITS`-bit integers, so insert only values
/// below `2^BITS` into a tree a circuit with that `BITS` proves against.
#[derive(Clone, Debug)]
pub struct IndexedTree<const DEPTH: usize> {
    tree: Tree<DEPTH>,
    leaves: Vec<IndexedLeaf>,
    /// Each value's slot, sorted by value.
    slots: BTreeMap<[u64; 4], usize>,
}

impl<const DEPTH: usize> Default for IndexedTree<DEPTH> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const DEPTH: usize> IndexedTree<DEPTH> {
    /// The tree with only the list's head, `(0, 0, 0)` in slot 0.
    pub fn new() -> Self {
        let head = IndexedLeaf {
            value: Field::zero(),
            next_index: Field::zero(),
            next_value: Field::zero(),
        };
        let mut tree = Tree::poseidon2(Field::from(INDEXED_EMPTY_LEAF));
        tree.push(head.hash());
        IndexedTree {
            tree,
            leaves: vec![head],
            slots: BTreeMap::from([(key(Field::zero()), 0)]),
        }
    }

    pub fn root(&self) -> Field {
        self.tree.root()
    }

    /// How many leaves are written, the head included.
    pub fn len(&self) -> usize {
        self.leaves.len()
    }

    /// Never: the head is always there.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// The leaf at `index`, if written.
    pub fn leaf(&self, index: usize) -> Option<IndexedLeaf> {
        self.leaves.get(index).copied()
    }

    /// The path of the slot at `index`.
    pub fn path(&self, index: usize) -> Path<DEPTH> {
        self.tree.path(index)
    }

    /// The slot holding `value`, if some leaf does.
    pub fn find(&self, value: Field) -> Option<usize> {
        self.slots.get(&key(value)).copied()
    }

    /// The slot of `value`'s low leaf: the leaf with the largest value below it.
    /// `None` when `value` is in the tree (so `0` never has one).
    pub fn low_leaf(&self, value: Field) -> Option<usize> {
        if self.find(value).is_some() {
            return None;
        }
        // The head's 0 is below every other value, so a smaller one exists.
        self.slots.range(..key(value)).next_back().map(|(_, &i)| i)
    }

    /// What proves `value` absent, or `None` when it's in the tree.
    pub fn non_membership(&self, value: Field) -> Option<NonMembership<DEPTH>> {
        let i = self.low_leaf(value)?;
        Some(NonMembership {
            low: self.leaves[i],
            path: self.tree.path(i),
        })
    }

    /// Insert `value` at the next free slot, pointing its low leaf at it.
    pub fn insert(&mut self, value: Field) -> Result<Insertion<DEPTH>, InsertError> {
        let low_index = self.low_leaf(value).ok_or(InsertError::Present)?;
        let new_index = self.len();
        if new_index == self.tree.capacity() {
            return Err(InsertError::Full);
        }
        let old_root = self.root();
        let low = self.leaves[low_index];
        let low_path = self.tree.path(low_index);

        let updated = IndexedLeaf {
            value: low.value,
            next_index: Field::from(new_index as u64),
            next_value: value,
        };
        self.leaves[low_index] = updated;
        self.tree.set(low_index, updated.hash());
        let new_path = self.tree.path(new_index);

        let leaf = IndexedLeaf {
            value,
            next_index: low.next_index,
            next_value: low.next_value,
        };
        self.leaves.push(leaf);
        self.tree.push(leaf.hash());
        self.slots.insert(key(value), new_index);
        Ok(Insertion {
            old_root,
            new_root: self.root(),
            value,
            low,
            low_path,
            new_path,
        })
    }
}
