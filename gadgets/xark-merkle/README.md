# xark-merkle

[![crates.io](https://img.shields.io/crates/v/xark-merkle.svg)](https://crates.io/crates/xark-merkle)
[![docs.rs](https://img.shields.io/docsrs/xark-merkle)](https://docs.rs/xark-merkle)

Merkle trees for xark circuits: prove a private leaf is in a tree with a public
root without saying which leaf, append a leaf to a tree, and prove a value is
*not* in an indexed tree. The crate also builds the trees on the host, so the
client that makes a proof computes the same roots and paths as the circuit.

```toml
[dependencies]
xark = "0.4"
xark-merkle = "0.4"
```

## Use

```rust
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
```

`siblings` is the authentication path, leaf level first. `index_bits` is the
leaf's position, least significant bit first: `0` means the running node is the
left child at that level, `1` the right. See
[`examples/merkle`](https://github.com/blueshift-gg/xark/tree/master/examples/merkle).

The crate root hashes nodes with Poseidon (`xark_poseidon::hash2`).
`xark_merkle::poseidon2` has the same functions with Poseidon2 nodes
(`xark_poseidon2::hash2`), which is cheaper and is what to use for a new tree.
It also has appends and indexed trees.

## API

| Item | What it does |
|---|---|
| `merkle_verify::<DEPTH>(leaf, siblings, index_bits, root)` | Assert `leaf` is in the tree with this `root`, at the position `index_bits`. |
| `merkle_root::<DEPTH>(leaf, siblings, index_bits)` | Fold the path and return the computed root, without checking it. |
| `cond_swap(bit, a, b)` | `bit ? (b, a) : (a, b)`, with `bit` constrained to 0 or 1. Not in the prelude. |
| `poseidon2::merkle_verify`, `poseidon2::merkle_root` | The same, with Poseidon2 nodes. |
| `poseidon2::merkle_append::<DEPTH>(old_root, empty_leaf, leaf, siblings, index_bits)` | Assert the slot at `index_bits` holds `empty_leaf` under `old_root`, and return the root with `leaf` written there. |
| `poseidon2::IndexedLeaf` | An indexed tree's leaf: `value`, `next_index`, `next_value`. `hash()` is what the tree holds. |
| `poseidon2::indexed_non_membership::<DEPTH, BITS>(x, low, siblings, index_bits, root)` | Assert no leaf of the indexed tree has the value `x`. |
| `poseidon2::indexed_insert::<DEPTH, BITS>(old_root, x, low, low_siblings, low_index_bits, new_siblings, new_index_bits)` | Assert `x` is absent, insert it, and return the new root. |
| `tree::Tree<DEPTH>` | A tree on the host, filled from the left: `poseidon2(empty_leaf)` or `poseidon(empty_leaf)`, then `push`, `extend`, `set`, `root`, `path(index)`, `empty_subtrees()`. |
| `tree::IndexedTree<DEPTH>` | An indexed tree on the host: `insert(x)` gives an `indexed_insert` witness, `non_membership(x)` an `indexed_non_membership` one. |

Each index bit is constrained to 0 or 1 inside the gadget, so a prover can't pass
some other value to steer the path. The tree must be built with the same hash:
`tree::Tree::poseidon2` for `poseidon2`, `tree::Tree::poseidon` for the crate
root.

## Appending

A program that keeps a tree's root, but doesn't hash, can grow the tree with
proofs: each proof shows the new root is the old tree with one leaf written in
an empty slot.

```rust
use xark_merkle::poseidon2::prelude::*;

/// ASCII `xarkzero`: no real leaf hashes to it, so an empty slot can't be claimed.
pub const EMPTY: u64 = 0x7861_726b_7a65_726f;

#[circuit]
pub fn deposit(
    siblings: Private<[Field; 20]>,
    leaf: Public<Field>,
    index: Public<u32>,
    old_root: Public<Field>,
    new_root: Public<Field>,
) {
    let bits = Field::from(index).to_bits::<20>();
    require_eq(merkle_append(old_root, Field::from(EMPTY), leaf, siblings, bits), new_root);
}
```

One path proves both roots: the empty leaf under `old_root` and the new leaf
under `new_root` share every sibling. The circuit checks that the slot was
empty, not that it is the next one. The program does that, here by checking
`index` against the next free slot it keeps.

On the host, `tree.path(tree.len())` is the next free slot's path:

```rust
use xark::Field;
use xark_merkle::tree::Tree;

let mut tree = Tree::<20>::poseidon2(Field::from(0x7861_726b_7a65_726fu64));
let old_root = tree.root();
let path = tree.path(tree.len());
tree.push(leaf);
// prove `deposit(path.siblings, leaf, path.index as u32, old_root, tree.root())`
```

## Non-membership: indexed trees

An indexed tree (Aztec's nullifier tree) keeps its values as a linked list
sorted by value. Each leaf is `(value, next_index, next_value)`, the next larger
value and its slot, with `next_value = 0` on the largest leaf. A value `x` is
absent when its *low leaf*, the one with the largest value below `x`, has
`value < x < next_value`, or `value < x` with `next_value = 0`.
`indexed_insert` proves exactly that, rewrites the low leaf to point at `x`, and
appends `(x, low.next_index, low.next_value)` in an empty slot. A tree changed
only by `indexed_insert`, starting from `IndexedTree::new()` (the head `(0, 0, 0)`
in slot 0), is always a sorted list, so a non-membership proof against its root
is sound.

```rust
use xark_merkle::tree::IndexedTree;

let mut tree = IndexedTree::<20>::new();
let ins = tree.insert(nullifier)?; // Err(InsertError::Present) if it's there
// ins.old_root, ins.new_root, ins.low, ins.low_path, ins.new_path:
// the arguments of `indexed_insert`
```

[`examples/nullifier_tree`](https://github.com/blueshift-gg/xark/tree/master/examples/nullifier_tree)
spends nullifiers this way.

**Value range.** The comparisons are on `BITS`-bit integers, with `BITS ≤ 252`.
Both sides of each comparison are range-checked below `2^BITS`, so
`a − b + 2^BITS` can't wrap the field. A value at or above `2^BITS` can't be
proven absent or inserted; it is never compared wrong. `0` is the head's value,
so it is always present. A field element is up to about `2^253.6`, so a hash fits
252 bits only about a third of the time. To use a hash as a value, reduce it
first, for example by taking its low 252 bits from `to_bits_canonical()` (353
rows). Use a narrower `BITS` when the values are smaller, such as 64 for `u64`
values: it's cheaper.

Empty slots hold `0`. A leaf is the Poseidon2 sponge over three fields, with its
capacity seeded with 3, and a node is the compression with capacity 0. So no leaf
is an empty slot or a node without a hash collision or preimage.

## Cost

R1CS rows after minimization, at depth 20 with 252-bit values:

| Circuit | Constraints |
|---|---|
| `merkle_verify` (Poseidon2) | 4,840 |
| `merkle_append` | 9,660 |
| `indexed_non_membership` | 6,585 |
| `indexed_insert` | 22,025 |

- Membership in a depth-4 Poseidon tree: 957 constraints
  ([`examples/merkle`](https://github.com/blueshift-gg/xark/tree/master/examples/merkle)).

Each level costs a Poseidon2 `hash2` (240 rows) and two rows for `cond_swap`.
When a second leaf folds up the same path (an append, the rewritten low leaf),
its level costs a hash and one row, since the bit is already proven boolean. The
indexed tree adds the leaf hashes (a two-permutation sponge each) and the 252-bit
comparisons.

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
