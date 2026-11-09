# xark-merkle

[![crates.io](https://img.shields.io/crates/v/xark-merkle.svg)](https://crates.io/crates/xark-merkle)
[![docs.rs](https://img.shields.io/docsrs/xark-merkle)](https://docs.rs/xark-merkle)

Merkle-tree membership for xark circuits: prove a private leaf is in a tree with
a public root, without saying which leaf. Nodes are hashed with Poseidon
(`xark_poseidon::hash2`).

```toml
[dependencies]
xark = "0.3"
xark-merkle = "0.3"
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

## API

| Item | What it does |
|---|---|
| `merkle_verify::<DEPTH>(leaf, siblings, index_bits, root)` | Assert `leaf` is in the tree with this `root`, at the position `index_bits`. |
| `merkle_root::<DEPTH>(leaf, siblings, index_bits)` | Fold the path and return the computed root, without checking it. |
| `cond_swap(bit, a, b)` | `bit ? (b, a) : (a, b)`, with `bit` constrained to 0 or 1. Not in the prelude. |

Each index bit is constrained to 0 or 1 inside the gadget, so a prover can't pass
some other value to steer the path. The tree must be built with the same
Poseidon `hash2(left, right)`.

## Cost

- Membership in a depth-4 tree: 957 constraints
  ([`examples/merkle`](https://github.com/blueshift-gg/xark/tree/master/examples/merkle)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
