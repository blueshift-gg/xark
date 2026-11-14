# xark-poseidon2

[![crates.io](https://img.shields.io/crates/v/xark-poseidon2.svg)](https://crates.io/crates/xark-poseidon2)
[![docs.rs](https://img.shields.io/docsrs/xark-poseidon2)](https://docs.rs/xark-poseidon2)

The Poseidon2 hash over BN254 for xark circuits: width 3, `x^5` S-box, 8 full and
56 partial rounds, with the Horizen Labs constants. Use it for commitments and
anything else you hash in a circuit and also compute outside it: the crate has a
native version of every function.

```toml
[dependencies]
xark = "0.4"
xark-poseidon2 = "0.4"
```

## Use

```rust
use xark_poseidon2::prelude::*;

#[circuit]
pub fn poseidon2_sponge(
    a: Private<Field>,
    b: Private<Field>,
    c: Private<Field>,
    d: Private<Field>,
    e: Private<Field>,
    out: Public<Field>,
) {
    require_eq(hash::<5>([a, b, c, d, e]), out);
}
```

See [`examples/poseidon2_sponge`](https://github.com/blueshift-gg/xark/tree/master/examples/poseidon2_sponge),
and [`examples/zkyc`](https://github.com/blueshift-gg/xark/tree/master/examples/zkyc)
for a commitment to a private credential.

## API

| Item | What it does |
|---|---|
| `hash2(a, b)` | 2-to-1 compression: `poseidon2_perm([a, b, 0])[0]`. |
| `hash::<N>(inputs)` | Sponge hash of `N` field elements (rate 2, capacity 1). The capacity is seeded with `N`, so `hash([a]) != hash([a, 0])`. |
| `commit::<N>(inputs)` | A commitment: `hash`'s sponge in domain 1. Include a random element to make it hiding. |
| `nullifier::<N>(inputs)` | A nullifier (say of a secret key and a note's commitment): `hash`'s sponge in domain 2. |
| `challenge::<N, BITS>(transcript)` | A Fiat–Shamir challenge: the low `BITS` canonical bits of `hash(transcript)`. |
| `poseidon2_perm(state)` | The Poseidon2 permutation on a width-3 state. |
| `native` | The same functions on the host, over `ark_bn254::Fr`, plus `hash_slice`, `commit_slice` and `nullifier_slice` for a length known only at run time. |

## Domains

Each function starts the sponge's capacity lane from its own value, so their
outputs are independent functions of their inputs (a sponge's capacity is its
domain separator; Bertoni et al., "On the indifferentiability of the sponge
construction", Eurocrypt 2008):

| Function | Capacity starts at |
|---|---|
| `hash2` (and so every Merkle node built on it) | `0` |
| `hash::<N>` | `N` |
| `commit::<N>` | `2^64 · 1 + N` |
| `nullifier::<N>` | `2^64 · 2 + N` |

No two are equal for any lengths (`N < 2^64`), so a commitment can't be passed off
as a nullifier or a node, and a nullifier reveals nothing about the commitment
made of the same values, short of a Poseidon2 collision. The length is in the
domain too: `commit([a])` and `commit([a, 0])` are unrelated. Domain 3 is kept
for authenticated encryption, which a later release may add.

`poseidon2_ref.py` has every function written from its definition;
`tests/modes.rs` checks the circuit
and `native` against its vectors.

## Outside the circuit

`xark_poseidon2::native` runs the same permutation on the host, over
`ark_bn254::Fr`, so a wallet or test can compute the digest a circuit commits to
without a second Poseidon2 implementation:

```rust
use xark_poseidon2::native::{hash, Fr};

let commitment: Fr = hash([Fr::from(7u64), Fr::from(11u64)]);
```

`poseidon2_perm`, `hash2` and `hash` all have native versions. Both sides are
one generic implementation (constants, rounds, S-box and linear layers), and the
tests check them against each other and the reference vectors.

## Cost

- The permutation of 3 private elements, checked against 3 public outputs: 243
  constraints ([`examples/poseidon2`](https://github.com/blueshift-gg/xark/tree/master/examples/poseidon2)).
- `hash::<5>`, checked against a public output: 721 constraints
  ([`examples/poseidon2_sponge`](https://github.com/blueshift-gg/xark/tree/master/examples/poseidon2_sponge)).
- `commit::<N>`, `nullifier::<N>` and `hash::<N>` cost `⌈N/2⌉` permutations (240
  rows each).
- `challenge::<N, 128>`: `hash::<N>` and 353 rows for the canonical
  decomposition (`challenge::<14, 128>`, its bits recomposed against a public
  value: 2035 constraints).

## In a TypeScript client

A circuit's `#[input] impl` methods run in its generated client, so a method that
calls `commit` or `nullifier` (`Note::commitment`, say) computes the same value in
TypeScript. `@blueshift-gg/xark` also has them directly: a session's
`commit(fields)` and `nullifier(fields)`.

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
