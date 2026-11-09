# xark-poseidon

[![crates.io](https://img.shields.io/crates/v/xark-poseidon.svg)](https://crates.io/crates/xark-poseidon)
[![docs.rs](https://img.shields.io/docsrs/xark-poseidon)](https://docs.rs/xark-poseidon)

The Poseidon hash over BN254 for xark circuits: width 3, `x^5` S-box, 8 full and
56 partial rounds, with the Horizen Labs BN256 constants. Poseidon works on field
elements directly, so it costs a few hundred constraints where a byte hash costs
thousands. `xark-merkle` uses it.

```toml
[dependencies]
xark = "0.3"
xark-poseidon = "0.3"
```

## Use

```rust
use xark_poseidon::prelude::*;

/// Prove knowledge of a Poseidon 2-to-1 preimage: `hash2(a, b) == out`.
#[circuit]
pub fn poseidon(a: Private<Field>, b: Private<Field>, out: Public<Field>) {
    require_eq(hash2(a, b), out);
}
```

See [`examples/poseidon`](https://github.com/blueshift-gg/xark/tree/master/examples/poseidon).
To hash a fixed number of elements, use the sponge, as in
[`examples/poseidon_sponge`](https://github.com/blueshift-gg/xark/tree/master/examples/poseidon_sponge):

```rust
require_eq(hash::<5>([a, b, c, d, e]), out);
```

## API

| Item | What it does |
|---|---|
| `hash2(a, b)` | 2-to-1 compression: `permute([0, a, b])[0]`. |
| `hash::<N>(inputs)` | Sponge hash of `N` field elements (rate 2, capacity 1). The capacity is seeded with `N`, so inputs of different lengths don't collide. |
| `permute(state)` | The Poseidon permutation on a width-3 state. |

Poseidon and Poseidon2 give different digests. Pick one and use the same one
wherever the digest is computed. If you also need the hash outside the circuit,
`xark-poseidon2` ships a native version; this crate does not.

## Cost

- `hash2` of two private elements, checked against a public output: 238
  constraints ([`examples/poseidon`](https://github.com/blueshift-gg/xark/tree/master/examples/poseidon)).
- `hash::<5>`, checked against a public output: 717 constraints
  ([`examples/poseidon_sponge`](https://github.com/blueshift-gg/xark/tree/master/examples/poseidon_sponge)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
