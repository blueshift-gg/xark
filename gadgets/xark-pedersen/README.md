# xark-pedersen

[![crates.io](https://img.shields.io/crates/v/xark-pedersen.svg)](https://crates.io/crates/xark-pedersen)
[![docs.rs](https://img.shields.io/docsrs/xark-pedersen)](https://docs.rs/xark-pedersen)

A Pedersen hash on the Grumpkin curve for xark circuits: `H = m₀·G₀ + m₁·G₁` for
two 128-bit scalars. Grumpkin's coordinates are BN254 field elements, the
circuit's own field, so the curve arithmetic needs no non-native limbs.

```toml
[dependencies]
xark = "0.3"
xark-pedersen = "0.3"
```

## Use

```rust
use xark_pedersen::prelude::*;

#[circuit]
pub fn pedersen(m0: Private<Field>, m1: Private<Field>, hx: Public<Field>, hy: Public<Field>) {
    let h = pedersen_hash([m0, m1]);
    require_eq(h[0], hx);
    require_eq(h[1], hy);
}
```

See [`examples/pedersen`](https://github.com/blueshift-gg/xark/tree/master/examples/pedersen).

## API

| Item | What it does |
|---|---|
| `pedersen_hash(inputs)` | `m₀·G₀ + m₁·G₁` for `mᵢ` in `[1, 2^128)`, returned as the affine point `[x, y]`. |

## Inputs it rejects

Each `mᵢ` must be in `[1, 2^128)`. Zero, larger values, and inputs where
`m₀·G₀ = ±m₁·G₁` leave the circuit unsatisfiable: they are rejected, never
forged.

The generators `Gᵢ` are derived by try-and-increment from
`SHA256("xark-pedersen:generator:i")`, so no discrete-log relation between them
is known. [`examples/grumpkin_reference`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin_reference)
derives the window tables from them with `ark-grumpkin`.

## Cost

- The hash of two private scalars, checked against a public point: 774
  constraints ([`examples/pedersen`](https://github.com/blueshift-gg/xark/tree/master/examples/pedersen)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
