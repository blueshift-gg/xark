# xark-mimc

[![crates.io](https://img.shields.io/crates/v/xark-mimc.svg)](https://crates.io/crates/xark-mimc)
[![docs.rs](https://img.shields.io/docsrs/xark-mimc)](https://docs.rs/xark-mimc)

The MiMC hash over BN254 for xark circuits: MiMC-p/p with exponent 7 and 91
rounds, compatible with circomlib. It is a port of
[`noir-lang/mimc`](https://github.com/noir-lang/mimc), and a test checks it
against Noir's known answer. Use it when you need digests that match a circom or
Noir system already using MiMC.

```toml
[dependencies]
xark = "0.3"
xark-mimc = "0.3"
```

## Use

From the crate's known-answer test (`tests/vec.rs`):

```rust
use xark_mimc::prelude::*;

pub fn circuit(out: Public<Field>) {
    require_eq(
        mimc_bn254([Field::from(12u8), Field::from(45u8), Field::from(78u8), Field::from(41u8)]),
        out,
    );
}
```

`out` must be
`18226366069841799622585958305961373004333097209608110160936134895615261821931`,
the value Noir's test gives for `mimc_bn254([12, 45, 78, 41])`.

## API

| Item | What it does |
|---|---|
| `mimc_bn254::<N>(inputs)` | The multi-input MiMC-BN254 hash (a Feistel / Miyaguchi–Preneel sponge). Matches Noir's `mimc_bn254`. |
| `mimc(x, k)` | The MiMC-p/p permutation keyed by `k`: 91 rounds of `(state + k + C[i])^7`, then a key addition. Matches Noir's `mimc`. |

The round constants are BN254 field elements, so the circuit must use the BN254
field (xark's default).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
