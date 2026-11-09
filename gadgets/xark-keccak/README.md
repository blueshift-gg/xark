# xark-keccak

[![crates.io](https://img.shields.io/crates/v/xark-keccak.svg)](https://crates.io/crates/xark-keccak)
[![docs.rs](https://img.shields.io/docsrs/xark-keccak)](https://docs.rs/xark-keccak)

Keccak-256 for xark circuits, the Ethereum `keccak256` flavour. Use it to prove
facts about Ethereum-style hashes. Its output matches `sha3::Keccak256`.

```toml
[dependencies]
xark = "0.3"
xark-keccak = "0.3"
```

## Use

```rust
use xark_keccak::prelude::*;

#[circuit]
pub fn keccak256(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Qualified call: the entry fn shares the gadget's name, so name it by path.
    require_eq(xark_keccak::keccak256(msg), digest);
}
```

The digest is a `Hash` (2 public inputs); on the host you pass a plain
`[u8; 32]`. See
[`examples/keccak256`](https://github.com/blueshift-gg/xark/tree/master/examples/keccak256).

## API

| Item | What it does |
|---|---|
| `keccak256::<N_BYTES>(msg)` | Keccak-256 of `N_BYTES` bytes, with Ethereum's `0x01` padding. Each byte is range-checked. Returns 4 lanes of 64 little-endian bits. |
| `keccak256_block(block)` | Keccak-256 of one rate block (17 lanes) you have already padded. |
| `keccak_f(state)` | The Keccak-f[1600] permutation: 24 rounds on 25 lanes. |
| `Hash` | Re-exported from `xark-hash`: a 256-bit digest as 2 field elements. |

This is Keccak-256 as Ethereum uses it, not NIST SHA3-256 (which pads with
`0x06`). `keccak_f` and `keccak256_block` expect every input bit to already be
constrained to 0 or 1; `keccak256` does that for you.

## Cost

- Keccak-256 of a 3-byte message, checked against a public `Hash`: 89,375
  constraints ([`examples/keccak256`](https://github.com/blueshift-gg/xark/tree/master/examples/keccak256)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
