# xark-blake3

[![crates.io](https://img.shields.io/crates/v/xark-blake3.svg)](https://crates.io/crates/xark-blake3)
[![docs.rs](https://img.shields.io/docsrs/xark-blake3)](https://docs.rs/xark-blake3)

BLAKE3 for xark circuits, for messages up to 1024 bytes (one chunk). Its output
matches the `blake3` crate's `hash`.

```toml
[dependencies]
xark = "0.3"
xark-blake3 = "0.3"
```

## Use

```rust
use xark_blake3::prelude::*;

#[circuit]
pub fn blake3(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Entry fn shares the gadget's name, so call it by path.
    require_eq(Blake256(xark_blake3::blake3(msg)), digest);
}
```

Wrap the output in `Blake256` before comparing it with a `Hash`: BLAKE3 writes
its words little-endian, and `Blake256` selects that byte order. See
[`examples/blake3`](https://github.com/blueshift-gg/xark/tree/master/examples/blake3).

## API

| Item | What it does |
|---|---|
| `blake3::<N_BYTES>(msg)` | BLAKE3 root hash of `N_BYTES` bytes (`N_BYTES <= 1024`). Each byte is range-checked. Returns 8 words of 32 little-endian bits. |
| `blake3_hash_one_block::<LEN>(input_words)` | Hash a single message of `LEN <= 64` bytes, given as 16 words, as a one-chunk root. The bytes past `LEN` must be zero. |
| `compress(...)` | The BLAKE3 compression function, with counter, block length and flags. |
| `Blake256` | Wrapper that compares a BLAKE output against a `Hash` in little-endian word order. |
| `Hash` | Re-exported from `xark-hash`: a 256-bit digest as 2 field elements. |

Messages over 1024 bytes (BLAKE3's multi-chunk tree mode) are not supported yet.
Keyed hashing and key derivation are not provided.

## Cost

- BLAKE3 of a 3-byte message, checked against a public `Hash`: 13,780
  constraints ([`examples/blake3`](https://github.com/blueshift-gg/xark/tree/master/examples/blake3)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
