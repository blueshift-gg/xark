# xark-blake2s

[![crates.io](https://img.shields.io/crates/v/xark-blake2s.svg)](https://crates.io/crates/xark-blake2s)
[![docs.rs](https://img.shields.io/docsrs/xark-blake2s)](https://docs.rs/xark-blake2s)

BLAKE2s-256 for xark circuits: unkeyed, with a 32-byte digest. Its output
matches the `blake2` crate's `Blake2s256`.

```toml
[dependencies]
xark = "0.3"
xark-blake2s = "0.3"
```

## Use

```rust
use xark_blake2s::prelude::*;

#[circuit]
pub fn blake2s(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Entry fn shares the gadget's name, so call it by path.
    require_eq(Blake256(xark_blake2s::blake2s(msg)), digest);
}
```

Wrap the output in `Blake256` before comparing it with a `Hash`: BLAKE2s writes
its words little-endian, and `Blake256` selects that byte order. See
[`examples/blake2s`](https://github.com/blueshift-gg/xark/tree/master/examples/blake2s).

## API

| Item | What it does |
|---|---|
| `blake2s::<N_BYTES>(msg)` | Unkeyed BLAKE2s-256 of `N_BYTES` bytes. Each byte is range-checked. Returns 8 words of 32 little-endian bits. |
| `blake2s_hash_one_block::<LEN>(input_words)` | Hash a single message of `LEN <= 64` bytes, given as 16 words. The bytes past `LEN` must be zero. |
| `compress(...)` | The BLAKE2s compression function, with counter and final-block flag. |
| `Blake256` | Wrapper that compares a BLAKE output against a `Hash` in little-endian word order. |
| `Hash` | Re-exported from `xark-hash`: a 256-bit digest as 2 field elements. |

Keyed hashing and other digest lengths are not supported.

## Cost

- BLAKE2s of a 3-byte message, checked against a public `Hash`: 20,066
  constraints ([`examples/blake2s`](https://github.com/blueshift-gg/xark/tree/master/examples/blake2s)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
