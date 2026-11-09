# xark-sha256

[![crates.io](https://img.shields.io/crates/v/xark-sha256.svg)](https://crates.io/crates/xark-sha256)
[![docs.rs](https://img.shields.io/docsrs/xark-sha256)](https://docs.rs/xark-sha256)

SHA-256 for xark circuits. Use it to prove you know a message with a given
SHA-256 digest, or to hash bytes inside a larger circuit. Its output matches the
`sha2` crate.

```toml
[dependencies]
xark = "0.3"
xark-sha256 = "0.3"
```

## Use

```rust
use xark_sha256::prelude::*;

#[circuit]
pub fn sha256(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    // Qualified: the entry fn shares the gadget's name.
    require_eq(xark_sha256::sha256(msg), digest);
}
```

The digest is a `Hash`: 256 bits packed into two field elements, so it costs 2
public inputs. On the host you pass a plain `[u8; 32]`. See
[`examples/sha256`](https://github.com/blueshift-gg/xark/tree/master/examples/sha256).

To compare against a digest fixed at compile time, use `Digest` instead, as in
[`examples/sha256_consume`](https://github.com/blueshift-gg/xark/tree/master/examples/sha256_consume):

```rust
let expected: Digest = SHA256_ABC.into();
Digest::from(sha256(msg)).require_eq(expected);
```

## API

| Item | What it does |
|---|---|
| `sha256::<N_BYTES>(msg)` | SHA-256 of `N_BYTES` bytes, with padding and multi-block chaining. Each byte is range-checked to `0..=255`. Returns 8 words of 32 little-endian bits. |
| `sha256_block(w)` | One compression from the standard IV, on 16 message words you have already laid out. No padding. |
| `compress(h_in, w)` | The compression function, from any 8-word chaining value. |
| `h0()` | The SHA-256 initial hash value, as field constants. |
| `Hash`, `Digest` | Re-exported from `xark-hash`: a 2-element packed digest, and a 256-bit one. |

The message length is a compile-time constant: a circuit has a fixed size.

## Cost

- SHA-256 of a 3-byte message, checked against a public `Hash`: 16,472
  constraints ([`examples/sha256`](https://github.com/blueshift-gg/xark/tree/master/examples/sha256)).
- The same against a constant `Digest`: 16,216 constraints
  ([`examples/sha256_consume`](https://github.com/blueshift-gg/xark/tree/master/examples/sha256_consume)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
