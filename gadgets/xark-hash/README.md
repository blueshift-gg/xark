# xark-hash

[![crates.io](https://img.shields.io/crates/v/xark-hash.svg)](https://crates.io/crates/xark-hash)
[![docs.rs](https://img.shields.io/docsrs/xark-hash)](https://docs.rs/xark-hash)

The shared 256-bit digest types for xark hash gadgets. `xark-sha256`,
`xark-keccak`, `xark-blake2s` and `xark-blake3` re-export `Hash` from their
preludes (`xark-sha256` also `Digest`), so circuit authors rarely depend on this
crate directly. Gadget
authors use it to give a new 256-bit hash the same public-input form.

```toml
[dependencies]
xark = "0.3"
xark-hash = "0.3"
```

## Use

`Hash` is the usual public digest, 2 public inputs. From
[`examples/sha256`](https://github.com/blueshift-gg/xark/tree/master/examples/sha256):

```rust
use xark_sha256::prelude::*;

#[circuit]
pub fn sha256(msg: Private<[u8; 3]>, digest: Public<Hash>) {
    require_eq(xark_sha256::sha256(msg), digest);
}
```

On the host, a `Hash` is a plain `[u8; 32]`.

## What's in it

| Item | What it does |
|---|---|
| `Hash` | A 256-bit hash as two field elements, `hi` and `lo` (16 bytes each, big-endian). As `Public<Hash>` it costs 2 public inputs, not 256. |
| `Hash::pack(bits)` | Build a `Hash` from 256 bits in big-endian weight order. Gadget authors use it to add their own output format. |
| `Hash::to_fields()` | The two field elements `[hi, lo]`, to hash or bind them. |
| `Digest` | All 256 bits of a SHA-256 output. Use it to compare against a constant digest baked into the circuit. |
| `Digest::require_eq(other)` | Constrain two digests equal, bit for bit. |

`require_eq` between a raw gadget output and a `Hash` works for SHA-256's output
(`[[Field; 32]; 8]`, big-endian words) and Keccak's (`[[Field; 64]; 4]`,
little-endian lanes). BLAKE outputs use the `Blake256` wrapper from their own
crates.

`Digest` as a public input would be 256 public inputs; use `Hash` for a digest
that changes per proof.

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
