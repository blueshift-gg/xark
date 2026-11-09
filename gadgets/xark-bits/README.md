# xark-bits

[![crates.io](https://img.shields.io/crates/v/xark-bits.svg)](https://crates.io/crates/xark-bits)
[![docs.rs](https://img.shields.io/docsrs/xark-bits)](https://docs.rs/xark-bits)

Bit- and word-level building blocks for writing xark gadgets: 32- and 64-bit
words as arrays of bit `Field`s, with bitwise operations, rotations and modular
addition. `xark-sha256`, `xark-keccak`, `xark-blake2s` and `xark-blake3` are
built on it. If you only need a hash, use those crates instead.

```toml
[dependencies]
xark = "0.3"
xark-bits = "0.3"
```

## Use

A word is a `[Field; 32]` (or `[Field; 64]`) of little-endian bits. Get one with
`Field::to_bits`, which also range-checks the value, and turn it back with
`Field::from_bits`:

```rust
use xark::{circuit, require_eq, Field, Private, Public};
use xark_bits::{add32, and32, rotr32, xor32};

#[circuit]
pub fn word_ops(a: Private<Field>, b: Private<Field>, out: Public<Field>) {
    let ba = a.to_bits::<32>();
    let bb = b.to_bits::<32>();
    let mixed = add32(rotr32(xor32(ba, bb), 7), and32(ba, bb));
    require_eq(Field::from_bits::<32>(mixed), out);
}
```

See [`examples/word_ops`](https://github.com/blueshift-gg/xark/tree/master/examples/word_ops)
and [`examples/bitwise_basic`](https://github.com/blueshift-gg/xark/tree/master/examples/bitwise_basic).

## What's in it

| Item | What it does |
|---|---|
| `and32`, `or32`, `xor32`, `not32` | Bitwise operations on 32-bit words. |
| `and64`, `xor64`, `not64` | The same on 64-bit words. |
| `rotr32`, `shr32`, `rotl64`, `rotr64` | Rotations and shifts. Rewiring only: no constraints. |
| `add32(a, b)`, `add3(a, b, c)` | Addition mod `2^32` of two or three words. |
| `reduce::<N>(sum)` | The low 32 bits of a field sum below `2^N`, in `N` rows. |
| `xor3`, `maj3`, `chi`, `ch` | One-row bit functions: 3-input XOR, majority, Keccak's χ, SHA-256's choice. |
| `xor3_32`, `xor3_64` | `xor3` bit by bit on a word. |
| `to_bits64`, `from_bits64` | Split a field element into 64 constrained bits, and recompose. |
| `read_n`, `sha256_iv` | Copy word `t` out of a word array; the SHA-256 IV (also BLAKE2s/BLAKE3's). |

Single-bit operations (booleanity, `to_bits`/`from_bits`, AND/OR/XOR/NOT on one
bit) are methods on `xark::Field`, not in this crate.

The bit functions assume their inputs are bits; `chi`, for one, leaves its
output free on a non-bit input. Feed them words from `to_bits` or from other
gadgets in this crate.

## Cost

- `a & b` and `a ^ b` on two 32-bit values: 128 constraints
  ([`examples/bitwise_basic`](https://github.com/blueshift-gg/xark/tree/master/examples/bitwise_basic)).
- The `word_ops` circuit above: 161 constraints
  ([`examples/word_ops`](https://github.com/blueshift-gg/xark/tree/master/examples/word_ops)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
