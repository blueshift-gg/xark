# xark

[![crates.io](https://img.shields.io/crates/v/xark.svg)](https://crates.io/crates/xark)
[![docs.rs](https://img.shields.io/docsrs/xark)](https://docs.rs/xark)

The language for [xark](https://github.com/blueshift-gg/xark) circuits: write a
zero-knowledge circuit as an ordinary Rust function, prove it with Groth16, and
verify it on Solana.

```rust
use xark::prelude::*;

/// I know a square root of `result`, and I won't say what it is.
#[circuit]
pub fn square_root(secret: Private<Field>, result: Public<Field>) {
    require_eq(secret * secret, result);
}

#[test]
fn only_a_square_root_proves() {
    square_root(3, 9).unwrap();
    assert!(square_root(3, 10).is_err());
}
```

A circuit crate depends on `xark` alone. You build and prove it with the
[`xark` CLI](https://crates.io/crates/xark-cli):

```sh
cargo install xark-cli
xark init my-circuit      # a crate like the one above, with its tests
xark test my-circuit      # build the circuit, then run the tests
```

## What's in the prelude

`use xark::prelude::*` brings in:

| Item | What it is |
|---|---|
| `#[circuit]` | Marks the circuit's entry function, and generates a validator of the same name for tests and host code |
| `Field` | An element of the BN254 scalar field: `+ - * /`, `.pow(n)`, comparisons, `.to_bits::<N>()` |
| `Private<T>`, `Public<T>` | An input the prover keeps secret, or one the verifier sees |
| `require`, `require_eq`, `require_ne`, `require_lt`, `require_le`, `require_gt`, `require_ge` | Constraints: the proof exists only if they hold |
| `bind` | Binds a public input that no constraint uses, such as a recipient a proof is for |
| `#[input]`, `Input` | Inputs as structs and enums, packed into as few field elements as they fit |
| `Days`, `Time`, `Timestamp`, `Text`, `Choice`, `Bitfield`, `Country` | Everyday input types for credential-style circuits |

`u8`–`u128`, `i8`–`i128` and `bool` inputs work as well, range-checked to their
width.

Circuit code also runs as plain Rust on the host, so tests and services call the
same helpers the circuit does. After `xark build`, `xark::prover` loads the built
circuit to check and prove inputs from Rust.

## Learn more

- [Quickstart](https://github.com/blueshift-gg/xark#quickstart): from `xark init` to a Solana verifier
- [Testing a circuit](https://github.com/blueshift-gg/xark/blob/master/docs/testing.md)
- [Inputs](https://github.com/blueshift-gg/xark/blob/master/docs/inputs.md)
- [What Rust compiles](https://github.com/blueshift-gg/xark/blob/master/docs/subset.md)
- [Gadgets](https://github.com/blueshift-gg/xark#gadgets): hashes, Merkle proofs and signatures as crates

> **Experimental, and not yet audited.** See
> [audit status](https://github.com/blueshift-gg/xark/blob/master/docs/audit-status.md).
