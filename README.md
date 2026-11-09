# xark

[![CI](https://github.com/blueshift-gg/xark/actions/workflows/ci.yml/badge.svg)](https://github.com/blueshift-gg/xark/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/xark-cli.svg?label=xark-cli)](https://crates.io/crates/xark-cli)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

**Zero-knowledge circuits in plain Rust, verified on Solana.** · [xark.gg](https://xark.gg)

You write a circuit as an ordinary Rust function. xark compiles it with your
stable `rustc`, proves it with Groth16, and gives you a verifier for your Solana
program. Proofs are 256 bytes.

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

## Why xark

- **It's just Rust.** No circuit DSL to learn. You get stable `rustc`, your editor,
  `cargo test`, and crates. A gadget is a Cargo dependency.
- **Errors point at your code.** Inputs that break the circuit are reported as the
  line that fails, in tests, at the command line and in the TypeScript client.
- **Small proofs, cheap verification.** A Groth16 proof over BN254 is 256 bytes and
  verifies on Solana in about 77k compute units.
- **Typed clients.** `xark client` turns your circuit's inputs into a typed
  TypeScript client that proves and verifies in Node or the browser.
- **The hard gadgets are done.** Poseidon, Poseidon2, SHA-256, Keccak, BLAKE2s,
  BLAKE3, Merkle proofs, AES, and ECDSA (secp256k1, P-256) and Ed25519 signature
  verification.

## Quickstart

You need Rust 1.89 or newer.

**1. Install the CLI**, and check your setup:

```sh
cargo install xark-cli
xark doctor
```

**2. Create a circuit.** `xark init` writes a crate with the square-root circuit
above and two tests:

```sh
xark init my-circuit
```

**3. Test it.** `xark test` builds the circuit, then runs the crate's tests:

```console
$ xark test my-circuit
xark building circuit `my-circuit`
xark 2 vars, 1 constraints, 0 witness-gen ops
xark circuit digest 75e3ce529473dfaa2f89a85a0d588228
...
test tests::accepts_valid ... ok
test tests::rejects_invalid ... ok
```

**4. Prove.** The first proof also makes the key, from your machine's randomness:

```console
$ xark prove my-circuit --inputs '{"secret": 3, "result": 9}'
...
✅ Proof produced and self-checked (1 public input(s)).
```

Try inputs that don't satisfy the circuit, and xark shows you where:

```console
$ xark prove my-circuit --inputs '{"secret": 3, "result": 10}'
error: witness does not satisfy the circuit

  src/lib.rs:6:16  require_eq(secret * secret, result);
```

**5. Verify**, then **export** the Solana verifier:

```console
$ xark verify my-circuit
✅ Proof verified

$ xark export my-circuit
...
Key: a single-party setup from OS randomness: sound unless whoever ran `xark setup` kept that randomness (xark doesn't). `xark ceremony` spreads that trust.
✅ On-chain verifier crate ready (verifying key embedded).
```

`my-circuit/my-circuit-verifier/` is a crate your Solana program depends on:

```rust
let proof = my_circuit_verifier::Proof::from_le_bytes(proof_bytes);
let public_inputs: [[u8; 32]; 1] = [/* from your program's state */];
if !my_circuit_verifier::verify(&proof, &public_inputs) {
    return Err(ProgramError::InvalidArgument);
}
```

A key you make yourself is a single-party trusted setup: whoever relies on your
verifier trusts that you didn't keep its randomness. For a key no one party has to
be trusted for, run a multi-party ceremony: see [Trusted setup](docs/trusted-setup.md).
The verifier crate's `SETUP` constant says which kind of key it embeds.

## Learn more

**Writing circuits**
- [Testing a circuit](docs/testing.md): the generated validator, failing lines,
  running circuit code on the host
- [Inputs](docs/inputs.md): `#[input]` structs, and the built-in types (dates,
  timestamps, text, enums and sets)
- [What Rust compiles](docs/subset.md): the supported subset, and what's rejected
- [Editor diagnostics](docs/editor.md): circuit errors inline in rust-analyzer

**Using proofs**
- [TypeScript clients](docs/typescript.md): typed provers and verifiers for Node
  and the browser
- [`@blueshift-gg/xark`](crates/wasm/README.md): the WebAssembly prover and
  verifier underneath
- [`xark-verifier`](crates/verifier/README.md): the on-chain verifier

**Going to production**
- [Trusted setup](docs/trusted-setup.md): a multi-party ceremony instead of a single-party key
- [Reproducible builds](docs/reproducible-build.md) of the on-chain verifier
- [Security](docs/security.md) and [audit status](docs/audit-status.md)

**How it works**
- [Architecture](docs/architecture.md): Rust → wasm → constraints → Groth16 →
  Solana
- [Toolchains](docs/toolchain.md): why a circuit is the same under every stable
  `rustc`

Every command has `--help`, and `xark <command>` defaults to the crate in the
current directory.

## Gadgets

Each gadget is its own crate under [`gadgets/`](gadgets). Add the ones you use:

```toml
[dependencies]
xark = "0.3"
xark-poseidon2 = "0.3"
```

| Crate | What it does |
|---|---|
| `xark-poseidon`, `xark-poseidon2` | Poseidon and Poseidon2 hashes over BN254, the cheapest in a circuit |
| `xark-sha256`, `xark-keccak`, `xark-blake2s`, `xark-blake3` | Standard hashes, matching their native implementations |
| `xark-mimc`, `xark-pedersen` | MiMC and Pedersen hashes |
| `xark-merkle` | Merkle-tree membership |
| `xark-aes` | AES-128/256 block cipher, CTR and GCM |
| `xark-secp256k1`, `xark-secp256r1` | ECDSA signature verification on secp256k1 and P-256 |
| `xark-ed25519` | Ed25519 (EdDSA) signature verification |
| `xark-grumpkin` | The Grumpkin curve, for recursion and folding |
| `xark-bits`, `xark-bignum`, `xark-curve`, `xark-hash` | Building blocks for writing your own gadgets |

## Examples

[`examples/`](examples) has 72 runnable circuits, from `cube` to `zkyc` (a private
credential check against a public policy), with the gadgets above at work. Test
any of them with `xark test examples/<name>`.

## Status

> **Experimental, and not yet audited.** Don't deploy a key made in dev mode, and
> don't rely on xark in production before an independent audit. See
> [audit status](docs/audit-status.md).

## Contributing

```sh
cargo xtask ci                  # every CI check, side by side
cargo test --workspace --release
cargo xtask digests --check     # every example's circuit is unchanged
```

`crates/lang`'s test suites are heavy, so CI runs them separately:
`cargo test --release -p xark`. [Toolchains](docs/toolchain.md) explains why a
change that alters any circuit must update the digests.

## License

[MIT](LICENSE)
