# xark-solana-verifier

Solana on-chain Groth16 BN254 verifier program. Consumes the wire format
produced by xark's `groth16-backend::solana` encoding library and evaluates
the standard Groth16 pairing check via Solana's `alt_bn128` syscalls.

## Building the on-chain program

```
cargo build-sbf -p xark-solana-verifier
```

The SBF toolchain is **not** exercised by `cargo test --workspace`; install
it via `solana-install` if you want to produce a deployable `.so` artifact.
CI integration arrives in roadmap step **E.2.d**.

The crate also builds as an ordinary host library
(`cargo build -p xark-solana-verifier`) so the `verify_groth16` core can be
exercised off-chain.

## Wire format

Instruction data layout, all big-endian, all `alt_bn128`-compatible:

```
num_inputs   : u32 BE                                          (4 B)
vk_bytes     : alpha    (G1, 64 B)
             | beta     (G2, 128 B)
             | gamma    (G2, 128 B)
             | delta    (G2, 128 B)
             | ic_count (u32 BE, 4 B)
             | ic_count * G1 (64 B each)
proof_bytes  : A (G1, 64 B) | B (G2, 128 B) | C (G1, 64 B)     (256 B)
public_inputs: num_inputs * Fr (32 B BE each)
```

G2 components are laid out as `(c1, c0)` — imaginary part first — to match
the Ethereum / Solana BN254 precompile convention. See
`crates/groth16-backend/src/solana.rs` for the canonical encoder.

`ic_count` MUST equal `num_inputs + 1` (one IC entry per public input plus
the constant term `ic[0]`).

## Pre-negation policy

The exporter (xark CLI, roadmap step E.2.c) pre-negates the Groth16 `A`
point so the on-chain code does not need to perform a modular subtraction
against the BN254 base-field prime. The bytes for `A` in `proof_bytes` are
therefore **already** `-A` on G1, ready to feed straight into the pairing.

This matches the convention used by the EVM verifier
(`groth16-backend::evm`), where the Solidity contract negates `A` itself
because it has cheap access to `Q - y mod Q`.

## Testing

Off-chain unit tests live under `src/verifier.rs` `#[cfg(test)]`. They
exercise the `verify_groth16_with::<B>` core by parametrising over a
[`Bn128Backend`] trait. Two backend implementations exist:

* `SolanaBackend` — calls the `sol_alt_bn128_*` syscalls. Used by the
  deployed program.
* `ArkBackend` (test-only) — implements the same trait using Arkworks
  BN254 primitives. Lets tests run as plain host-side `cargo test` without
  any Solana runtime.

Round-trip tests use the committed fixtures under
`tests/fixtures/groth16/arithmetic_square/`.

```
cargo test -p xark-solana-verifier
```

## Roadmap

This crate implements roadmap step **E.2.b**. The remaining Solana work:

* **E.2.c — Exporter and CLI.** A `xark export solana` command that writes
  `verifying_key.solana.bin`, `proof.solana.bin`, `public_inputs.solana.bin`
  (with `A` pre-negated) plus a TypeScript client snippet.
* **E.2.d — End-to-end harness.** A workspace-level test that compiles this
  crate with `cargo build-sbf` and runs the program inside
  `solana-program-test`, then a CI workflow that runs it on PRs touching
  either this crate or the encoding library.
