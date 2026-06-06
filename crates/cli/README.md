# xark-cli

The `xark` command-line tool: a Groth16 (BN254) backend for Noir. It takes a
circuit compiled by `nargo`, runs trusted setup, proves, verifies, and exports
a ready-to-use **on-chain Solana verifier** for the circuit.

The crate's binary is named `xark`.

```
cargo install --path crates/cli # or: cargo run -p xark-cli -- <command>
```

## Commands

- **`xark setup`** — Groth16 trusted setup for a compiled ACIR artifact.
 `--insecure-dev-mode` generates toy keys for local iteration; for anything
 real, use the ceremony flow below.
- **`xark prove`** — produce a proof from an artifact + `nargo`-solved witness.
 Self-verifies before writing the proof.
- **`xark verify`** — verify a proof against a verifying key and public inputs.
- **`xark export`** — emit a **self-contained Rust crate** for the circuit: it
 bakes the verifying key into a typed `Verifier<N>` and exposes
 `verify(...)` / `verify_instruction_data(...)`. Depend on it from your Solana
 program; re-run `xark export` when the circuit changes and that generated
 crate is the only thing that updates.
- **`xark inspect`** — dump the contents of a VK / proof / key file.
- **`xark write-vk`** — write the verifying key in the Solana LE wire format.
- **`xark ceremony`** — run a real Groth16 trusted setup: `init` from a snarkjs
 `powersoftau` file, `contribute` (phase-2 MPC), `verify`, and `finalize`. See
 `docs/CEREMONY.md`.

## Pipeline

```
nargo compile # circuit.json (ACIR) + witness
 └─ xark setup # proving_key.bin + verifying_key.bin
 └─ xark prove # proof.bin (self-verified)
 └─ xark verify # off-chain check
 └─ xark export # on-chain verifier crate for Solana
```

Lowering is handled by [`xark-acir-r1cs`] and proving by [`xark-backend`]; the
exported crate depends on [`xark-verifier`].

[`xark-acir-r1cs`]:../acir-r1cs
[`xark-backend`]:../backend
[`xark-verifier`]:../verifier
