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
 `--artifact` and `--out` become optional when `xark` can infer them from a
 nearby single-package `Nargo.toml`; `--insecure-dev-mode` generates toy keys
 for local iteration, and real deployments should use the ceremony flow below.
- **`xark prove`** — produce a proof from an artifact + `nargo`-solved witness.
 `--artifact`, `--witness`, `--proving-key`, and `--out` become optional under
 the same `Nargo.toml` inference rule. Self-verifies before writing the proof.
- **`xark verify`** — verify a proof against a verifying key and public inputs.
 `--verifying-key`, `--proof`, and `--public-inputs` become optional when
 inference succeeds.
- **`xark export`** — emit a **self-contained Rust crate** for the circuit: it
 bakes the verifying key into a typed `Verifier<N>` and exposes
 `verify(...)` / `verify_instruction_data(...)`. Depend on it from your Solana
 program; re-run `xark export` when the circuit changes and that generated
 crate is the only thing that updates.
- **`xark inspect`** — inspect a Noir artifact; `--artifact` becomes optional
 when inference succeeds.
- **`xark write-vk`** — write the verifying key in the Solana LE wire format.
- **`xark ceremony`** — run a real Groth16 trusted setup: `init` from a snarkjs
 `powersoftau` file, `contribute` (phase-2 MPC), `verify`, and `finalize`. See
 `docs/trusted-setup.md`.

## Pipeline

```
nargo compile # target/<name>.json (ACIR)
nargo execute # target/<name>.gz (witness)
 └─ xark setup   # target/groth16/proving_key.bin + verifying_key.bin
 └─ xark prove   # target/groth16/proof.bin (self-verified)
 └─ xark verify  # off-chain check
 └─ xark export  # on-chain verifier crate for Solana
```

When run from inside a Noir project, `xark` walks upward to find the nearest
`Nargo.toml`, reads `[package].name`, and infers the standard `target/` paths
from it. Explicit flags override inference.

Lowering is handled by [`xark-acir-r1cs`] and proving by [`xark-backend`]; the
exported crate depends on [`xark-verifier`].

[`xark-acir-r1cs`]:../acir-r1cs
[`xark-backend`]:../backend
[`xark-verifier`]:../verifier
