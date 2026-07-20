# xark — write, compile, prove and verify zero-knowledge circuits in Rust

[![CI](https://github.com/blueshift-gg/xark/actions/workflows/ci.yml/badge.svg)](https://github.com/blueshift-gg/xark/actions/workflows/ci.yml)

xark is a single, cohesive tool that takes a circuit written as ordinary Rust
all the way to an on-chain proof. You express the circuit in a small, explicitly
validated Rust subset; xark drives `rustc` to type-check it, extracts its MIR,
lowers that to R1CS, and proves it with Groth16 over BN254 — with a verifier
that runs on Solana. There is no separate circuit DSL and no opaque per-gadget
backend: **gadgets are ordinary Rust libraries** that lower to a small
primitive constraint set, so the backend stays lean and the frontend stays
expressive.

## Installation

xark installs as **two** binaries: `xark` — the CLI, plain **stable** Rust — and
`xark-rustc`, the `rustc_driver` shim `xark build` runs to extract MIR, which needs
a **pinned nightly**. `xark build` invokes `xark-rustc` as a sibling of `xark`, so
install both into the same bin directory (`cargo install` uses `~/.cargo/bin`).

First install the pinned nightly the driver needs:

`rustup toolchain install nightly-2026-05-03 --profile minimal --component rust-src --component rustc-dev --component llvm-tools`

Then install both binaries from GitHub:

```bash
# the rustc-driver shim (pinned nightly)
cargo +nightly-2026-05-03 install --git https://github.com/blueshift-gg/xark xark-rustc
# the CLI (stable Rust)
cargo install --git https://github.com/blueshift-gg/xark xark-cli
```

Only `xark-rustc` touches nightly — you write **stable Rust** in your circuits.

## Two faces: a language *and* a toolchain

### As a language (library)

Write a circuit as a `#![no_std]` Rust function over `Field` values, using the
`xark` prelude. `assert_eq` emits a circuit equality constraint (not a native
`bool`); `Private<T>` / `Public<T>` mark input visibility; `Field` supports
`+ - * ^` (with `^ n` meaning exponentiation).

```rust
#![no_std]
use xark::prelude::*;

/// Prove knowledge of a cube root: `secret^3 == result`.
pub fn circuit(secret: Private<Field>, result: Public<Field>) {
    assert_eq(secret ^ 3, result);
}
```

### As a toolchain (CLI)

```bash
# Scaffold a new circuit crate, pre-wired for rust-analyzer diagnostics.
xark init my-circuit

# Compile a circuit crate: Rust → MIR → xark-IR → R1CS. All xark output
# (artifacts + an isolated cargo target) lives under the crate's target/xark/.
xark build examples/cube
# → writes examples/cube/target/xark/cube/ (circuit.json + r1cs.json)

# Generate Groth16 keys. With no .ptau this produces an INSECURE dev key
# (single-party OsRng); pass --ptau-file (or run `xark ceremony`) for production.
xark setup examples/cube

# Solve the witness from your inputs, then produce AND verify a Groth16 proof.
xark prove examples/cube --input secret=3 --input result=27
# → ✅ Proof produced and self-checked (1 public input).

# Validate a circuit crate WITHOUT emitting artifacts — report subset
# violations as rustc diagnostics with source spans (great for editors / CI).
xark check examples/cube
# → clean; nothing printed
```

## Editor diagnostics (rust-analyzer)

`xark check <crate-dir>` runs the full `rustc` frontend *and* the xark subset
validator, then surfaces every rejection as a **real `rustc` diagnostic with a
source span** (`file:line:col`). With `--message-format=json` it emits the same
JSON stream as `cargo check`, so an editor can show live rejections on save — no
toolchain fork required.

`xark init` writes this wiring for you. To add it to an existing crate, point
`rust-analyzer`'s check command at `xark` via a `rust-analyzer.toml` at the crate
root (or the equivalent `.vscode/settings.json`) — `xark` must be on `PATH`
(`cargo install --path crates/xark-cli` for the stable CLI, plus
`cargo +nightly-2026-05-03 install --path crates/xark-rustc` for the driver into
the same bin dir):

```toml
# rust-analyzer.toml
[check]
overrideCommand = ["xark", "check", ".", "--message-format=json"]
```

```jsonc
// .vscode/settings.json (VS Code equivalent)
{
  "rust-analyzer.check.overrideCommand": ["xark", "check", ".", "--message-format=json"]
}
```

Use an absolute path to the built binary if `xark` is not on `PATH`, and replace
`.` with the crate directory (e.g. `examples/cube`) when the editor is opened
above the circuit crate. A violation then appears inline, e.g.:

```text
error: witness-dependent control flow is not supported
 --> src/lib.rs:7:5
note: branch conditions must be compile-time constants (e.g. loop bounds)
```

## The pipeline

```text
Rust source  →  rustc MIR  →  xark-IR  →  R1CS  →  Groth16 (BN254)  →  Solana verifier
```

The backend never grows a per-gadget opcode to special-case: hashes / curves /
ECDSA / … are plain Rust crates that lower to the same primitive constraints.

## snarkjs compatibility

`xark setup` and `xark prove` emit snarkjs-compatible JSON alongside the
native binary artifacts:

* `snarkjs-verification_key.json` — from `xark setup`
* `snarkjs-proof.json` and `snarkjs-public.json` — from `xark prove`

These can be verified directly with snarkjs:

```bash
snarkjs groth16 verify \
  target/xark/<name>/snarkjs-verification_key.json \
  target/xark/<name>/snarkjs-public.json \
  target/xark/<name>/snarkjs-proof.json
```

This enables verification in JavaScript environments (browser, Node.js, etc.)
and compatibility with the snarkjs/circom ecosystem.

## How it uses MIR

`xark build` runs `cargo build` on your circuit crate with `xark-rustc` (the
`rustc_driver` shim, on a pinned nightly) as the compiler, so every dependency
(the `xark` lib and any gadget crates) is compiled with matching MIR-encoded
rlibs. rustc does the hard work — parse, type-check, borrow-check,
monomorphize — and `xark-rustc` then:

1. finds `pub fn circuit(..)` in the primary crate,
2. reads its signature to recover `Private` / `Public` visibility,
3. extracts its MIR body, with cross-crate gadget calls inlined via
   `-Zalways-encode-mir`,
4. sanitizes and validates the accepted subset (rejecting arbitrary control
   flow, references, aggregates, unknown calls, …),
5. lowers it to xark-IR, then to R1CS, and writes `circuit.json` + `r1cs.json`.

Signalling intrinsics recognised in MIR are named `__xark_*` (`__xark_add`,
`__xark_mul`, `__xark_hint_bit`, …).

## A note on nightly

MIR access has no stable API, so `xark-rustc` uses a **pinned nightly** toolchain
(`rust-toolchain.toml`) internally. That nightly is invisible to circuit authors:
**you write stable Rust**, the `xark` CLI is stable, and only the `xark-rustc`
driver touches nightly.

## Crates and gadgets

* **`xark`** — the language library (`#![no_std]`, stable). Its `prelude` provides
  the marker primitives (`Field`, `assert_eq`, `Private`/`Public`) from its `lang`
  module. The CLI is the separate **`xark-cli`** crate (stable, binary `xark`) and
  the MIR-extraction driver is **`xark-rustc`** (pinned nightly).
* **Backend** — `xark-backend` (Groth16 setup/prove/verify, trusted setup,
  serialization) and `xark-verifier` (the `no_std` on-chain Solana verifier).
  Both are frontend-agnostic.

**Basic building blocks (bits) ship in `xark`.** Specialized building blocks and
gadgets are **separate crates you add only when you need them**: `xark-bignum`
(non-native / foreign-field arithmetic, used by the EC gadgets) and the gadgets
`xark-poseidon`, `xark-poseidon2`, `xark-sha256`, `xark-keccak`, `xark-mimc`,
`xark-blake3`, `xark-blake2s`, `xark-aes`, `xark-pedersen`, `xark-grumpkin`,
`xark-secp256k1`, `xark-secp256r1`, `xark-ed25519`.

Adding a gadget is just a Cargo dependency:

```toml
# examples/poseidon/Cargo.toml
[dependencies]
xark = { path = "../../crates/xark" }
xark-poseidon = { path = "../../crates/xark-poseidon" }
```

```rust
#![no_std]
use xark::prelude::*;
use xark_poseidon::hash;
// ... call `hash(..)` inside `circuit` and `assert_eq` the result.
```

Because gadgets are ordinary Rust, the backend never needs per-gadget support —
they all lower to the same primitive constraint set.

## Examples

`examples/` holds runnable circuits. The simple ones (`cube`,
`difference_of_squares`, `linear`, `inverse`) depend only on `xark` and use the
prelude; the rest pull in the gadget crates they exercise (`poseidon`,
`keccak`, `sha256`, `ecdsa_verify`, `grumpkin`, …). Build any of them with
`xark build examples/<name>`.

## Status

> **Experimental.** Do not use generated Groth16 parameters or proofs in
> production until the lowering, serialization, and setup process have been
> independently audited. For real deployments run a multi-party phase-2 trusted
> setup (`xark`'s ceremony path); never ship a key produced in insecure
> dev mode.

* **Trusted setup** — `.ptau` phase-1 parsing with admissibility checks, phase-2
  setup derived from a `.ptau` file, and a multi-contributor phase-2 MPC
  ceremony with Schnorr proofs of knowledge and δ-consistency pairing checks.
  See [`docs/trusted-setup.md`](docs/trusted-setup.md).
* **Verifier** — the `xark-verifier` crate verifies proofs on Solana via the
  `alt_bn128` syscalls.

Audit status: see [`docs/audit-status.md`](docs/audit-status.md). No external
audit has been performed; the "experimental" label stays until that changes.

## Development

```bash
# Install the CLI (puts `xark` on PATH — needed for `xark init`/`build`/`prove`
# and the rust-analyzer integration). The stable CLI and the nightly rustc-driver
# are two crates; install both into the same bin dir so `xark` finds `xark-rustc`:
cargo install --path crates/xark-cli
cargo +nightly-2026-05-03 install --path crates/xark-rustc

cargo test --workspace --release
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check

# The compiler (`crates/xark`) is a nightly `rustc_driver`, excluded from the
# root workspace, so its snapshot suite runs separately:
cd crates/xark && cargo test --test snapshot          # fast, 42 tests
cd crates/xark && cargo test --test snapshot -- --include-ignored  # + heavy KATs
```

The nightly pin the compiler needs (and how to bump it) is documented in
[`docs/toolchain.md`](docs/toolchain.md).

Writing circuits — the supported Rust subset, the rejections you'll hit, and what
to write instead: [`docs/subset.md`](docs/subset.md).

Architecture: [`docs/architecture.md`](docs/architecture.md). Security
walkthrough: [`docs/security.md`](docs/security.md).
