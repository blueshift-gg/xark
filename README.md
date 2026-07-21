# xark — write, compile, prove and verify zero-knowledge circuits in Rust

[![CI](https://github.com/blueshift-gg/xark/actions/workflows/ci.yml/badge.svg)](https://github.com/blueshift-gg/xark/actions/workflows/ci.yml)

xark takes a circuit written as ordinary Rust all the way to an on-chain proof.
You write the circuit in a small, explicitly validated Rust subset; xark drives
`rustc` to type-check it, extracts its MIR, lowers that to R1CS, and proves it
with Groth16 over BN254 — with a verifier that runs on Solana. There is no
separate circuit DSL: **gadgets are ordinary Rust libraries** that lower to a
small primitive constraint set, so the backend stays lean and the frontend
stays expressive.

## Installation

xark installs as **two** binaries: `xark` — the CLI, plain **stable** Rust — and
`xark-rustc`, the `rustc_driver` shim `xark build` runs to extract MIR, which needs
a **pinned nightly**. `xark build` invokes `xark-rustc` as a sibling of `xark`, so
install both into the same bin directory (`cargo install` uses `~/.cargo/bin`).

Install the pinned nightly the driver needs, then both binaries:

```bash
rustup toolchain install nightly-2026-05-03 --profile minimal --component rust-src --component rustc-dev --component llvm-tools
# the rustc-driver shim (pinned nightly)
cargo +nightly-2026-05-03 install --git https://github.com/blueshift-gg/xark xark-rustc
# the CLI (stable Rust)
cargo install --git https://github.com/blueshift-gg/xark xark-cli
```

Only `xark-rustc` touches nightly — you write **stable Rust** in your circuits.

## As a language (library)

Write a circuit as a `#![no_std]` function over `Field` values, using the `xark`
prelude. `require_eq` emits a circuit equality constraint (not a native `bool`);
`Private<T>` / `Public<T>` mark input visibility; `Field` supports `+ - * ^`
(with `^ n` meaning exponentiation).

```rust
#![no_std]
use xark::prelude::*;

/// Prove knowledge of a cube root: `secret^3 == result`.
pub fn circuit(secret: Private<Field>, result: Public<Field>) {
    require_eq(secret ^ 3, result);
}
```

## As a toolchain (CLI)

```bash
# Scaffold a new circuit crate, pre-wired for rust-analyzer diagnostics.
xark init my-circuit

# Compile: Rust → MIR → xark-IR → R1CS. All output (artifacts + an isolated
# cargo target) lives under the crate's target/xark/.
xark build examples/cube
# → writes examples/cube/target/xark/cube/ (circuit.json + r1cs.json)

# Generate Groth16 keys. With no .ptau this produces an INSECURE dev key
# (single-party OsRng); pass --ptau-file (or run `xark ceremony`) for production.
xark setup examples/cube

# Solve the witness from your inputs, then produce AND verify a Groth16 proof.
xark prove examples/cube --input secret=3 --input result=27
# → ✅ Proof produced and self-checked (1 public input).

# Validate a circuit WITHOUT emitting artifacts — subset violations as rustc
# diagnostics with source spans (great for editors / CI).
xark check examples/cube
```

## Editor diagnostics (rust-analyzer)

`xark check <crate-dir>` runs the full `rustc` frontend *and* the xark subset
validator, surfacing every rejection as a **real `rustc` diagnostic with a source
span**. With `--message-format=json` it emits the same JSON stream as `cargo
check`, so an editor shows live rejections on save. `xark init` writes this
wiring; to add it to an existing crate, point `rust-analyzer`'s check command at
`xark` (which must be on `PATH`):

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

Replace `.` with the crate directory (e.g. `examples/cube`) when the editor is
opened above the circuit crate. A violation then appears inline, e.g.:

```text
error: witness-dependent control flow is not supported
 --> src/lib.rs:7:5
note: branch conditions must be compile-time constants (e.g. loop bounds)
```

## The pipeline

```text
Rust source  →  rustc MIR  →  xark-IR  →  R1CS  →  Groth16 (BN254)  →  Solana verifier
```

`xark build` runs `cargo build` on your circuit crate with `xark-rustc` (the
`rustc_driver` shim, pinned nightly) as the compiler, so every dependency (the
`xark` lib and any gadget crates) is compiled with matching MIR-encoded rlibs.
rustc does the hard work — parse, type-check, borrow-check, monomorphize — and
`xark-rustc` then finds `pub fn circuit(..)`, reads its signature for `Private` /
`Public` visibility, extracts its MIR (cross-crate gadget calls inlined via
`-Zalways-encode-mir`), validates the accepted subset (rejecting arbitrary
control flow, references, aggregates, unknown calls, …), and lowers it to
xark-IR then R1CS. Signalling intrinsics recognised in MIR are named `__xark_*`
(`__xark_add`, `__xark_mul`, `__xark_hint_bit`, …). The backend never grows a
per-gadget opcode: hashes / curves / ECDSA are plain Rust crates that lower to
the same primitive constraints.

MIR access has no stable API, so `xark-rustc` uses a pinned nightly
(`rust-toolchain.toml`) internally — invisible to circuit authors.

## snarkjs compatibility

`xark setup` and `xark prove` emit snarkjs-compatible JSON alongside the native
binary artifacts: `snarkjs-verification_key.json` (from `xark setup`),
`snarkjs-proof.json` and `snarkjs-public.json` (from `xark prove`). Verify
directly with snarkjs (enabling verification in JS/browser/Node environments):

```bash
snarkjs groth16 verify \
  target/xark/<name>/snarkjs-verification_key.json \
  target/xark/<name>/snarkjs-public.json \
  target/xark/<name>/snarkjs-proof.json
```

## Crates and gadgets

* **`xark`** (`crates/lang`, `#![no_std]`, stable) — the language library; its
  `prelude` provides the marker primitives (`Field`, `require_eq`,
  `Private`/`Public`). The CLI is **`xark-cli`** (stable, binary `xark`) and the
  MIR-extraction driver is **`xark-rustc`** (pinned nightly).
* **Backend** — `xark-backend` (Groth16 setup/prove/verify, trusted setup,
  serialization) and `xark-verifier` (the `no_std` on-chain Solana verifier).
  Both are frontend-agnostic.

Gadgets are **separate crates you add only when you need them**, all under
**`gadgets/`** — kept apart from the core toolchain so they're easy to fork or
use standalone. Shared circuit libraries: `xark-bits` (booleanity /
bit-decomposition), `xark-bignum` (non-native arithmetic, used by the EC
gadgets), `xark-curve` (curve macros), `xark-hash` (`Hash`/`Digest` types). Leaf
gadgets: `xark-poseidon`, `xark-poseidon2`, `xark-sha256`, `xark-keccak`,
`xark-mimc`, `xark-blake3`, `xark-blake2s`, `xark-aes`, `xark-pedersen`,
`xark-grumpkin`, `xark-secp256k1`, `xark-secp256r1`, `xark-ed25519`.

Adding a gadget is just a Cargo dependency:

```toml
# examples/poseidon/Cargo.toml
[dependencies]
xark = { path = "../../crates/lang" }
xark-poseidon = { path = "../../gadgets/xark-poseidon" }
```

```rust
#![no_std]
use xark::prelude::*;
use xark_poseidon::hash;
// ... call `hash(..)` inside `circuit` and `require_eq` the result.
```

## Examples

`examples/` holds runnable circuits. The simple ones (`cube`,
`difference_of_squares`, `linear`, `inverse`) depend only on `xark`; the rest
pull in the gadget crates they exercise. Build any with `xark build
examples/<name>`.

## Status

> **Experimental.** Do not use generated Groth16 parameters or proofs in
> production until the lowering, serialization, and setup process have been
> independently audited. For real deployments run a multi-party phase-2 trusted
> setup (`xark`'s ceremony path); never ship a key produced in insecure dev mode.

* **Trusted setup** — `.ptau` phase-1 parsing with admissibility checks, phase-2
  setup derived from a `.ptau`, and a multi-contributor phase-2 MPC ceremony with
  Schnorr proofs of knowledge and δ-consistency pairing checks. See
  [`docs/trusted-setup.md`](docs/trusted-setup.md).
* **Verifier** — `xark-verifier` verifies proofs on Solana via the `alt_bn128`
  syscalls.

No external audit has been performed; see [`docs/audit-status.md`](docs/audit-status.md).

## Development

```bash
# Install the CLI (puts `xark` on PATH) and the nightly rustc-driver into the
# same bin dir so `xark` finds `xark-rustc`:
cargo install --path crates/cli
cargo +nightly-2026-05-03 install --path crates/rustc

cargo test --workspace --release
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check

# `crates/lang` is excluded from the root workspace (needs the pinned nightly),
# so its snapshot suite runs separately:
cd crates/lang && cargo test --test snapshot          # fast, ~78 tests
cd crates/lang && cargo test --test snapshot -- --include-ignored  # + heavy KATs
```

The nightly pin (and how to bump it): [`docs/toolchain.md`](docs/toolchain.md).
Writing circuits — the supported subset and rejections: [`docs/subset.md`](docs/subset.md).
Architecture: [`docs/architecture.md`](docs/architecture.md).
Security walkthrough: [`docs/security.md`](docs/security.md).
