# Architecture

xark is one tool with two faces — a **language** (write a circuit as ordinary
`#![no_std]` Rust) and a **toolchain** (`xark build` / `xark prove`) — split into
focused crates with strict layering so that:

* the circuit-author surface (`xark`'s prelude: `Field`, `require_eq`,
  `Private`/`Public`, `bits`) stays small and stable,
* MIR → xark-IR → R1CS lowering can be tested without a proving system,
* the Groth16 layer can be swapped without touching lowering,
* the on-chain verifier stays tiny, `no_std`, and dependency-light,
* gadgets are ordinary Rust library crates, not per-gadget backend opcodes.

```text
Rust circuit source (uses `xark::prelude::*` + gadget crates)
  │  rustc frontend (nightly): parse, type-check, borrow-check, monomorphize
  ▼
rustc MIR  ──(-Zalways-encode-mir inlines cross-crate gadget calls)
  │  extract the `circuit` fn's MIR, sanitize + validate the accepted subset
  ▼
xark-IR (primitive constraint / hint program)
  │  lower to rank-1 constraints
  ▼
R1CS
  │  Groth16 setup / prove / verify (BN254)
  ▼
proof + verifying key ──▶ on-chain Solana verifier (alt_bn128 syscalls)
```

The backend never grows a per-gadget opcode: gadgets (hashes, curves, ECDSA, …)
are plain Rust crates that lower to the *same* small primitive constraint set.

## How MIR is used

The `xark` binary is both the friendly CLI and, when `cargo` invokes it as
`RUSTC` during `xark build`, a `rustc_driver` (nightly, `#![feature(rustc_private)]`).
`xark build` runs `cargo build` on the circuit crate with itself as the compiler
under one pinned nightly, so every dependency (the `xark` lib and gadget crates)
is built with matching MIR-encoded rlibs. Only the primary crate
(`CARGO_PRIMARY_PACKAGE`) is extracted; the rest compile normally so their MIR is
available for cross-crate inlining.

For the primary crate the driver, in `after_analysis`, obtains the `TyCtxt`, finds
`pub fn circuit(..)`, reads its signature to recover `Private`/`Public` visibility,
pulls its MIR body (gadget calls inlined via `-Zalways-encode-mir`), validates that
only the accepted MIR subset is present (rejecting arbitrary control flow,
references, aggregates, unknown calls, …), lowers it to xark-IR and then R1CS, and
writes the output. Signalling intrinsics recognised in MIR are named `__xark_*`
(`__xark_add`, `__xark_mul`, `__xark_hint_bit`, …).

Nightly is required only because there is no stable API for MIR access, and it is
hidden inside the tool: **circuit authors write stable Rust**; only the tool touches
nightly (pinned in `crates/lang/rust-toolchain.toml`). See
[`docs/toolchain.md`](toolchain.md) for the pin and bump procedure.

## Crates

### `xark` (the language + CLI) — `crates/lang`

The library defines the marker primitives — `Field`, `require_eq`,
`Private`/`Public`, and the `__xark_*` / `hint_*` intrinsics the compiler
recognises in MIR — in its `lang` module, re-exported via its `prelude` (so an
author needs only `use xark::prelude::*`; the marker bodies never run, as the tool
stops after MIR extraction). The binary (feature-gated behind `cli`) is the `xark`
command — `build`, `prove`/`verify` — and doubles as the `rustc_driver`. Compiler
internals live in `crates/rustc/src/{driver,find_entry,validate,lower_mir,diagnostics}.rs`.

### `xark-ir`

The xark-IR data structures (variables, linear combinations, R1CS constraints, the
primitive/hint program) plus JSON serialization.

### Gadget crates (in `gadgets/`, add individually)

The circuit-library surface lives under **`gadgets/`**, separate from the core
toolchain in `crates/` so it can be forked or used on its own. Everything here is
ordinary Rust that lowers to the same primitive constraint set (no per-gadget
backend support), and each ships KAT tests.

Shared libraries the gadgets build on: `xark-bits` (bit/word blocks — `to_bits32`,
`xor32`, `rotr32`, `add32`, …), `xark-bignum` (non-native / foreign-field
arithmetic, used by the EC gadgets), `xark-curve` (shared curve macros), `xark-hash`
(the `Hash`/`Digest` types). The gadgets: `xark-poseidon`, `xark-poseidon2`,
`xark-sha256`, `xark-keccak`, `xark-mimc`, `xark-blake3`, `xark-blake2s`, `xark-aes`,
`xark-pedersen`, `xark-grumpkin`, `xark-secp256k1`, `xark-secp256r1`, `xark-ed25519`.

### `xark-prover` — `crates/prover`

Solves the witness from `--inputs` values, synthesizes the R1CS as an Arkworks
`ConstraintSynthesizer`, and runs Groth16 `prove` / `verify`.

### `xark-backend` — `crates/backend`

Frontend-agnostic Groth16 over BN254:

* Groth16 setup / prove / verify. `setup`/`prove` take explicit `CryptoRng + RngCore`
  bounds; `prove` self-verifies before returning.
* `ptau.rs` / `setup_phase2.rs` / `ceremony.rs` — the real trusted-setup path:
  ingest a snarkjs `powersoftau` (`.ptau`) transcript, derive a phase-2 setup,
  run a multi-contributor MPC ceremony with Schnorr PoKs and δ-consistency
  pairing checks (see `docs/trusted-setup.md`).
* `keys.rs`, `proof.rs`, `serialization.rs` — binary (`CanonicalSerialize`)
  encoding of keys, proofs, and public inputs.
* `solana.rs` — the little-endian wire encoder for the on-chain verifier.

### `xark-verifier` — `crates/verifier`

The on-chain Groth16 verifier: consumes the LE wire bytes, runs the pairing check
via `solana-nostd-alt-bn128`, `#![no_std]` on the Solana target. The typed
`Verifier<N>` bakes the VK in at compile time.

## Determinism and circuit hashing

The circuit hash covers a lowering-version tag (bump it whenever the lowering
algorithm changes), the curve and proving-system identifiers, the number and
identity of public inputs, and the constraints themselves (coefficients and variable
indices). Setup writes that hash into metadata alongside the backend version and
constraint count, so any change to lowering or to the circuit produces a different
hash.
