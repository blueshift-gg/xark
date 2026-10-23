# Architecture

xark is one tool with two faces — a **language** (write a circuit as ordinary
Rust) and a **toolchain** (`xark build` / `xark prove`) — split into
focused crates with strict layering so that:

* the circuit-author surface (`xark`'s prelude: `Field`, `require_eq`,
  `Private`/`Public`, `bits`) stays small and stable,
* Rust → xark-IR → R1CS lowering can be tested without a proving system,
* the Groth16 layer can be swapped without touching lowering,
* the on-chain verifier stays tiny, `no_std`, and dependency-light,
* gadgets are ordinary Rust library crates, not per-gadget backend opcodes.

```text
Rust circuit source (uses `xark::prelude::*` + gadget crates)
  │  stable rustc (wasm32, `--cfg xark`): parse, type-check, borrow-check,
  │  monomorphize, optimize — circuit ops are calls to `xark.*` wasm imports
  ▼
wasm module
  │  xark-frontend runs it symbolically: known values execute (loops unroll),
  │  witness values flow into constraints; imports build the circuit
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

## How the frontend works

`xark build` runs `cargo build` on the circuit crate for `wasm32-unknown-unknown`
with `--cfg xark` (any stable toolchain, 1.89+). Under that cfg each intrinsic
(`Field` arithmetic, comparisons, hints, `require_eq`, input binding) is a call to
an `xark.*` wasm import. `crates/frontend` then interprets the module: concrete
values execute as ordinary wasm, and the imports, implemented by the circuit
builder, turn witness values into constraints. Witness branches run both arms and
merge with selects; an arm that can only panic is pruned and its condition
constrained. Because every circuit operation is an opaque import, the circuit is
the same under every rustc (CI checks 1.89, stable and beta). Details:
[`crates/frontend/README.md`](../crates/frontend/README.md); toolchains:
[`docs/toolchain.md`](toolchain.md).

## Crates

### `xark` (the language + CLI) — `crates/lang`

The library defines the circuit primitives — `Field`, `require_eq`,
`Private`/`Public`, and the `__xark_*` / `hint_*` intrinsics (wasm imports in the
circuit build) — in its `lang` module, re-exported via its `prelude` (so an author
needs only `use xark::prelude::*`). The `xark` command is the `xark-cli` crate
(`crates/cli`); the frontend that lowers a circuit's wasm is `xark-frontend`
(`crates/frontend`).

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

Solves the witness from `--inputs` values and proves with `xark-groth16`
(`circuit("name").prove(inputs)` returns the proof bytes). `xark` re-exports it
as `xark::prover` in host builds, so circuit crates depend on `xark` alone.

### `xark-groth16` — `crates/groth16`

The Groth16 implementation: key generation (dev and Powers-of-Tau phase 2), the
streaming prover, verification, and the key/proof types, which serialize
byte-for-byte like `ark-groth16`'s (checked against it in tests).

### `xark-backend` — `crates/backend`

Frontend-agnostic Groth16 over BN254:

* `verify.rs` — Groth16 verification (`xark-groth16`'s pairing check).
* `ptau.rs` / `ceremony.rs` — the real trusted-setup path:
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
