# xark — Rust Groth16 Backend for Noir

[![CI](https://github.com/blueshift/xark/actions/workflows/ci.yml/badge.svg)](https://github.com/blueshift/xark/actions/workflows/ci.yml)

xark consumes Noir/ACIR artifacts, lowers supported ACIR opcodes into R1CS,
and proves/verifies them using Arkworks Groth16 over BN254. Noir remains the
frontend; this repository owns the backend boundary:

```
Noir source
 -> nargo compile / nargo execute
 -> ACIR artifact + witness artifact
 -> xark
 -> R1CS
 -> Groth16 setup / prove / verify
 -> proof, verification key, public inputs, optional verifier exports
```

## Crates

* `xark-acir-r1cs` (`crates/acir-r1cs`) — artifact + witness parsing, ACIR →
 R1CS lowering, opcode coverage, opcode rejection. Houses the gadget library
 (Sha256, Blake2s, Blake3, Keccak-f[1600], AES-128, Poseidon2, ECDSA
 secp256k1/secp256r1, variable-index memory).
* `xark-backend` (`crates/backend`) — Arkworks `ConstraintSynthesizer`
 wrapper; Groth16 setup/prove/verify; key + proof serialization (binary +
 JSON); `.ptau` phase-1 parsing and phase-2 contribution; multi-contributor
 MPC ceremony driver; Solana wire-format export.
* `xark-cli` (`crates/cli`) — the `xark` command-line tool (`inspect`,
 `setup`, `prove`, `verify`, `export`, `ceremony`).
* `xark-verifier` (`crates/verifier`) — on-chain Groth16 verifier for
 Solana, using the `alt_bn128` syscalls.

## Prerequisites

Noir must be [installed separately](https://noir-lang.org/docs/installation).
See [NOIR_VERSION.md](./NOIR_VERSION.md) for compatible versions.

## Quick start

```bash
# 1. Install xark CLI
cargo install --path ./crates/cli

# 2. Compile a circuit with Noir
cd crates/tests/circuits/arithmetic_square
nargo execute
#    Produces: target/arithmetic_square.json  (compiled ACIR artifact)
#              target/arithmetic_square.gz    (witness generated from Prover.toml)

# 3. Inspect the compiled ACIR artifact
xark inspect

# 4. Generate proving and verifying keys (dev mode — see warning below)
xark setup --insecure-dev-mode
#    Produces: target/groth16/proving_key.bin
#              target/groth16/verifying_key.bin
#              target/groth16/metadata.json
#              target/groth16/snarkjs-verification_key.json

# 5. Generate a proof against the witness from step 2
xark prove
#    Produces: target/groth16/proof.bin
#              target/groth16/public_inputs.bin
#              target/groth16/snarkjs-proof.json
#              target/groth16/snarkjs-public.json

# 6. Verify the proof
xark verify
#    Checks the proof against the verifying key and public inputs.
#    Output: `Proof verified: true`

# 7. Export a verifier crate for Solana program
xark export
#    Produces: target/arithmetic_square-xark-verifier/
```

## snarkjs compatibility

`xark setup` and `xark prove` emit snarkjs-compatible JSON alongside the
native binary artifacts:

* `snarkjs-verification_key.json` — from `xark setup`
* `snarkjs-proof.json` and `snarkjs-public.json` — from `xark prove`

These can be verified directly with snarkjs:

```bash
snarkjs groth16 verify \
  target/groth16/snarkjs-verification_key.json \
  target/groth16/snarkjs-public.json \
  target/groth16/snarkjs-proof.json
```

This enables verification in JavaScript environments (browser, Node.js, etc.)
and compatibility with the snarkjs/circom ecosystem.

## Solana on-chain verifier

`xark export` generates a self-contained Rust crate that embeds your circuit's
verifying key. The simplest way to verify a proof is to use the
`verify_instruction_data` function.

### Pinocchio example
```rust
use arithmetic_square_xark_verifier as verifier;
use pinocchio::{
    account::AccountView,
    address::Address,
    entrypoint,
    ProgramResult,
};
use solana_program_error::ProgramError;

entrypoint!(process_instruction);

fn process_instruction(
    _program_id: &Address,
    _accounts: &mut [AccountView],
    instruction_data: &[u8],
) -> ProgramResult {
    // instruction_data = proof (256 B) || public_inputs (N × 32 B)
    if verifier::verify_instruction_data(instruction_data) {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}
```

The key points:

* The generated crate embeds the verifying key at compile time.
* `verify_instruction_data` takes the raw instruction data
  (`proof || public_inputs`) and verifies it against the embedded verifying key.
* When the circuit changes, re-run `xark export`; the generated crate is the
  **only thing** you update — your program code stays the same.
* See [`client_call_example.rs`](crates/tests/fixtures/groth16/arithmetic_square/client_call_example.rs)
  for an example of submitting the proof to an onchain program.

If you need a single program to serve multiple circuits with verifying keys
loaded from accounts, use the `verify_proof_only` API:

```rust
use xark_verifier::verify_proof_only;

let vk_bytes = /* loaded from an authenticated account */;
let ok = verify_proof_only(vk_bytes, instruction_data).unwrap_or(false);
```

It is important that the program authenticates the verifying keys in this approach.

## Status

> **This project is experimental.** Do not use generated Groth16 parameters or
> proofs in production until the backend, lowering logic, serialization, and
> setup process have been independently audited. For real deployments use
> `xark ceremony` to run a multi-party phase-2 trusted setup; never ship a key
> produced with `--insecure-dev-mode`.

Supported in this release:

* `AssertZero` (arithmetic constraints) — full multi-term coverage.
* `BlackBoxFuncCall`:
 * `RANGE` (with constant fast path).
 * `AND` / `XOR` bitwise.
 * `Sha256Compression` (~53k constraints), `Blake2s` (~33k), `Blake3`
 (~23k, single + multi-chunk), `Keccakf1600` (~250k).
 * `AES128Encrypt` (~46k per 16-byte block).
 * `Poseidon2Permutation`.
 * `EmbeddedCurveAdd`, `MultiScalarMul` (Grumpkin embedded curve) —
 points validated on-curve at allocation time.
 * `EcdsaSecp256k1` (~3.6M constraints per verify, GLV + fixed-base
 comb on `G`), `EcdsaSecp256r1` (~5.4M, comb on `G` + 4-bit
 windowed double-and-add on `Q`). Both validate the public key
 is on the curve and `r, s ∈ [1, n − 1]`.
* `MemoryInit` / `MemoryOp` — constant-index reads/writes; variable-index
 reads and writes via a selector-gated per-slot shadow update.
* `BrilligCall` — trust-outputs strategy (the surrounding `AssertZero`
 opcodes pin the outputs; see `docs/brillig.md`).
* `Call` (cross-circuit) — inlined into the caller's R1CS via
 witness-index shifting, including nested calls. Predicated calls
 (`predicate ≠ 1`) are supported uniformly via an `e`-aux gating
 trick in `R1csBuilder::enforce`, so every gadget works under a
 Call predicate without per-gadget threading.

Verifier:

* **Solana** on-chain verifier — `xark export` generates a self-contained
  verifier crate and proof (see "Solana on-chain verifier" above). The
  `xark-verifier` crate provides the underlying `alt_bn128` syscall verifier.

Trusted setup:

* `.ptau` phase-1 transcript parsing with admissibility checks
 (`docs/trusted-setup.md`).
* Phase-2 setup derived from a `.ptau` file and per-deployment seed.
* Multi-contributor phase-2 MPC ceremony with Schnorr proofs of
 knowledge and δ-consistency pairing checks.

See `NOIR_VERSION.md` for the pinned nargo/ACIR version. (xark lowers
ACIR, not Noir source — the pin is on the `nargo`-emitted ACIR format, not
the Noir language.)

## Development

Use `--release` when running the test suite. End-to-end Groth16
setup/prove/verify pipelines in the integration tests are 10–20× slower
in debug:

```bash
cargo test --workspace --release
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

Benchmarks (criterion) live under `crates/tests/benches/`:

```bash
cargo bench -p xark-tests
# Or save a baseline before a perf PR and compare afterwards:
cargo bench -p xark-tests -- --save-baseline before
cargo bench -p xark-tests -- --baseline before
```

Audit status: see [`docs/audit-status.md`](docs/audit-status.md).
No external audit has been performed; the "experimental" label above
stays until that changes.

For Solana on-chain verifier tests, install the Anza CLI (provides
`cargo-build-sbf`) and run `cargo test -p xark-tests --test sbpf --release`;
each `#[svm_test]` is compiled to its own SBF program and run in Mollusk on
the real `alt_bn128` syscalls.
