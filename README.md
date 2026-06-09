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
 `setup`, `prove`, `verify`, `export`, `ceremony`, `write-vk`).
* `xark-verifier` (`crates/verifier`) — on-chain Groth16 verifier for
 Solana, using the `alt_bn128` syscalls.

## Quick start

```bash
cd crates/tests/circuits/arithmetic_square
nargo execute

xark inspect --artifact./target/arithmetic_square.json

xark setup \
 --artifact./target/arithmetic_square.json \
 --out./target/groth16 \
 --insecure-dev-mode

xark prove \
 --artifact./target/arithmetic_square.json \
 --witness./target/arithmetic_square.gz \
 --proving-key./target/groth16/proving_key.bin \
 --out./target/groth16/proof.bin

xark verify \
 --verifying-key./target/groth16/verifying_key.bin \
 --proof./target/groth16/proof.bin \
 --public-inputs./target/groth16/public_inputs.json
```

Expected:

```
Proof verified: true
```

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

* **Solana** on-chain verifier — `xark export` emits the wire bytes; the
 `xark-verifier` crate verifies them on chain via the `alt_bn128` syscalls.

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
