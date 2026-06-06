# Architecture

xark is split into focused crates with strict layering, so that:

* ACIR artifact parsing and R1CS lowering can be tested without depending on a
 proving system,
* the Groth16 layer can be swapped or extended without touching ACIR parsing,
* the on-chain verifier stays tiny, `no_std`, and dependency-light, and
* the CLI is a thin wrapper that owns file paths and user-facing text only.

```text
xark-cli ──▶ xark-backend ──▶ xark-acir-r1cs ──▶ (acir, acvm crates, Arkworks)

xark-verifier (standalone, no_std on Solana) ──▶ solana-nostd-alt-bn128
 ▲
 └── the crate `xark export` generates depends on this, and so does any
 Solana program that verifies a proof on chain.

xark-tests (publish = false) ── all integration tests, benches, and fixtures
```

The prove-side stack (`xark-cli` → `xark-backend` → `xark-acir-r1cs`) runs
off-chain on the host. The verify-side crate (`xark-verifier`) is independent:
it consumes only the exported wire bytes and runs both on the host (Arkworks
fallback) and on chain (the `alt_bn128` syscalls).

## `xark-acir-r1cs`

Owns the boundary between the Noir/ACIR world and the Arkworks world.

* `artifact.rs` — parses the JSON wrapper that `nargo` writes
 (`target/<name>.json`), base64-decodes the ACIR `Program` bytecode blob, and
 hands it to `acir::circuit::Program::deserialize_program`. The supported
 ACIR/nargo version
 is pinned in `SUPPORTED_NOIR_VERSION_PREFIX` and any other is refused. (xark
 lowers ACIR, not Noir source — see `NOIR_VERSION.md`.)
* `witness.rs` — reads the gzip-compressed `WitnessStack` file and converts
 every Noir field element to `ark_bn254::Fr`.
* `field.rs` — single source of truth for `FieldElement <-> Fr`. The two types
 are isomorphic for the `bn254` feature, but we always convert via canonical
 big-endian bytes to keep the boundary explicit and testable.
* `opcodes/` — opcode classification and dispatch: `AssertZero`, memory
 (init/read/write, constant- and variable-index), Brillig (unconstrained)
 blocks, and multi-function `Call`. Genuinely unsupported opcodes fail loudly
 (`opcodes/unsupported.rs`) with the opcode index and a remediation hint.
* `gadgets/` — the black-box function implementations: range, boolean, bitwise,
 the hashes (SHA-256, Keccak, Blake2s, Blake3, Poseidon), AES, ECDSA
 (secp256k1 / secp256r1), and elliptic-curve ops. Each has KAT tests in
 `xark-tests`.
* `lower.rs` — the heart of the project. Allocates all public-input variables
 first (ordering fixed by the parsed artifact and asserted here), then lowers
 each opcode to Arkworks R1CS constraints. `AssertZero` expressions with
 multiple mul-terms decompose into `t_i = a_i * b_i` auxiliaries plus one
 summing linear constraint; black-box opcodes dispatch into `gadgets/`.
* `r1cs_builder.rs` — bookkeeping wrapper around `ConstraintSystemRef<Fr>` that
 tracks the `WitnessIndex → Variable` map, reused for both setup-mode and
 proving-mode synthesis so circuit shape stays identical between the two.
* `public_inputs.rs` — extracts the public portion of the witness in the order
 the prover and verifier both agree on.

## `xark-backend`

Wraps `xark-acir-r1cs` for `ark-groth16`:

* `circuit.rs` — implements `ConstraintSynthesizer<Fr>` over a
 `LoweredAcirCircuit` plus an optional witness. Setup mode passes `None`;
 proving passes `Some(witness)`.
* `setup.rs` / `prove.rs` / `verify.rs` — the Groth16 entry points.
 `setup`/`prove` take explicit `CryptoRng + RngCore` bounds so callers can't
 pass a non-cryptographic source; `prove` self-verifies its output before
 returning (a witness/lowering bug fails fast as `Unsatisfiable` rather than
 shipping a broken proof).
* `ptau.rs` / `setup_phase2.rs` / `ceremony.rs` — the real trusted-setup path:
 ingest a snarkjs `powersoftau` (`.ptau`) transcript, derive a phase-2 setup,
 and run a multi-contributor MPC ceremony with Schnorr PoKs and δ-consistency
 pairing checks. See `docs/trusted-setup.md`.
* `keys.rs`, `proof.rs` — binary I/O using Arkworks' `CanonicalSerialize`.
* `serialization.rs` — JSON encodings for proofs, verifying keys, and public
 inputs (decimal-string coordinates; `encoding` recorded explicitly).
* `solana.rs` — the little-endian wire encoder for the on-chain verifier
 (`assemble_{vk,proof,public_inputs}_bytes_le`). See `docs/serialization.md`.

## `xark-verifier`

The on-chain Groth16 verifier (see its own `README.md`). Consumes the LE wire
bytes, runs the pairing check via `solana-nostd-alt-bn128`, and is `#![no_std]`
on the Solana target so it links into the cdylibs `svm-unit-test` generates. The
typed `Verifier<N>` bakes the VK in at compile time. `xark export` generates a
small self-contained crate per circuit that depends on this one.

## `xark-cli`

* `commands/` — one module per subcommand (`setup`, `prove`, `verify`,
 `export`, `inspect`, `write-vk`, `ceremony`). Each owns its own argument
 parsing, file I/O, and human/JSON output; there is no shared state between
 commands. The binary is named `xark`.

## `xark-tests`

`publish = false` aggregator holding every crate's integration tests, all
benches, and the committed circuit fixtures (see its `README.md` for why it has
to be one crate — the `svm-unit-test` cdylibs depend on its lib).

## Determinism and circuit hashing

`LoweredAcirCircuit::circuit_hash` covers:

* `LOWERING_VERSION` (bump it whenever the lowering algorithm changes).
* The curve and proving system identifiers.
* The pinned nargo/ACIR version string (the ACIR format the artifact was
 compiled with — not the Noir source language).
* The number and identity of public inputs.
* The `Display` form of every opcode (which bakes in coefficients and witness
 indices).

Setup writes that hash into `metadata.json` alongside the backend version,
timestamp, and constraint count. Any change to lowering or to the circuit
itself produces a different hash.
