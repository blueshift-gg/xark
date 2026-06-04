# Architecture

xark is split into three crates with strict layering. Each crate's job is
narrow on purpose, so that:

* artifact parsing can be tested without depending on Arkworks,
* the Groth16 layer can be swapped or extended without touching ACIR
  parsing, and
* the CLI is a thin wrapper that owns file paths and user-facing text only.

```text
xark-cli ──▶ groth16-backend ──▶ acir-r1cs ──▶ (acir, acvm crates, Arkworks)
                                       │
                                       └─▶ ark-bn254 / ark-relations
```

## `acir-r1cs`

Owns the boundary between the Noir world and the Arkworks world.

* `artifact.rs` — parses the JSON wrapper that `nargo` writes
  (`target/<name>.json`), pulls out the base64-encoded ACIR `Program`, and
  hands it to `acir::circuit::Program::deserialize_program`. We pin the Noir
  version inside `SUPPORTED_NOIR_VERSION_PREFIX` and refuse any other.
* `witness.rs` — reads the gzip-compressed `WitnessStack` file and converts
  every Noir field element to `ark_bn254::Fr`.
* `field.rs` — single source of truth for `FieldElement <-> Fr`. The two
  types are isomorphic for the `bn254` feature, but we always convert via
  canonical big-endian bytes to keep the boundary explicit and testable.
* `opcodes/` — opcode classification (supported vs unsupported) and the
  `unsupported_error` builder that the lowering layer uses for hard
  rejections.
* `lower.rs` — the heart of the project. Converts ACIR `Opcode::AssertZero`
  expressions into Arkworks R1CS constraints. Public input ordering is
  fixed by the parsed artifact and asserted here (all public input variables
  are allocated before any opcode is touched). Multi-mul-term expressions
  decompose into `t_i = a_i * b_i` auxiliaries plus one summing linear
  constraint.
* `r1cs_builder.rs` — bookkeeping wrapper around `ConstraintSystemRef<Fr>`
  that tracks the `WitnessIndex → Variable` map.
* `gadgets/` — empty placeholders. Range, boolean, bitwise and hash gadgets
  land here in later milestones.

## `groth16-backend`

Wraps `acir-r1cs` for ark-groth16:

* `circuit.rs` — implements `ConstraintSynthesizer<Fr>` over a
  `LoweredAcirCircuit` plus an optional `WitnessMap<Fr>`. Setup mode passes
  `None`; proving passes `Some(witness)`.
* `setup.rs` / `prove.rs` / `verify.rs` — thin wrappers over Arkworks
  Groth16 functions, with explicit `CryptoRng + RngCore` bounds on the
  setup/prove RNGs so callers can't accidentally pass a non-cryptographic
  source.
* `keys.rs`, `proof.rs` — binary I/O using `CanonicalSerialize`.
* `serialization.rs` — JSON encodings for proofs, verifying keys, and
  public inputs. All coordinates are emitted as decimal strings; `encoding`
  is recorded explicitly so future hex support can be opt-in.
* `evm.rs` — stubbed exporter; the CLI surface exists but returns the
  documented "not implemented yet" error.

## `xark-cli`

* `commands/` — one module per subcommand. Each command owns its own
  argument parsing, file I/O, and human/JSON output. There is no shared
  state between commands.
* `synth_err` — single shim that converts ark-relations's `SynthesisError`
  (which is `ark_std::error::Error`, not `std::error::Error`) into
  `anyhow::Error`.

## Determinism and circuit hashing

`LoweredAcirCircuit::circuit_hash` covers:

* `LOWERING_VERSION` (bump it whenever the lowering algorithm changes).
* The curve and proving system identifiers.
* The pinned Noir version string.
* The number and identity of public inputs.
* The `Display` form of every opcode (which bakes in coefficients and
  witness indices).

Setup writes that hash into `metadata.json` alongside the backend version,
timestamp, and constraint count. Any change to lowering or to the circuit
itself produces a different hash.
