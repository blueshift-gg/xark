# PLAN.md — Rust Groth16 Backend for Noir

## Project Name

`noir-groth16-rs`

## Goal

Build a Rust backend for Noir that consumes Noir/ACIR artifacts, lowers supported ACIR opcodes into R1CS, and proves/verifies them using Groth16 over BN254 via Arkworks.

This project should act like a serious Rust-native equivalent of the gnark Noir backend idea, but without Go or FFI. Noir remains the frontend. This repository owns the backend boundary:

```text
Noir source
  -> nargo compile / nargo execute
  -> ACIR artifact + witness artifact
  -> noir-groth16-rs
  -> R1CS
  -> Groth16 setup/prove/verify
  -> proof, verification key, public inputs, optional verifier exports
```

## Core Principle

Do not build a Rust clone of gnark’s DSL.

Build this instead:

```text
ACIR parser + witness parser + ACIR-to-R1CS lowering + Arkworks Groth16 backend + CLI
```

Noir already provides the high-level language. This backend should be deterministic, testable, version-pinned, and honest about unsupported ACIR opcodes.

---

# 1. Repository Structure

Create a Rust workspace:

```text
noir-groth16-rs/
  Cargo.toml
  README.md
  PLAN.md
  crates/
    acir-r1cs/
      Cargo.toml
      src/
        lib.rs
        artifact.rs
        witness.rs
        field.rs
        lower.rs
        r1cs_builder.rs
        public_inputs.rs
        opcodes/
          mod.rs
          arithmetic.rs
          blackbox.rs
          memory.rs
          unsupported.rs
        gadgets/
          mod.rs
          boolean.rs
          range.rs
          bitwise.rs
          hash.rs
    groth16-backend/
      Cargo.toml
      src/
        lib.rs
        circuit.rs
        setup.rs
        prove.rs
        verify.rs
        keys.rs
        proof.rs
        serialization.rs
        evm.rs
    noir-groth16-cli/
      Cargo.toml
      src/
        main.rs
        commands/
          mod.rs
          inspect.rs
          setup.rs
          prove.rs
          verify.rs
          write_vk.rs
          export.rs
  examples/
    arithmetic_square/
      Nargo.toml
      src/main.nr
      Prover.toml
    arithmetic_public_inputs/
      Nargo.toml
      src/main.nr
      Prover.toml
    range_basic/
      Nargo.toml
      src/main.nr
      Prover.toml
  tests/
    fixtures/
    integration/
  docs/
    architecture.md
    acir-lowering.md
    serialization.md
    trusted-setup.md
```

## Crate Responsibilities

### `acir-r1cs`

Owns:

* Reading Noir artifacts.
* Reading witness files.
* Converting Noir field elements into `ark_bn254::Fr`.
* Mapping ACIR witnesses to R1CS variables.
* Lowering supported ACIR opcodes into R1CS constraints.
* Rejecting unsupported opcodes explicitly.
* Reporting opcode coverage and constraint counts.

This crate must not perform Groth16 proving.

### `groth16-backend`

Owns:

* Arkworks `ConstraintSynthesizer` wrapper.
* BN254 Groth16 setup.
* Proof generation.
* Proof verification.
* Proving key / verifying key serialization.
* Proof serialization.
* Public input ordering.
* Optional EVM-compatible formatting.

This crate must not know about Noir project folders directly. It should operate on parsed/lowered circuit structures from `acir-r1cs`.

### `noir-groth16-cli`

Owns:

* CLI UX.
* File paths.
* Commands.
* Error messages.
* Developer diagnostics.
* Integration with example projects.

---

# 2. Initial Dependencies

Use Arkworks as the proving backend.

Start with these dependency families, pinning exact compatible versions in `Cargo.lock`:

```toml
ark-bn254 = "*"
ark-ff = "*"
ark-ec = "*"
ark-groth16 = "*"
ark-relations = "*"
ark-serialize = "*"
ark-std = "*"

anyhow = "*"
thiserror = "*"
clap = { version = "*", features = ["derive"] }
serde = { version = "*", features = ["derive"] }
serde_json = "*"
flate2 = "*"
tracing = "*"
tracing-subscriber = "*"
hex = "*"
base64 = "*"
```

Important:

* Replace `*` with exact versions during implementation.
* Prefer the current stable Arkworks release.
* Pin Noir/ACIR-related crates to the version matching the target Noir release.
* Add a `NOIR_VERSION.md` file documenting the supported `nargo` version.

---

# 3. Supported Noir/ACIR Version

Before implementing parsing, Claude must determine and document the target Noir version.

Create:

```text
NOIR_VERSION.md
```

With:

```text
Supported Noir version:
Supported nargo version:
Supported ACIR artifact format:
Supported witness format:
Date tested:
Known incompatible versions:
```

Do not support multiple Noir versions initially.

The first version of this backend should support exactly one Noir release. Version flexibility comes later.

---

# 4. CLI Design

Implement this CLI binary:

```bash
noir-groth16
```

## Required Commands

### `inspect`

Inspect a Noir artifact and print backend-relevant metadata.

```bash
noir-groth16 inspect \
  --artifact ./target/example.json
```

Output should include:

```text
Circuit name:
Noir/ACIR version if available:
Opcode count:
Witness count:
Public input count:
Private witness count:
Supported opcode count:
Unsupported opcode count:
Unsupported opcodes:
Estimated R1CS constraints:
```

Acceptance:

* Works without a witness.
* Never panics on unsupported opcodes.
* Produces machine-readable JSON with `--json`.

---

### `setup`

Generate Groth16 proving and verifying keys.

```bash
noir-groth16 setup \
  --artifact ./target/example.json \
  --out ./target/groth16 \
  --insecure-dev-mode
```

Outputs:

```text
target/groth16/proving_key.bin
target/groth16/verifying_key.bin
target/groth16/metadata.json
```

Important:

* Groth16 setup is circuit-specific.
* `--insecure-dev-mode` must be required for local random setup.
* Without `--insecure-dev-mode`, fail with a clear error until real MPC/import support exists.

Acceptance:

* Setup succeeds for arithmetic-only example circuits.
* Metadata records circuit hash, Noir version, backend version, curve, proving system, and timestamp.
* Setup fails clearly if unsupported opcodes are present.

---

### `prove`

Generate a Groth16 proof.

```bash
noir-groth16 prove \
  --artifact ./target/example.json \
  --witness ./target/witness.gz \
  --proving-key ./target/groth16/proving_key.bin \
  --out ./target/groth16/proof.bin
```

Also write:

```text
target/groth16/public_inputs.json
target/groth16/proof.json
```

Acceptance:

* Proof generation succeeds for supported circuits.
* Proof generation fails if the witness is missing required assignments.
* Proof generation fails if the witness does not satisfy constraints.
* Public inputs are written in exactly the order expected by verification.

---

### `verify`

Verify a Groth16 proof.

```bash
noir-groth16 verify \
  --verifying-key ./target/groth16/verifying_key.bin \
  --proof ./target/groth16/proof.bin \
  --public-inputs ./target/groth16/public_inputs.json
```

Acceptance:

* Valid proof verifies.
* Modified public input fails.
* Modified proof fails.
* Wrong verifying key fails.

---

### `write-vk`

Extract or convert a verifying key.

```bash
noir-groth16 write-vk \
  --proving-key ./target/groth16/proving_key.bin \
  --out ./target/groth16/verifying_key.json
```

Acceptance:

* Writes both binary and JSON forms.
* JSON includes G1/G2 affine coordinates.
* Field elements are encoded consistently.

---

### `export`

Export artifacts for external systems.

Initial supported export:

```bash
noir-groth16 export evm \
  --verifying-key ./target/groth16/verifying_key.bin \
  --out ./target/groth16/Verifier.sol
```

For MVP, this command may be stubbed with:

```text
EVM verifier export is not implemented yet.
```

But the CLI shape should exist.

---

# 5. Artifact and Witness Parsing

## Objective

Read the files produced by `nargo execute` or the equivalent current Noir workflow.

Expected inputs:

```text
target/<circuit>.json
target/witness.gz
```

Implementation must not assume old Noir artifact shapes. Claude must inspect the generated fixture artifacts from the pinned Noir version.

## Tasks

* [ ] Create example Noir projects.
* [ ] Run `nargo execute` manually during development.
* [ ] Commit small sanitized artifacts under `tests/fixtures`.
* [ ] Implement artifact parsing.
* [ ] Implement witness parsing.
* [ ] Convert all field values to `ark_bn254::Fr`.
* [ ] Identify public input witnesses.
* [ ] Preserve public input order exactly.
* [ ] Add tests for artifact roundtrip parsing.
* [ ] Add tests for witness roundtrip parsing.

## Required Types

In `acir-r1cs`:

```rust
pub struct NoirArtifact {
    pub circuit_name: String,
    pub opcodes: Vec<AcirOpcode>,
    pub public_inputs: Vec<WitnessIndex>,
    pub witness_count: usize,
    pub metadata: ArtifactMetadata,
}

pub struct WitnessMap<F> {
    pub values: BTreeMap<WitnessIndex, F>,
}

pub struct WitnessIndex(pub u32);
```

These may wrap actual ACIR crate types if available and stable. If direct ACIR crate usage is awkward, define local normalized types and parse into those.

---

# 6. R1CS Lowering Design

## R1CS Form

All constraints must be lowered into:

```text
<A, z> * <B, z> = <C, z>
```

Where:

* `z[0]` is one / constant.
* Public inputs are allocated as public input variables.
* Private witnesses are allocated as private witness variables.
* Auxiliary variables are allocated as needed.

Use Arkworks `ConstraintSystemRef<Fr>`.

## Variable Allocation

Rules:

1. Allocate the constant one variable implicitly through Arkworks.
2. Allocate public inputs first and in exact Noir order.
3. Allocate private witnesses after public inputs.
4. Allocate auxiliary variables only during lowering.
5. Maintain a deterministic map:

```rust
BTreeMap<WitnessIndex, Variable>
```

## Arithmetic Lowering

Support ACIR arithmetic assertions first.

An arithmetic expression may contain:

```text
constant
linear terms
multiplication terms
```

The semantic target is:

```text
expression == 0
```

### Linear-only expression

For:

```text
a*x + b*y + c == 0
```

Emit:

```text
0 * 0 = a*x + b*y + c
```

or equivalent R1CS enforcing the linear combination equals zero.

### One multiplication term

For:

```text
q_m*a*b + linear_terms + constant == 0
```

Emit a single R1CS constraint equivalent to:

```text
a * (q_m*b) = -(linear_terms + constant)
```

### Multiple multiplication terms

For:

```text
q0*a0*b0 + q1*a1*b1 + linear_terms + constant == 0
```

Introduce auxiliaries:

```text
t0 = a0 * b0
t1 = a1 * b1
...
q0*t0 + q1*t1 + linear_terms + constant == 0
```

Emit:

```text
a0 * b0 = t0
a1 * b1 = t1
...
0 * 0 = q0*t0 + q1*t1 + linear_terms + constant
```

## Acceptance Tests

Create tests for:

* `x + y = z`
* `x * y = z`
* `x * x = public_y`
* `x * y + z = public_out`
* Multiple multiplication terms in one ACIR expression.
* Negative coefficients.
* Constant terms.
* Zero coefficients.
* Missing witness values.
* Incorrect witness values.

---

# 7. Opcode Support Policy

Unsupported opcodes must be explicit.

Never silently skip an opcode.

Create:

```rust
pub enum BackendError {
    UnsupportedOpcode {
        opcode: String,
        index: usize,
        help: String,
    },
    MissingWitness {
        witness: WitnessIndex,
    },
    ConstraintUnsatisfied {
        detail: String,
    },
    ArtifactVersionUnsupported {
        found: String,
        supported: String,
    },
}
```

## MVP Supported Opcodes

Phase 1 support:

```text
AssertZero / arithmetic constraints
Public/private witness mapping
Basic field equality
```

Phase 2 support:

```text
Range checks
Boolean constraints
Bit decomposition
AND
XOR
```

Phase 3 support:

```text
Poseidon if Noir emits it and Arkworks-compatible parameters are confirmed
Pedersen only if needed
```

Phase 4 support:

```text
SHA256
ECDSA secp256k1
Big integer helpers
```

Phase 5 support:

```text
Memory opcodes
Brillig-related opcodes if emitted in relevant Noir artifacts
```

## Required Behavior

If a circuit uses unsupported opcodes:

```bash
noir-groth16 inspect --artifact target/foo.json
```

Should report them.

```bash
noir-groth16 setup ...
```

Should fail before creating keys.

```bash
noir-groth16 prove ...
```

Should fail before proving.

---

# 8. Black-box Gadget Plan

Black-box functions are the highest-risk area.

Implement them gradually.

## Boolean Gadget

Create:

```rust
pub fn enforce_boolean(var: Variable) -> Result<(), SynthesisError>
```

Constraint:

```text
x * (x - 1) = 0
```

Tests:

* `0` passes.
* `1` passes.
* `2` fails.

## Range Gadget

Implement bit decomposition.

For an `n`-bit range check:

```text
x = b0 + 2*b1 + 4*b2 + ... + 2^(n-1)*b_{n-1}
```

And each bit is boolean.

Tasks:

* [ ] Add auxiliary bit variables.
* [ ] Enforce each bit is boolean.
* [ ] Enforce recomposition equals original value.
* [ ] Reject range sizes larger than field capacity unless explicitly supported.

Tests:

* `x = 0` passes.
* `x = 2^n - 1` passes.
* `x = 2^n` fails.
* Random valid values pass.
* Random invalid values fail.

## Bitwise AND / XOR

Implement via bit decomposition.

For each bit:

```text
AND: z = x * y
XOR: z = x + y - 2xy
```

Tasks:

* [ ] Decompose operands.
* [ ] Enforce boolean bits.
* [ ] Enforce bitwise relation.
* [ ] Recompose output.
* [ ] Add tests against native Rust bitwise operations.

## Hashes and Signatures

Do not start here.

Only implement after arithmetic/range/bitwise are stable.

For each hash/signature gadget:

* Confirm Noir’s exact ACIR black-box semantics.
* Confirm field encoding.
* Confirm endianness.
* Confirm padding.
* Add fixtures generated by Noir.
* Add independent known-answer tests.

---

# 9. Arkworks Groth16 Circuit Wrapper

In `groth16-backend`, implement:

```rust
pub struct NoirGroth16Circuit {
    pub lowered: LoweredAcirCircuit,
    pub witness: Option<WitnessMap<Fr>>,
}
```

Implement:

```rust
impl ConstraintSynthesizer<Fr> for NoirGroth16Circuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        // allocate public inputs
        // allocate private witnesses
        // lower all constraints
        // return Ok(())
    }
}
```

Rules:

* For setup, use a circuit with the same shape but no secret-dependent branching.
* For proving, use full witness assignments.
* Circuit shape must not depend on private witness values.
* Public input order must be deterministic and tested.

---

# 10. Setup / Prove / Verify API

Expose library functions:

```rust
pub fn setup(
    circuit: NoirGroth16Circuit,
    rng: impl RngCore,
) -> Result<Groth16Keys>;

pub fn prove(
    proving_key: &ProvingKey<Bn254>,
    circuit: NoirGroth16Circuit,
    rng: impl RngCore,
) -> Result<Proof<Bn254>>;

pub fn verify(
    verifying_key: &VerifyingKey<Bn254>,
    proof: &Proof<Bn254>,
    public_inputs: &[Fr],
) -> Result<bool>;
```

Also expose deterministic test helpers under a test-only feature:

```rust
#[cfg(feature = "test-deterministic")]
pub fn test_rng() -> impl RngCore;
```

Production CLI should use secure randomness.

---

# 11. Serialization

## Binary

Use Arkworks canonical serialization for:

```text
proving_key.bin
verifying_key.bin
proof.bin
```

## JSON

Create explicit JSON formats.

### `proof.json`

```json
{
  "curve": "bn254",
  "protocol": "groth16",
  "a": {
    "x": "...",
    "y": "..."
  },
  "b": {
    "x": ["...", "..."],
    "y": ["...", "..."]
  },
  "c": {
    "x": "...",
    "y": "..."
  }
}
```

### `verifying_key.json`

```json
{
  "curve": "bn254",
  "protocol": "groth16",
  "alpha_g1": { "x": "...", "y": "..." },
  "beta_g2": { "x": ["...", "..."], "y": ["...", "..."] },
  "gamma_g2": { "x": ["...", "..."], "y": ["...", "..."] },
  "delta_g2": { "x": ["...", "..."], "y": ["...", "..."] },
  "gamma_abc_g1": [
    { "x": "...", "y": "..." }
  ]
}
```

### `public_inputs.json`

```json
{
  "curve": "bn254",
  "field": "fr",
  "encoding": "decimal-string",
  "inputs": ["..."]
}
```

Rules:

* Be explicit about decimal vs hex.
* Use decimal string as default.
* Add `--encoding hex` later.
* Never rely on implicit coordinate ordering.
* Add tests for binary roundtrip and JSON roundtrip.

---

# 12. Trusted Setup Policy

Groth16 requires circuit-specific setup.

The initial CLI must make this impossible to miss.

## Required CLI Behavior

This should fail:

```bash
noir-groth16 setup --artifact target/foo.json --out target/groth16
```

With:

```text
Groth16 setup requires trusted randomness.
For local testing, pass --insecure-dev-mode.
Do not use insecure dev parameters in production.
```

This should work:

```bash
noir-groth16 setup \
  --artifact target/foo.json \
  --out target/groth16 \
  --insecure-dev-mode
```

## Metadata

Write:

```json
{
  "protocol": "groth16",
  "curve": "bn254",
  "setup_mode": "insecure-dev-mode",
  "production_safe": false,
  "circuit_hash": "...",
  "backend_version": "...",
  "noir_version": "...",
  "created_at": "..."
}
```

Future production support:

```text
import proving/verifying keys
MPC ceremony transcript verification
Powers of Tau compatibility if applicable
documented ceremony workflow
```

Do not pretend local setup is production-safe.

---

# 13. Example Noir Programs

Create examples and use them as integration fixtures.

## `examples/arithmetic_square`

```rust
fn main(x: Field, y: pub Field) {
    assert(x * x == y);
}
```

`Prover.toml`:

```toml
x = "9"
y = "81"
```

Acceptance:

* `nargo execute` succeeds.
* `inspect` reports only supported opcodes.
* `setup` succeeds.
* `prove` succeeds.
* `verify` succeeds.
* Mutating `y` to `82` fails verification.

## `examples/arithmetic_public_inputs`

```rust
fn main(x: Field, y: Field, out: pub Field) {
    assert(x * y + x + y == out);
}
```

`Prover.toml`:

```toml
x = "3"
y = "4"
out = "19"
```

Acceptance:

* Same as above.
* Public input order is stable.

## `examples/range_basic`

Only add after range checks are implemented.

```rust
fn main(x: u8, out: pub Field) {
    assert(x as Field == out);
}
```

Acceptance:

* Range opcode is either supported or clearly reported as unsupported.
* Once range support exists, valid witness proves and invalid witness fails.

---

# 14. Integration Test Matrix

Create integration tests that shell out to the CLI.

## Test: Full Happy Path

```text
nargo execute
noir-groth16 inspect
noir-groth16 setup --insecure-dev-mode
noir-groth16 prove
noir-groth16 verify
```

Expected:

```text
verify == true
```

## Test: Bad Public Input

1. Generate valid proof.
2. Modify `public_inputs.json`.
3. Run verify.

Expected:

```text
verify == false
```

## Test: Bad Proof

1. Generate valid proof.
2. Flip one byte in proof.
3. Run verify.

Expected:

```text
verify == false or deserialization error
```

## Test: Wrong VK

1. Generate proof for circuit A.
2. Verify using VK for circuit B.

Expected:

```text
verify == false
```

## Test: Unsupported Opcode

1. Compile a Noir circuit known to emit an unsupported opcode.
2. Run inspect.

Expected:

```text
unsupported_opcodes.length > 0
```

3. Run setup.

Expected:

```text
non-zero exit code
clear error message
```

---

# 15. Determinism and Circuit Hashing

Implement deterministic circuit hashing.

Hash should include:

```text
normalized ACIR opcodes
public input ordering
backend lowering version
curve
proving system
supported opcode semantics version
```

Use this hash in:

```text
metadata.json
proving key metadata
verifying key metadata
proof metadata if possible
```

Acceptance:

* Same circuit gives same hash.
* Changing public input order changes hash.
* Changing an opcode changes hash.
* Changing backend lowering version changes hash.

---

# 16. Diagnostics

Good errors are part of the product.

## Required Error Examples

Unsupported opcode:

```text
Unsupported ACIR opcode at index 17: BlackBoxFuncCall::Sha256

This backend does not support SHA256 yet.

Try:
  - use a circuit without SHA256, or
  - implement crates/acir-r1cs/src/gadgets/hash.rs, or
  - run `noir-groth16 inspect --artifact ...` to see full opcode coverage.
```

Missing witness:

```text
Missing witness value: witness 42

The circuit references witness 42, but it was not present in the witness file.
Regenerate the witness with `nargo execute`.
```

Version mismatch:

```text
Unsupported Noir/ACIR artifact version.

Supported:
  Noir: <documented version>
Found:
  <found version>

Pin nargo to the supported version or update acir-r1cs parsing.
```

---

# 17. Development Milestones

## Milestone 0 — Workspace Bootstrapping

Tasks:

* [ ] Create Rust workspace.
* [ ] Add crates.
* [ ] Add CLI skeleton.
* [ ] Add tracing/logging.
* [ ] Add README.
* [ ] Add `NOIR_VERSION.md`.
* [ ] Add CI with `cargo fmt`, `cargo clippy`, `cargo test`.

Acceptance:

```bash
cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

All pass.

---

## Milestone 1 — Artifact and Witness Parsing

Tasks:

* [ ] Create arithmetic Noir example.
* [ ] Generate artifact and witness.
* [ ] Add sanitized fixtures.
* [ ] Implement artifact parser.
* [ ] Implement witness parser.
* [ ] Implement field conversion.
* [ ] Implement `inspect`.

Acceptance:

```bash
noir-groth16 inspect --artifact tests/fixtures/arithmetic_square.json
```

Prints valid metadata and opcode summary.

---

## Milestone 2 — Arithmetic ACIR to R1CS

Tasks:

* [ ] Implement R1CS builder.
* [ ] Implement variable allocation.
* [ ] Implement linear expression lowering.
* [ ] Implement single multiplication lowering.
* [ ] Implement multiple multiplication lowering.
* [ ] Add unit tests for lowering.
* [ ] Add constraint satisfaction tests.

Acceptance:

* Arithmetic constraints pass with valid witness.
* Arithmetic constraints fail with invalid witness.
* Unsupported opcodes are reported clearly.

---

## Milestone 3 — Groth16 Setup / Prove / Verify

Tasks:

* [ ] Implement Arkworks `ConstraintSynthesizer`.
* [ ] Implement setup.
* [ ] Implement prove.
* [ ] Implement verify.
* [ ] Implement binary serialization.
* [ ] Implement public input JSON.
* [ ] Wire CLI commands.

Acceptance:

```bash
noir-groth16 setup --artifact ... --out ... --insecure-dev-mode
noir-groth16 prove --artifact ... --witness ... --proving-key ... --out ...
noir-groth16 verify --verifying-key ... --proof ... --public-inputs ...
```

Works for arithmetic examples.

---

## Milestone 4 — JSON Serialization and Developer UX

Tasks:

* [ ] Add `proof.json`.
* [ ] Add `verifying_key.json`.
* [ ] Add `metadata.json`.
* [ ] Add `--json` output for inspect.
* [ ] Add helpful error messages.
* [ ] Add docs.

Acceptance:

* All binary artifacts roundtrip.
* All JSON artifacts roundtrip.
* CLI errors are clear and actionable.

---

## Milestone 5 — Range and Boolean Support

Tasks:

* [ ] Implement boolean gadget.
* [ ] Implement bit decomposition.
* [ ] Implement range checks.
* [ ] Add range fixtures.
* [ ] Add property tests if practical.

Acceptance:

* Noir circuits using small unsigned integer types can prove if they only require supported range semantics.
* Invalid range witnesses fail.

---

## Milestone 6 — Bitwise Support

Tasks:

* [ ] Implement AND.
* [ ] Implement XOR.
* [ ] Add bitwise fixtures.
* [ ] Add tests against Rust native operations.

Acceptance:

* Noir circuits using basic bitwise operations prove and verify.
* Bad bitwise witnesses fail.

---

## Milestone 7 — Exporters

Tasks:

* [ ] Decide first external target.
* [ ] Implement verifying key export for that target.
* [ ] Implement proof calldata/export formatting.
* [ ] Add generated verifier tests if practical.

Initial preferred target:

```text
EVM BN254 Groth16 verifier
```

Acceptance:

* Exported verifier compiles.
* Exported proof/public inputs are accepted by generated verifier.
* Coordinate ordering and encoding are tested.

---

# 18. Security Requirements

This project handles cryptographic proving. Be conservative.

Rules:

* Do not claim production readiness until audited.
* Do not hide trusted setup risk.
* Do not use insecure randomness except behind `--insecure-dev-mode`.
* Do not silently accept unsupported opcodes.
* Do not silently reorder public inputs.
* Do not silently truncate field elements.
* Do not silently accept invalid points.
* Do not silently ignore deserialization failures.
* Do not generate EVM verifier calldata without tests.

Add this warning to README:

```text
This project is experimental. Do not use generated Groth16 parameters or proofs in production until the backend, lowering logic, serialization, and setup process have been independently audited.
```

---

# 19. Claude Execution Rules

Claude should execute this plan milestone by milestone.

## Do Not Skip

Claude must not skip:

* Tests.
* Error handling.
* Public input ordering.
* Unsupported opcode reporting.
* Metadata.
* Documentation of supported Noir version.

## When Blocked

If blocked by unclear Noir artifact format:

1. Inspect generated `target/*.json`.
2. Search local dependency docs.
3. Add a note to `docs/blockers.md`.
4. Implement a narrow parser for the current fixture.
5. Keep parsing isolated behind `artifact.rs`.

If blocked by unsupported ACIR crate APIs:

1. Do not rewrite the architecture.
2. Create local normalized types.
3. Parse into those types.
4. Continue with lowering.

If blocked by a black-box opcode:

1. Report it through `inspect`.
2. Add it to unsupported opcode tests.
3. Do not implement a fake placeholder constraint.

## Completion Criteria

The project is considered MVP-complete when this works end-to-end:

```bash
cd examples/arithmetic_square
nargo execute

noir-groth16 inspect \
  --artifact ./target/arithmetic_square.json

noir-groth16 setup \
  --artifact ./target/arithmetic_square.json \
  --out ./target/groth16 \
  --insecure-dev-mode

noir-groth16 prove \
  --artifact ./target/arithmetic_square.json \
  --witness ./target/witness.gz \
  --proving-key ./target/groth16/proving_key.bin \
  --out ./target/groth16/proof.bin

noir-groth16 verify \
  --verifying-key ./target/groth16/verifying_key.bin \
  --proof ./target/groth16/proof.bin \
  --public-inputs ./target/groth16/public_inputs.json
```

Expected final output:

```text
Proof verified: true
```

And these must pass:

```bash
cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

---

# 20. Non-Goals for MVP

Do not implement these in the first MVP:

* Full Noir opcode coverage.
* SHA256.
* ECDSA.
* Recursive proofs.
* Universal setup.
* Production MPC ceremony.
* GPU proving.
* WASM proving.
* Solidity verifier unless arithmetic MVP is already stable.
* Multiple Noir version support.
* A new Rust circuit DSL.

These are future extensions.

---

# 21. Future Roadmap

After MVP:

1. Expand ACIR opcode coverage.
2. Add range and bitwise support.
3. Add hash gadgets.
4. Add signature gadgets.
5. Add EVM verifier export.
6. Add Solidity calldata generation.
7. Add benchmark suite.
8. Add compatibility tests against another backend where possible.
9. Add ceremony/key import workflows.
10. Add audit-focused documentation.

---

# 22. Design Summary

This backend should be boring, explicit, and correct.

The important engineering asset is not the Groth16 call. Arkworks gives us that.

The important engineering asset is the lowering layer:

```text
Noir ACIR semantics -> deterministic R1CS constraints
```

Everything else exists to protect that layer:

```text
tests
fixtures
metadata
version pinning
public input ordering
clear unsupported opcode errors
serialization roundtrips
trusted setup warnings
```

Build the arithmetic MVP first. Then expand opcode coverage carefully.

