# ROADMAP.md — Path to a Complete Noir Groth16 Backend

This file extends `PLAN.md`. It assumes the MVP described in `PLAN.md`
through `LoweredAcirCircuit::circuit_hash` is shipped and currently green
(arithmetic + RANGE + Sha256Compression supported, 28 tests passing).
Everything below builds on that base.

## How to use this document

Work is organized into **six parallel workstreams** (`WS-A`..`WS-F`), each
containing numbered **steps**. Every step has:

* **Scope** — what to change, in one paragraph.
* **Deliverables** — concrete files / tests.
* **Acceptance** — what must be green when the step is "done".
* **Depends on** — prior steps that must land first.
* **Parallel?** — whether an agent can pick this up at the same time as
  other open work.

When in doubt about ordering, the rule is: **dependencies inside a workstream
are strict; across workstreams they are only declared where listed.**

### Recommended execution model

* **Solo**: walk WS-A → WS-B → (WS-C ‖ WS-D) → WS-E → WS-F in order.
* **Two agents**: agent 1 owns WS-B → WS-D (opcode coverage); agent 2 owns
  WS-A → WS-E (infra + exporters). Synchronize after WS-A.5 lands.
* **Many agents**: WS-A.1 must land first (CI gates the rest). Then
  WS-A.{2,3,4,5}, WS-B.{1,2,3,4,5}, and WS-D.{1,2,3,4} can all run in
  parallel after the prerequisites listed below. WS-C and WS-E.2 (Solana)
  need WS-A.5 to land first.

---

# WS-A — Foundations

Small, mostly-independent infrastructure work. Must land first because
everything else regresses against it.

## A.1 — Add CI

**Scope.** GitHub Actions workflow that runs `cargo fmt --check`,
`cargo clippy --workspace --all-targets -- -D warnings`,
`cargo test --workspace` on every push and PR. Cache `~/.cargo` and
`target/` keyed on `Cargo.lock`. Pin to `stable` Rust. Single OS
(`ubuntu-latest`) is fine for v1.

**Deliverables.**
* `.github/workflows/ci.yml`
* Status badges in `README.md`.

**Acceptance.**
* PR fails CI on a deliberate `cargo fmt` violation.
* PR fails CI on a deliberate `clippy::unused` warning.
* PR fails CI on a deliberate failing test.
* Cache survives across runs (verify by looking at build times on the
  second run of an unchanged PR).

**Depends on.** Nothing.

**Parallel?** Must land before any other PR is merged.

## A.2 — Cleanup pass

**Scope.** Remove dead scaffolding without changing behavior.

Specific items:
* Delete the `MissingValueExt` trait in `crates/acir-r1cs/src/r1cs_builder.rs`;
  call `Err(SynthesisError::AssignmentMissing)` directly in
  `maybe_witness_value`.
* Delete unused helpers: `has_witness`, `function_input_to_u32`,
  `word_zero`, `_ones_lc`, `_serde_round_trip`.
* Move `enforce_word_eq_var` from `gadgets::hash` to `gadgets::range`
  (where it lives semantically); keep a `pub use` re-export until callers
  are updated, then delete the re-export.

**Deliverables.** Edits to `r1cs_builder.rs`, `gadgets/hash.rs`,
`gadgets/range.rs`.

**Acceptance.** `cargo clippy -- -D warnings` clean. `cargo test
--workspace` still 28+ passing.

**Depends on.** A.1.

**Parallel?** Yes.

## A.3 — Stable circuit hashing

**Scope.** `LoweredAcirCircuit::circuit_hash` currently digests opcodes via
`format!("{op}")` — i.e. their `Display` impl, which is not a stability
contract across Noir releases. Replace the per-opcode digest with the
msgpack-compact bytes that `acir::circuit::Program::serialize_program`
produces. This is the same encoding nargo writes to disk, so it's stable
by construction.

**Deliverables.**
* Edit `gadgets`/`lower.rs` to compute the hash from
  `Program::serialize_program(&self.artifact.program)`.
* Add a test that asserts the hash for `arithmetic_square.json` is stable
  across runs and matches a hardcoded value.
* Add a test that swapping public-input order changes the hash.
* Add a test that an extra opcode changes the hash.

**Acceptance.**
* Same artifact → same hash, byte-identical across machines.
* Tests in `lower.rs` exercising the three change-detection rules above.

**Depends on.** A.1.

**Parallel?** Yes.

## A.4 — Bind Public Input ordering to a test matrix

**Scope.** Add fixtures that exercise non-trivial public input layouts:
* return values only (no public params)
* mixed public params + return values
* out-of-order witness indices for public params
* large public-input vectors (≥16)

For each, prove a known circuit and verify, asserting the
`public_inputs.json` order is what the verifier consumes.

**Deliverables.** 4 new `examples/` Noir programs + committed fixtures
under `tests/fixtures/`. Integration tests in
`crates/xark-cli/tests/end_to_end.rs`.

**Acceptance.** All 4 cases prove → verify true. Tampering with any single
public input → verify false.

**Depends on.** A.1.

**Parallel?** Yes.

## A.5 — Freeze the binary VK / proof formats

**Scope.** Document and pin the exact byte layout of `verifying_key.bin`
and `proof.bin`. This becomes the boundary for downstream consumers
(EVM verifier, Solana verifier). Add round-trip tests asserting that
saved fixtures still deserialize bit-exactly after future code changes.

Concretely:
* Commit a `verifying_key.bin` / `proof.bin` / `public_inputs.json` set
  for `arithmetic_square` under `tests/fixtures/groth16/`.
* Add a test in `groth16-backend` that reads them, re-verifies, and
  asserts a SHA-256 hash of the bytes matches a hardcoded value.
* Add a test that re-serializing the parsed VK and proof yields the same
  bytes (canonical).

**Deliverables.** Fixture files + tests in
`crates/groth16-backend/tests/serialization.rs`.

**Acceptance.** Hashes match. Bumping `ark-groth16` and breaking the
format → test fails clearly.

**Depends on.** A.1.

**Parallel?** Yes. Blocks WS-E (exporters).

---

# WS-B — Opcode coverage (lowering layer)

Each step here adds a new ACIR opcode to the supported set. All gadgets
already exist except where noted.

## B.1 — Wire `BlackBoxFuncCall::AND` and `XOR`

**Scope.** Noir emits these for `a & b` / `a ^ b` on integer types up to
64 bits. The gadgets in `gadgets::bitwise` are 32-bit. Generalize to
`num_bits`-bit (the opcode carries `num_bits: u32`), then dispatch from
`opcodes::blackbox::lower_black_box`.

For `num_bits > 64`, reject with a clear error referencing this file.

**Deliverables.**
* `gadgets::bitwise::and_n` / `xor_n` taking a width parameter.
* New dispatch arms in `lower_black_box`.
* New example: `examples/bitwise_basic` using `u32` AND + XOR.
* Integration tests for happy + tampered path.
* Update `OpcodeClass::is_supported` to include `"and"` and `"xor"`.

**Acceptance.** `xark inspect` reports the bitwise example with
`unsupported_opcode_count: 0`. End-to-end verify true.

**Depends on.** A.1, A.5.

**Parallel?** Yes.

## B.2 — Generalize range to arbitrary `num_bits`

**Scope.** Today `enforce_range` already accepts any `num_bits ≤ MAX_BITS`
(253). Add an explicit, tested upper bound and a clearer error for
out-of-range widths. Also add fixtures that exercise `u8`, `u16`, `u32`,
`u64` ranges.

**Deliverables.** Tests + 4 small Noir examples.

**Acceptance.** All four range widths prove and verify; out-of-band
witnesses fail at nargo execute time (already true) and out-of-band
direct ACIR fails at `is_satisfied` time.

**Depends on.** A.1.

**Parallel?** Yes.

## B.3 — Field-equality and constant-witness shortcuts

**Scope.** `function_input_to_var` currently allocates a fresh witness +
linear constraint for every `FunctionInput::Constant`. For black-boxes
that take many constants (e.g. Poseidon round constants are emitted as
constants in some Noir versions), this becomes wasteful. Add an alternate
return type that lets callers thread a constant `LinearCombination`
instead.

**Deliverables.** Refactor `function_input_to_var` to return an enum
`{ Variable(Variable, value), Constant(Fr) }`. Update RANGE and Sha256
call sites. No behavior change, only constraint count.

**Acceptance.** Constraint count for `sha256_basic.json` strictly
decreases (or is unchanged). All existing tests still pass.

**Depends on.** A.1.

**Parallel?** Yes.

## B.4 — Multi-function ACIR programs

**Scope.** `artifact.rs` currently rejects multi-function programs. Noir
emits multiple functions for recursion and some macro expansions. Add
support for the trivial case: programs with one entry function and N
inlined helper circuits, with no `Call` opcode. Reject programs that
actually use `Call` with the existing error.

**Deliverables.** Update `parse_artifact_bytes` to accept multi-function
programs but only synthesize `functions[0]`. Add a test fixture and assert
that helpers are reported in `inspect` JSON.

**Acceptance.** Multi-function fixture parses cleanly; the main function
proves and verifies; helpers appear in inspect output.

**Depends on.** A.1.

**Parallel?** Yes.

## B.5 — `Call` opcode (cross-circuit)

**Scope.** The hard variant of B.4: actually lower `Call`. Each callee
function becomes an inlined sub-R1CS; predicate gates the constraints.
Allocate inputs/outputs as witnesses, recurse the lowering, gate every
sub-constraint by `predicate`.

**Deliverables.** `lower::lower_call`, fixtures, tests.

**Acceptance.** A Noir program that uses an explicit `pub fn foo(...) {}`
call from `main` proves and verifies.

**Depends on.** B.4.

**Parallel?** No (sequential after B.4).

---

# WS-C — Memory and Brillig

The two big "unlocks any real Noir program" items. Both need design work
before code.

## C.1 — Design doc: `BrilligCall`

**Scope.** Write `docs/brillig.md` covering two strategies:
1. **Trust outputs**: ignore `BrilligCall` opcodes, trust that ACIR's
   surrounding `AssertZero` constraints fully pin the outputs. Verify
   this is sound by inspecting how Noir uses Brillig (it's a witness-only
   computation that must be re-derived by ACIR for soundness, by design).
2. **Re-execute**: run the Brillig VM in setup mode to derive outputs and
   bind them. Larger surface but bulletproof.

Pick (1) and document the soundness argument with explicit references to
Noir compiler invariants.

**Deliverables.** `docs/brillig.md` with the decision and rationale.

**Acceptance.** Reviewed and signed off (out-of-band).

**Depends on.** A.1.

**Parallel?** Yes.

## C.2 — Implement `BrilligCall` (trust-outputs)

**Scope.** Per C.1: accept `BrilligCall` opcodes by **binding the declared
output witnesses to whatever value the witness map already contains**,
then doing nothing else. Add an aggressive integration test asserting
that if any output witness is *missing* from the witness map, proving
fails clearly.

**Deliverables.** Lowering arm in `lower_black_box`. Update
`OpcodeClass::is_supported`. Test fixture using a Noir program that
emits Brillig (e.g. unconstrained `if-else` with hint computation).

**Acceptance.** Real Noir program with `// Safety: ` Brillig calls proves
and verifies; tampering with any constrained witness fails verify.

**Depends on.** C.1, A.5.

**Parallel?** No.

## C.3 — Design doc: `MemoryOp` / `MemoryInit`

**Scope.** Write `docs/memory.md` covering R1CS-friendly random-access
memory: array allocation, fixed-length read, fixed-length write. For
constant indices, lower directly via `AssertZero`. For variable indices,
use a permutation-argument-style memory check (selector polynomial /
indexed lookup). Decide whether to ship constant-index-only first
(quick win) or invest in full variable-index support (slow, requires
extra precommittments).

Recommend: constant-index-only ships in C.4, variable-index lookup ships
in C.5 (separate step) so the easy circuits get unblocked fast.

**Deliverables.** `docs/memory.md`.

**Depends on.** A.1.

**Parallel?** Yes.

## C.4 — Constant-index memory

**Scope.** Lower `MemoryInit { block_id, init }` by recording the witness
indices for each slot. Lower `MemoryOp { block_id, op }` for `op.index`
*that is a constant expression* by emitting a direct equality constraint
to the matching init witness. Reject variable-index ops with a clear
error referencing C.5.

**Deliverables.** New `gadgets::memory` module. Lowering arm. Tests with
fixed-index Noir programs.

**Acceptance.** Programs with constant-index array access prove and
verify. Variable-index access fails with a clear "see C.5" error.

**Depends on.** C.3, A.5.

**Parallel?** Yes.

## C.5 — Variable-index memory

**Scope.** Implement variable-index reads via a selector argument: for
read `out = arr[i]`, allocate per-slot selectors `s_j`, enforce
`sum(s_j) = 1`, each `s_j * (i - j) = 0`, and `out = sum(s_j * arr[j])`.
Writes are similar. Cost: `O(N)` constraints per access.

**Deliverables.** Variable-index path in `gadgets::memory`. Fixtures with
variable-index access. Constraint-count benchmarks.

**Acceptance.** Programs with variable-index array access prove and
verify. Document the per-access constraint cost in `docs/memory.md`.

**Depends on.** C.4.

**Parallel?** No.

---

# WS-D — Cryptographic gadgets

After WS-B.1 (bitwise) ships, these all become independent of each other
and can be picked up by separate agents.

## D.1 — Keccak-f[1600] permutation

**Scope.** Implement the Keccak-f[1600] permutation as 24 rounds over a
5x5 array of 64-bit lanes. Reuses 64-bit XOR / AND / NOT / ROT gadgets
(generalize from `gadgets::bitwise` which is currently 32-bit).

**Deliverables.** `gadgets::hash::keccakf1600`. Test against
[`keccak` crate](https://crates.io/crates/keccak)'s KAT on the
all-zeros block. Wire into `BlackBoxFuncCall::Keccakf1600`. Example
program + fixtures.

**Acceptance.** End-to-end Keccak Noir program proves and verifies. Bit
flipping any output word → verify false.

**Depends on.** A.5, B.1.

**Parallel?** Yes.

## D.2 — Blake2s

**Scope.** Implement the Blake2s compression (10 rounds, 32-bit lanes).
The plan called out that Noir's `BlackBoxFuncCall::Blake2s` takes a
variable-length input + outputs 32 bytes. Probably means we also need to
implement Blake2s *padding* in the gadget (verify against Noir's
implementation first).

**Deliverables.** `gadgets::hash::blake2s`. Test against
`blake2` crate KAT (`b"abc"` → fixed digest). Wire into
`BlackBoxFuncCall::Blake2s`. Example program + fixtures.

**Acceptance.** End-to-end Blake2s Noir program proves and verifies.

**Depends on.** A.5, B.1.

**Parallel?** Yes.

## D.3 — Blake3

**Scope.** Same as D.2 but Blake3. The compression function is similar
to Blake2s; tree structure differs. Decide first whether Noir emits
single-chunk or multi-chunk hashes (probably single for short inputs,
multi for long).

**Deliverables.** `gadgets::hash::blake3`. KAT test. Wire into the
opcode. Example + fixtures.

**Acceptance.** End-to-end Blake3 Noir program proves and verifies.

**Depends on.** A.5, B.1.

**Parallel?** Yes.

## D.4 — Poseidon2 permutation

**Scope.** This is the only field-native hash, so it doesn't need bit
decomposition. Implement Poseidon2 over BN254 Fr with the same round
constants and matrix Noir uses. **Critical**: cross-check parameters
against Noir's `BlackBoxFuncCall::Poseidon2Permutation` semantics — bit
endianness, MDS matrix, round constant order are easy to get wrong.

**Deliverables.** `gadgets::hash::poseidon2`. KAT test using values from
Noir's own test suite. Wire into the opcode. Example + fixtures.

**Acceptance.** End-to-end Poseidon Noir program proves and verifies.
Document the parameter set in `docs/poseidon-params.md`.

**Depends on.** A.5.

**Parallel?** Yes.

## D.5 — Embedded curve add + MSM (Grumpkin)

**Scope.** Noir's `BlackBoxFuncCall::EmbeddedCurveAdd` and
`MultiScalarMul` work over Grumpkin (the curve whose base field is BN254
Fr). We need EC point arithmetic in R1CS over Grumpkin. Use Arkworks'
short Weierstrass operations adapted into constraints — or write the
constraints by hand: `(x3, y3) = (x1, y1) + (x2, y2)` with separate
cases for doubling vs addition.

This is a substantial gadget; budget 2-3 PRs.

**Deliverables.** `gadgets::curve::{ec_add, ec_double, scalar_mul,
multi_scalar_mul}`. Tests against arkworks Grumpkin native ops. Wire
into the two opcodes.

**Acceptance.** End-to-end Schnorr-style verification using
EmbeddedCurveAdd / MSM proves and verifies.

**Depends on.** A.5.

**Parallel?** Yes (but big).

## D.6 — ECDSA-secp256k1 / secp256r1

**Scope.** The biggest single gadget. ECDSA verification over secp256k1
requires:
* 256-bit modular arithmetic over the curve's base field Fq (≠ BN254 Fr,
  so this is foreign-field arithmetic).
* Point operations on secp256k1.
* Hash-to-scalar (the `e` value).
* Scalar inversion mod `n`.
* Two scalar muls + one EC addition.

Roughly 60k–150k constraints per verification depending on optimization.
Probably 3-4 PRs.

**Deliverables.** `gadgets::ecdsa::{secp256k1, secp256r1}`. KAT test
against a known signature. Wire into both opcodes. Example program
verifying a real Bitcoin/Ethereum-style signature.

**Acceptance.** End-to-end ECDSA Noir program proves and verifies.

**Depends on.** A.5, B.1, D.4 (for hashing if needed).

**Parallel?** Yes.

## D.7 — AES-128 encryption

**Scope.** AES-128 single-block encryption. 10 rounds; each round is
SubBytes (8-bit S-box) + ShiftRows + MixColumns + AddRoundKey. S-box is
the painful bit — typically implemented as a 256-entry lookup, which in
R1CS becomes either:
* a polynomial interpolation (very expensive), or
* a "value is one of 256 known constants" witness gadget.

**Deliverables.** `gadgets::aes::aes128_encrypt`. KAT against NIST test
vectors. Wire into `BlackBoxFuncCall::AES128Encrypt`.

**Acceptance.** End-to-end AES Noir program proves and verifies.

**Depends on.** A.5, B.1.

**Parallel?** Yes.

## D.8 — RecursiveAggregation

**Scope.** Stub for now: explicitly reject with a clear error explaining
that recursive Groth16 verification needs a second curve (BN254 inside
itself doesn't form a cycle). Could be implemented later with a cycle of
curves (e.g. BLS12-377 / BW6-761) but that's its own multi-month effort.

**Deliverables.** Explicit error in `lower_black_box`. Add to docs.

**Acceptance.** Programs with RecursiveAggregation reject cleanly.

**Depends on.** A.1.

**Parallel?** Yes.

---

# WS-E — Verifier exports

These produce on-chain verifiers for proofs generated by xark. Both
exports consume the **frozen** VK + proof format from A.5.

## E.1 — EVM Solidity verifier

**Scope.** Generate a single-file Solidity contract `Verifier.sol`
containing the VK as constants plus a `verifyProof(uint[2] a, uint[2][2] b,
uint[2] c, uint[N] inputs)` function. Use the standard Ethereum BN254
precompiles (`0x06` G1add, `0x07` G1mul, `0x08` pairing). VK constants
should match the `verifying_key.json` schema.

Approach: copy the template from a reference like the snarkjs / Tornado
Solidity verifier and have xark fill in constants + N-public-input
arity.

**Deliverables.**
* `crates/groth16-backend/src/evm.rs` template + codegen.
* CLI `xark export evm --verifying-key X --out Verifier.sol`.
* A Foundry/Hardhat smoke test runs the exported verifier on a real
  proof and confirms it returns `true`. Commit the test under
  `tests/evm/` with a README on how to run it (since Foundry isn't part
  of normal `cargo test`).

**Acceptance.** Exported `Verifier.sol` compiles with `solc 0.8.x`.
Foundry test passes against a proof produced by `xark prove`.
Tampered public input → revert / returns false.

**Depends on.** A.5.

**Parallel?** Yes.

## E.2 — Solana verifier (NEW)

**Scope.** Solana has BN254 precompiles via the `alt_bn128` syscalls:
* `sol_alt_bn128_addition` (G1 + G1)
* `sol_alt_bn128_multiplication` (G1 * scalar)
* `sol_alt_bn128_pairing` (n × (G1, G2) → bool)

Build a reusable on-chain Groth16 verifier program plus a host-side
exporter that produces VK + proof + public-input bytes in the on-chain
format.

**Important serialization details.**
* Solana's `alt_bn128` uses Ethereum-compatible uncompressed big-endian
  encoding: G1 = 64 bytes (`x || y`), G2 = 128 bytes
  (`x.c1 || x.c0 || y.c1 || y.c0` — note the c1/c0 order!).
* Pairing input = `n × 192 bytes` (G1 + G2 pairs).
* Scalars are 32 bytes BE.

Pairing check to evaluate on-chain:
```
e(A, B) * e(α, β)^{-1} * e(vk_x, γ)^{-1} * e(C, δ)^{-1} = 1
```
i.e. `e(-A, B) * e(α, β) * e(vk_x, γ) * e(C, δ) = 1` after negating
`A` on G1. `vk_x = ic[0] + Σ inputs[i] * ic[i+1]`, computed via the
addition + multiplication syscalls.

**Deliverables.** Split this into four sub-steps:

### E.2.a — Encoding library

A `solana-format` module in `crates/groth16-backend/src/solana.rs` that
serializes G1Affine, G2Affine, and Fr to Solana/Ethereum format. Unit
tests against known points.

* G2 byte order: arkworks gives `(c0, c1)` for Fq2 internally; Solana
  syscalls expect `(c1, c0)`. Write this difference in a comment and a
  test.
* G1 negation: `y → -y mod p`. Also unit-tested.

**Acceptance.** Round-trip via `ark_serialize` → Solana format → back to
Arkworks via parse-from-syscall-format → identical point.

### E.2.b — On-chain verifier program

A new crate at `crates/xark-solana-verifier/` containing a Solana
program (BPF). Entry point reads (VK bytes, proof bytes, public inputs)
from instruction data (or a PDA account, configurable later) and runs
the Groth16 check using the syscalls.

Structure:
* `process_instruction(...) -> ProgramResult`
* `verify_groth16(vk: &VkBytes, proof: &ProofBytes, inputs: &[FrBytes])
  -> Result<bool>`
* Use `solana-program` `^1.18` (or current stable).
* No allocations beyond `Vec<u8>` for pairing input.

VK arity is parameterized: the program reads `num_public_inputs` from
the VK bytes and validates `inputs.len() == num_public_inputs`.

**Acceptance.**
* `cargo build-sbf` (or `cargo build-bpf`) produces a `.so`.
* `solana-program-test` integration test deploys the program in a local
  validator, calls `verify_groth16` with a real `arithmetic_square`
  proof, and asserts success.
* Tampered public input → returns `Err(InvalidArgument)` (or returns
  false and the test asserts the error).

### E.2.c — Exporter and CLI

CLI:
```
xark export solana \
  --verifying-key target/groth16/verifying_key.bin \
  --proof        target/groth16/proof.bin \
  --public-inputs target/groth16/public_inputs.json \
  --out          target/solana/
```

Output:
* `verifying_key.solana.bin` — VK in Solana on-chain format.
* `proof.solana.bin` — proof in Solana on-chain format (with `A` already
  negated, so the on-chain code doesn't need to do it).
* `public_inputs.solana.bin` — concatenated 32-byte BE field elements.
* `client_call_example.ts` (or `.rs`) — a Solana client snippet showing
  how to assemble the instruction.

**Acceptance.** Files round-trip through E.2.b's verifier and verify
`true`. CLI integration test parallel to the existing EVM test.

### E.2.d — End-to-end harness

Wire E.2.a through E.2.c into a `cargo test --workspace` integration
test that:
1. Compiles `xark-solana-verifier` (skip if `cargo build-sbf` is
   unavailable, with a clear warning).
2. Generates Groth16 keys + proof for `arithmetic_square`.
3. Runs the exported verifier inside `solana-program-test`.
4. Asserts `Proof verified: true`.

Add a CI job (separate workflow file) that runs this on PRs touching
`crates/xark-solana-verifier/` or `crates/groth16-backend/src/solana.rs`.

**Acceptance.** Test passes locally and in CI on a clean checkout.

**Depends on.** E.2.a → E.2.b → E.2.c → E.2.d.

**Parallel?** E.2.a + E.2.b can be done in parallel by one agent each;
E.2.c needs E.2.a; E.2.d needs everything.

---

# WS-F — Production setup

The "you can ship this in production" workstream. Smallest WS by line
count but has the highest review burden.

## F.1 — Powers of Tau import

**Scope.** Accept a Powers of Tau transcript (the standard ".ptau" /
".ph1" format used by snarkjs and Tornado) and run the circuit-specific
phase 2 contribution from it. Output keys carry
`metadata.setup_mode = "phase2-from-ptau"` and `production_safe = true`.

**Deliverables.**
* Parser for `.ptau` files (probably reuse a crate; if no good one
  exists, write one).
* Phase 2 circuit-specific contribution in `groth16-backend::setup`.
* CLI flag: `--ptau-file <path>` (mutually exclusive with
  `--insecure-dev-mode`).
* Test against a known-good `.ptau` file (commit a small one or fetch
  via CI).

**Acceptance.** Keys produced from a real ceremony transcript verify a
proof identically to dev-mode keys. Metadata reflects the real source.

**Depends on.** A.5.

**Parallel?** Yes.

## F.2 — MPC ceremony driver

**Scope.** A binary subcommand that runs a phase 2 MPC ceremony: emit
a contribution, accept other parties' contributions, verify the
transcript, output final keys.

**Deliverables.** New `xark ceremony {init, contribute, verify,
finalize}` commands. Documentation in `docs/ceremony.md`.

**Acceptance.** A ceremony with 3 contributors produces keys that
verify a real proof.

**Depends on.** F.1.

**Parallel?** No.

## F.3 — Production randomness audit

**Scope.** Replace deterministic seeds in `setup` and `prove` with OS
randomness for non-dev paths. Add a `--deterministic-rng <seed>` flag
gated behind `--insecure-dev-mode` for reproducible test artifacts.

**Deliverables.** RNG plumbing changes. Tests asserting two consecutive
prove invocations produce different proofs of the same statement (which
both verify).

**Acceptance.** No fixed seeds outside test code.

**Depends on.** A.1.

**Parallel?** Yes.

## F.4 — Security review checklist

**Scope.** Write `docs/security.md` walking every constraint we emit
and arguing for soundness: range, bitwise, add-mod-32, SHA-256, etc.
List known unaudited paths.

Not a code change, but a release-gating doc.

**Deliverables.** `docs/security.md`.

**Acceptance.** Reviewed (out-of-band).

**Depends on.** Everything in WS-B, WS-C, WS-D landed.

**Parallel?** No.

---

# Cross-cutting: benchmarks

After WS-B + WS-D ship, add `cargo bench`-based benches in a new
`benches/` directory at the workspace root. Cover:

* SHA-256 compression: setup time, prove time, constraint count.
* Range check (32-bit and 64-bit).
* Bitwise AND / XOR (32-bit and 64-bit).
* End-to-end `arithmetic_square` and `sha256_basic` prove time.

Track regressions in CI by saving the criterion baseline.

This is not blocking but should land before WS-E ships, so the EVM and
Solana verifier benchmarks have a baseline to compare against.

---

# Ordering summary (graph)

```
A.1 ──┬─→ A.2,  A.3,  A.4,  A.5
      │
      ├─→ B.1 ──→ B.2,  B.3,  B.4 ──→ B.5
      │     │
      │     └─→ D.1, D.2, D.3, D.6 (D.4, D.5, D.7 only need A.5)
      │
      ├─→ C.1 ──→ C.2
      │
      ├─→ C.3 ──→ C.4 ──→ C.5
      │
      ├─→ A.5 ──→ E.1
      │     └──→ E.2.a + E.2.b ──→ E.2.c ──→ E.2.d
      │
      └─→ F.1 ──→ F.2,  F.3, F.4 (last)
```

# Tracker

| Step | Owner | Status |
|------|-------|--------|
| A.1  |       | done |
| A.2  |       | done |
| A.3  |       | done |
| A.4  |       | done |
| A.5  |       | done |
| B.1  |       | done |
| B.2  |       | done (MAX_BITS already enforced) |
| B.3  |       | done (RANGE constant fast path + helper for future gadgets) |
| B.4  |       | done |
| B.5  |       | done (predicate=1 inlining + witness shifting + nested calls via running offset counter; `nested_calls` 2-level fixture proves and verifies) |
| C.1  |       | done |
| C.2  |       | done |
| C.3  |       | done |
| C.4  |       | done |
| C.5  |       | done (variable-index reads + writes via selector-gated per-slot shadow update) |
| D.1  |       | done |
| D.2  |       | done |
| D.3  |       | done (single + multi-chunk via PARENT-compression binary tree) |
| D.4  |       | done |
| D.5  |       | done |
| D.6  |       | done. secp256k1: ~3.6M constraints/verify (GLV + fixed-base 4-bit comb on G + 2-way joint Strauss-Shamir on `u2·Q`). secp256r1: ~5.4M (comb on G + 4-bit windowed double-and-add on Q — no useful endomorphism). Both now also enforce `(Q.x, Q.y)` on-curve and `r, s ∈ [1, n-1]`. Original schoolbook impl was ~17–18M; optimisation history is in the rustdoc on `report_ecdsa_verify_*_baseline` tests. |
| D.7  |       | done |
| D.8  |       | done (clearer error referencing curve cycle limitation) |
| E.1  |       | done |
| E.2.a|       | done |
| E.2.b|       | done |
| E.2.c|       | done |
| E.2.d|       | done (Mollusk on-chain, processor!-macro path) |
| F.1  |       | done (parser + admissibility check + phase-2 contribution with γ/δ derivation from caller seed; CLI flag `--ptau-file`) |
| F.2  |       | done (multi-contributor δ chain with Schnorr proofs + pairing consistency checks; `xark ceremony {init,contribute,verify,finalize}` CLI; 5 tests pass) |
| F.3  |       | done |
| F.4  |       | done |
