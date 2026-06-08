# Audit status

> **Has xark been externally audited?** No.

This document is the canonical place to track what *has* been internally
reviewed, what's known to be load-bearing for soundness, and what an
external auditor should focus on first. Pairs with
[`security.md`](security.md), which walks the per-gadget soundness claims,
and [`FORMAL_VERIFICATION_PLAN.md`](FORMAL_VERIFICATION_PLAN.md), which
tracks the formal-verification roadmap.

---

## What's been reviewed internally

### Documentation
* [`security.md`](security.md) — per-gadget soundness sketches written
  alongside each gadget's implementation. Authored by the same person
  who wrote the gadget, so it should be read as an *assertion* of
  soundness rather than independent corroboration.
* [`brillig.md`](brillig.md) — soundness argument for the
  trust-outputs Brillig lowering strategy. Relies on a property of
  Noir's compiler (the `(SI)` invariant), now *machine-checked at
  artifact-load time* by
  `crates/acir-r1cs/src/opcodes/brillig_check.rs` (see "Brillig
  output-pinning check" below).
* [`memory.md`](memory.md) — soundness of the selector-argument
  variable-index memory lowering.
* [`trusted-setup.md`](trusted-setup.md) — the phase-2 MPC ceremony
  driver and the admissibility checks on imported `.ptau` transcripts.
* [`reproducible-build.md`](reproducible-build.md) — pinned-toolchain
  build flow for the on-chain verifier `.so` (`xark_verifier_reference_program.so`),
  with a hash-verification step in CI.

### Test suite
~250 unit + integration tests across `crates/tests/tests/` including:

* **KAT cross-checks** against `k256`, `p256`, `sha2`, `keccak`,
  `blake2`, `blake3`, `aes`, `ark-grumpkin`.
* **Tampering tests**: every gadget's e2e test mutates the witness and
  verifies the constraint system reports unsatisfied.
* **Adversarial gadget tests** (`differential_gadgets.rs`, 15/15 pass)
  — every committed gadget covered with all-zero, all-FF, alternating,
  near-modulus, boundary-length adversarial inputs against published
  reference crates.
* **NIST/RFC official vectors** (`nist_rfc_vectors.rs`, 23/23 pass +1
  ignored) — FIPS 180-4 §B (SHA-256), FIPS 202 §C (SHA-3), RFC 7693 §B
  (BLAKE2s), official BLAKE3 `test_vectors.json`, FIPS 197 §B + CAVP
  (AES-128).
* **Determinism propagation** (`determinism_propagation.rs`,
  CI-gated by `.github/workflows/determinism-prop.yml`) — a Lean-style
  R1CS under-constraint analyser over BN254 `Fr` (Layer-B / track 1).
* **Lean ↔ R1CS bridge** (`lean_r1cs_bridge.rs`, 11/11 pass) — for
  each gadget, materialises the R1CS, walks every row, classifies it
  into one of five Lean-modeled shapes (Boolean / MulCSingle / MulCEmpty /
  XorAux / Linear) and asserts zero unclassified rows. Pins total
  constraint counts (SHA-256 = 52 768, Keccak-f[1600] = 250 482, etc.)
  so any drift forces a Lean-side reload.
* **Bitwuzla bit-equivalence** (CI-gated by `.github/workflows/bitwuzla.yml`)
  — QF_BV equivalence proofs for SHA-256 compression, AES-128 block
  encrypt, BLAKE3 compression, BLAKE2s compression, Keccak-f[1600].
* **Brillig output-pinning** (`brillig_pinning.rs`, 3/3 pass) — runs
  `check_brillig_outputs_pinned` across every fixture; asserts the
  `(SI)` invariant holds and explicitly cites the Lean theorem
  `Formal.Brillig.brillig_lowering_vacuous_sound` whose hypothesis the
  runtime check discharges.
* **Ceremony enforcement** (`ceremony_enforcement.rs`, 10/10 pass) —
  pins all `CeremonyError` rejection paths: Schnorr-PoK, transcript
  hash chain, δ-consistency between G1/G2, dev-mode guards.
* **cargo-fuzz smoke** (CI-gated by `.github/workflows/fuzz.yml`) —
  short-interval fuzz over artifact parser, witness parser, and
  ACIR→R1CS lowering. Production fuzzing campaigns are CPU-weeks; CI
  is a regression guard.

### Lean 4 / mathlib formal proofs (`formal/`)

Layer-B per-gadget soundness, plus a large fraction of Layer-A and the
ACIR meta-theorem. CI-gated by `.github/workflows/lean.yml`; the
axiom check rejects any proof depending on `sorryAx`.

Coverage (theorem names → modules):

* **Field primitives** — `boolean_sound`, `range_unique`, `bits_unique`
  (`Formal.Gadgets`).
* **Bitwise** — `and_sound`, `xor_sound`, `not_sound`, `xor_n_parity_*`,
  `add_mod_32_*` (`Formal.Bitwise` + `Formal.Arith`).
* **SHA-256 structural** — `rotr_sound`, `shr_sound`, `Ch_bit_sound`,
  `Maj_bit_sound`, `MessageScheduleStep_iff` (`Formal.Sha256`).
* **Curve** — Grumpkin `ec_add_in_circuit_sound` (full algebraic
  closure: generic + doubling + inverse + on-curve + selector mux),
  `secp256k1` / `secp256r1` closures (`Formal.Curve / Secp256k1 / Secp256r1`).
* **Concrete point groups** — `Secp256k1Point` (`Formal.Secp256k1Group`),
  `Secp256r1Point` (`Formal.Secp256r1Group`), `GrumpkinPoint`
  (`Formal.GrumpkinGroup`). All three are mathlib `WeierstrassCurve.Affine.Point`
  aliases inheriting `AddCommGroup` via `inferInstance`. Three trusted
  primality axioms (one per curve's base field) — see
  "Trusted base additions" below.
* **Poseidon2** — `poseidon_permutation_determined`,
  `poseidon2_bn254_determined` (`Formal.Poseidon` + `Formal.Poseidon2Bn254`).
* **ECDSA scalar mult** — `ladder_step_correct`, `ladder_correct`,
  `ladder_determinism` (`Formal.Ecdsa`).
* **Non-native arithmetic** — `mul_mod_via_Fr_limbwise_constraints`
  (the full ℕ + Fr no-wrap chain for the secp256k1 base/scalar-field
  product) (`Formal.NonNative`).
* **ECDSA verifier wrapper** — `ecdsa_verify_compose` (parametric over
  `G : AddCommGroup`), specialised to secp256k1/r1/Grumpkin
  (`Formal.EcdsaVerify` + the per-curve `*Group` modules).
* **GLV** — `glv_sum_eq`, `glv_via_endomorphism`,
  `glv_endomorphism_correct` (abstract eigenvalue extension over any
  cyclic subgroup), `glv_endomorphism_correct_secp256k1` (concrete φ for
  secp256k1) (`Formal.Glv` + `Formal.Secp256k1Group`).
* **Comb / Strauss-Shamir** — `windowed_scalar_mul_sound`,
  `joint_strauss_shamir_correct` (`Formal.AdvancedGadgets`).
* **ACIR → R1CS meta-theorem** — linear `AssertZero` (full bidirectional
  iff), mul-term `AssertZero` (`full_satisfied_via_list_aux` +
  `full_satisfied_from_per_mul_rows`), `BlackBoxFuncCall` dispatch
  (`lowerBlackBox_sound`), cross-circuit Call relabel +
  predicate-combined gating (`lowerCall_outputs_bound`,
  `combine_predicates_*`, `gated_under_combined_predicate_sound`),
  memory-scope namespace disjointness (`memory_scope_splice_fresh`),
  heterogeneous opcode pool + per-opcode row-level soundness
  (`AcirOpcode` + `lowerAcirOpcode` + `lowerAcirOpcode_sound_no_full`
  + `lowerAcirOpcode_full_sound`) (`Formal.AcirLowering` +
  `Formal.CallInlining`).
* **Per-opcode end-to-end wrappers** — `lower<X>_sound` for SHA-256,
  Keccak, BLAKE2s, BLAKE3, AES-128, Poseidon2, EmbeddedCurveAdd,
  MultiScalarMul, Ecdsa-secp256k1/r1. Each one has a concrete Lean
  round-step transcribed from the FIPS / RFC spec (no `opaque`s) and a
  substantive `<X>_iter_of_rel` composition theorem that collapses the
  snapshot history into the spec relation by induction over rounds
  (`Formal.Wrappers`).
* **Bitwuzla composition** — `<X>_round_pinned` and `<X>_closed_chain`
  per hash/cipher: combines the substantive wrapper with the QF_BV
  bit-equivalence axiom (one per gadget; each axiom's docstring cites
  the specific Bitwuzla harness file) into a single audit-readable
  chain (`Formal.BitwuzlaCompose`).
* **Allocation bookkeeping** — `AllocState`, `alloc_witness_idempotent`,
  `alloc_witness_injective`, `AllocState.alloc_preserves_invariant`,
  `read/write_const_index_correct` (`Formal.Bookkeeping`).
* **Public-input flow** — `public_input_projection_consistent` +
  `buildInstance_eq_w_on_pub` (canonical-construction discharge) +
  `alloc_state_pins_public_inputs` (bookkeeping bridge)
  (`Formal.AdvancedGadgets`).
* **Verifier (Layer-A) — Kani** — canonicality, fail-closed (every
  structural error path returns `Err` ≠ `Ok(true)`), strict
  non-malleability, arity, plus the recently-added totality with
  curve-op stubs (`totality_verify_groth16`, `totality_verify_proof_only`)
  and pairing operand-assembly (`pairing_operand_assembly`); see
  `#[cfg(kani)] mod proofs` in `crates/verifier/src/verifier.rs` and
  the CI workflow at `.github/workflows/kani.yml`.

The `lean.yml` axiom check enumerates **all** of these theorem names
and rejects any proof depending on `sorryAx`. The standard mathlib
axioms (`propext`, `Classical.choice`, `Quot.sound`) are allowed.

### Trusted base additions (axiomatised)

Five axioms are declared in `formal/`, each documented at its
declaration site:

| Axiom | Scope | Why |
|---|---|---|
| `secp256k1_p_prime : Fact (Nat.Prime secp256k1_p)` | 256-bit prime | Lean's kernel can't `decide` 256-bit primality; verifiable via `openssl prime`. |
| `secp256r1_p_prime : Fact (Nat.Prime secp256r1_p)` | 256-bit prime | Same as above. |
| `bn254_r_prime : Fact (Nat.Prime r)` | 254-bit prime | BN254 `Fr` modulus; used by `GrumpkinPoint` and the existing field instances. |
| `secp256k1_phi_preserves_nonsingular` | curve automorphism | `φ(x,y) = (β·x, y)` preserves the secp256k1 nonsingularity predicate. Algebraically follows from `β³ = 1`; axiomatised so the concrete `secp256k1_phi` definition lands. |
| `Bitwuzla<X>Equivalent` (5 axioms, one per hash/cipher) | bit-equivalence | Each is discharged by a specific `crates/tests/tests/bitwuzla_*.rs` harness via `unsat`. The axiom's docstring cites the harness path. |

These are the only `axiom` declarations in `formal/`. No `sorry` /
`sorryAx`. The `lean.yml` axiom check prints `#print axioms` for every
load-bearing theorem and fails CI if any depends on `sorryAx`.

This is **not** an external audit. Until an external firm has reviewed
the code, the README's "experimental — do not use in production" label
stays.

---

## Where an external auditor should start

Listed in rough order of "biggest blast radius if wrong":

### 1. Non-native arithmetic over secp curves (`gadgets/ecdsa.rs`)

The single largest soundness surface. Every ECDSA proof depends on the
correctness of:

* `bigint256_mul_mod` — limb-by-limb non-native multiplication with
  prover-aided quotient. Soundness now mechanised in
  `Formal.NonNative.mul_mod_via_Fr_limbwise_constraints` (the full
  ℕ + Fr no-wrap chain over `n = 4, β = 2^64`).
* `sub_mod` — the direct subtraction form
  (`a − b + k·m − c = 0`, `k ∈ {0, 1}`).
* `inv_mod` — modular inverse via `a · a_inv = 1`. Reduces to
  `mul_mod`'s correctness plus a non-zero check on `a`.
* `enforce_on_curve` — `y² = x³ + a·x + b mod p`. Mechanised for
  secp256k1 (`Formal.Secp256k1.enforce_on_curve_secp256k1_sound`),
  secp256r1, and Grumpkin.
* `enforce_in_range_one_to_n` — `r, s ∈ [1, n − 1]`. Without it, a
  malicious prover could exploit the `inv_mod(s)` step.
* GLV decomposition (`glv_decompose_in_circuit`) — proves
  `k = k1 + λ·k2 (mod n)` with `|k1|, |k2| < 2^129`. Algebraic kernel
  proven (`Formal.Glv.glv_via_endomorphism` +
  `glv_endomorphism_correct`); concrete `secp256k1_phi` definition
  + eigenvalue computation are documented in
  `Formal.Secp256k1Group` (the homomorphism + eigenvalue proofs are
  the residual obligations for full discharge).
* The fixed-base comb tables for `u1·G` — algebraic core proven
  (`Formal.AdvancedGadgets.windowed_scalar_mul_sound`); the comb-row-2
  doubling exception is in scope of the same proof.

### 2. Brillig trust-outputs assumption (`opcodes/brillig.rs`, `docs/brillig.md`)

`BrilligCall` outputs are allocated as fresh witnesses with **no**
in-circuit constraints. Soundness rests on the `(SI)` invariant: every
Brillig output must be pinned by surrounding ACIR constraining opcodes.

This is now mechanically checked at artifact-load time by
[`opcodes/brillig_check.rs`](../crates/acir-r1cs/src/opcodes/brillig_check.rs)
and exposed via the CLI `xark inspect --strict` flag. The integration
test `crates/tests/tests/brillig_pinning.rs` asserts the check holds
across every committed fixture and explicitly cites the Lean theorem
`Formal.Brillig.brillig_lowering_vacuous_sound` whose hypothesis the
runtime check discharges. The Lean theorem itself is sorry-free.

An auditor should:

* Verify the analyser correctly identifies *all* referencing opcodes,
  including newly-added variants of `BlackBoxFuncCall` upstream.
* Construct adversarial ACIR artifacts where a Brillig output is **not**
  pinned and confirm `check_brillig_outputs_pinned` flags them.

### 3. Universal predicate gating (`r1cs_builder.rs::enforce_gated`)

The e-aux trick: under an active call-site predicate `p`, every
`A · B = C` becomes `A · B = C + e` plus `p · e = 0`. Mechanised in
`Formal.Predication.enforce_gated_sound` (sorry-free; standard mathlib
axioms only) and combined with cross-circuit `Call` inlining in
`Formal.CallInlining.gated_under_combined_predicate_sound`.

### 4. R1CS lowering layer (`acir-r1cs/src/lower.rs`)

* `lower_assert_zero_gated` — predicated linear/full `AssertZero`
  lowering. Mechanised in `Formal.AcirLowering.lowerAssertZeroLinear_sound`
  (bidirectional iff over all witnesses) +
  `full_satisfied_via_list_aux` / `full_satisfied_from_per_mul_rows`
  (mul-term case, sorry-free).
* `lower_call_at` — cross-circuit `Call` inlining with witness-index
  shifting + predicate combination + memory-scope splice. Mechanised
  in `Formal.CallInlining` (output binding, predicate combination,
  memory-scope namespace disjointness; the inductive proof that
  `AllocState` reaches the requisite `offset` after the caller's
  `MemoryInit` pass is documented in scoped-down lemmas).
* Pinned-constant detection (`memory.rs:extract_pinned_constants`)
  — distinguishes constant-index from variable-index memory ops. The
  variable-index proof is in `Formal.MemoryVarIndex.selector_partition_unique`;
  the constant-index shortcut is wrapped in
  `Formal.Bookkeeping.read/write_const_index_correct`.
* Heterogeneous opcode list-fold composition — the unified
  `AcirOpcode` inductive + `lowerAcirOpcode` + the per-arm soundness
  theorems compose into row-by-row whole-circuit soundness over the
  four heterogeneous arms (linear, full, linear-shifted, brillig).
  BlackBox / MemoryOp / MemoryInit reduce within the lowering to these
  arms via the per-gadget wrappers.

### 5. Trusted-setup ceremony (`xark-backend/src/setup_phase2.rs`, `ceremony.rs`, `ptau.rs`)

* `.ptau` admissibility checks — degree match, subgroup membership,
  pairing-consistency, etc.
* Phase-2 contribution — Schnorr proof of knowledge for each δ
  contribution; chain verification.
* The deterministic-RNG path for `--insecure-dev-mode` (the only RNG
  path used by tests) is explicitly *not* production-safe; the
  CLI guards prevent its use outside dev mode.

All four enforcement paths (Schnorr-PoK, transcript chain, δ
consistency, dev-mode guard) are pinned by
`crates/tests/tests/ceremony_enforcement.rs` (10/10 pass).

### 6. Serialisation boundaries (`xark-backend/src/{serialization,solana}.rs`)

* Binary VK/proof format — pinned by
  [`serialization.md`](serialization.md) and snapshot-tested.
* Solana export — little-endian uncompressed encoding (`x || y`, each
  field element 32-byte LE), with `Fq2` components in `(c0, c1)` order.
  This is what `xark-verifier` consumes on chain via the `alt_bn128_*_le`
  syscalls; `assemble_{vk,proof,public_inputs}_bytes_le` in `solana.rs`
  is the canonical encoder.

### 7. On-chain verifier (`crates/verifier/src/verifier.rs`)

Now fully Kani-proven for canonicality, fail-closed, strict
non-malleability, arity, totality (over the full body, with stubs for
`G1Point::Mul / Add / pairing`), and pairing operand assembly. The
reference program (`crates/verifier/reference-program/`) has a pinned
SHA-256 in `expected.sha256` verified in CI by
`.github/workflows/reproducible-build.yml`.

---

## Out of scope

* External audit cost / scoping — not yet engaged.
* Side-channel analysis of the prover binary — Groth16's standard
  threat model treats the prover as a black box; the prover's
  randomness source is documented in [`security.md`](security.md).
* Fault attacks on the prover machine — handled at the deployment
  layer.
* Network-level integrity between prover and verifier — out of scope.
* Bug-bounty programme — not yet launched.
* Community review of the Lean proofs (e.g. by posting `formal/` to
  Lean Zulip or a ZK research venue) — not yet engaged.

---

## Trust base (we depend on but do not verify)

| Component | Mitigation |
|---|---|
| `nargo` / ACVM correctness | Pin the version, document known limitations, fuzz the ACIR output. |
| `solana_nostd_alt_bn128` syscall ↔ Arkworks fallback | Differential fuzzing (run CPU-weeks under OSS-Fuzz). |
| Arkworks Groth16 | Cite published Groth16 mechanisations (e.g. Microsoft's verified Groth16 in F*); no in-repo proof. |
| Lean kernel + mathlib | Trusted base; replace via Coq cross-check if extreme confidence requires. |
| `rustc` / `cargo` / `lake` / `bitwuzla` / `Kani` / CBMC | Toolchain trust. |

---

## How to update this document

When an audit happens, replace the *Has xark been externally
audited?* line at the top with the audit firm, date, scope, and link
to the published report. Move "findings" into a new
`## Audit findings (YYYY-MM-DD, <firm>)` section and link to the
report. Keep this document concise — it is not a re-statement of
[`security.md`](security.md), only a pointer for an external
reviewer.
