# Audit status

> **Has xark been externally audited?** No.

Canonical place to track what *has* been internally reviewed, what's load-bearing for
soundness, and what an external auditor should focus on first. Pairs with
[`security.md`](security.md) (per-gadget soundness claims).

## What's been reviewed internally

### Documentation
* [`security.md`](security.md) — per-gadget soundness sketches, authored by the same
  person who wrote the gadget: read as an *assertion*, not independent corroboration.
* Hint/advice output-pinning soundness — every hint output (inverses, bit
  decompositions) must be pinned by surrounding R1CS constraints; now *machine-checked
  during lowering* in the xark-IR→R1CS path (see below).
* [`trusted-setup.md`](trusted-setup.md) — phase-2 MPC driver and `.ptau` admissibility.
* [`reproducible-build.md`](reproducible-build.md) — pinned-toolchain build of the
  verifier `.so` (`xark_verifier_reference_program.so`), hash-verified in CI.

### Test suite
Integration tests in `gadgets/tests/tests/` (`differential_alt_bn128` and `sbpf` as
their own binaries; `ceremony_cli`, `end_to_end`, `fuzz`, `host`, `multi_function`, `ptau`,
`serialization`, `solana_format`, `xark_ir_e2e` and the rest as modules of the one `it`
binary under `it/`) plus workspace unit tests, including:

* **KAT cross-checks** against `k256`, `p256`, `sha2`, `keccak`, `blake2`, `blake3`,
  `aes`, `ark-grumpkin` — each gadget vs the published reference crate.
* **Tampering tests** — every gadget's e2e test mutates the witness and verifies the
  constraint system reports unsatisfied.
* **Adversarial inputs** — all-zero, all-FF, alternating, near-modulus, boundary-length
  vs reference crates. Fixtures are being regenerated directly from xark circuits.
* **NIST/RFC official vectors** — FIPS 180-4 §B (SHA-256), FIPS 202 §C (SHA-3), RFC 7693
  §B (BLAKE2s), official BLAKE3 `test_vectors.json`, FIPS 197 §B + CAVP (AES-128).
* **Lean ↔ R1CS bridge** (`crates/lang/tests/snapshot.rs`) — thirteen tests pin
  multiplication-gate counts, most of circuits a hand-restated Lean model describes, so
  drift there forces a re-check.
* **Hint/advice output-pinning** — hint outputs are pinned by surrounding R1CS
  constraints, and the solver's `solve_and_check` rejects any witness that violates a
  constraint, so an unpinned hint output can't force a satisfying assignment.
* **Ceremony enforcement** — `CeremonyError` rejection paths (Schnorr-PoK, transcript
  hash chain, δ-consistency, seeded-key guards) exercised by the ptau/setup paths.
* **proptest smoke** (`gadgets/tests/tests/it/fuzz.rs`) — the verifier's entry points
  on arbitrary and mutated bytes (never panic, never accept) and the `circuit.xbc`
  decoder on arbitrary bytes (never panic). Runs with the test suite; production
  fuzzing is CPU-weeks.

### Lean 4 / mathlib formal proofs (`formal/`)

Per-gadget soundness over the exported rows, hand-restated models, and the frontend's
rewrites and minimizer certificates. CI-gated by `.github/workflows/lean.yml`; the axiom
check rejects any proof depending on `sorryAx`. Coverage (theorem names → modules):

* **Gadget templates (proofs over the exported rows)** — each `#[gadget]` harness under
  `formal/templates/` has `Xark.Templates.<Gadget>.soundness` over the rows the frontend
  emits, re-exported and hash-checked in CI: bit decompositions (`Formal.ToBits*`,
  `Formal.ToBitsCanonical`), `xor` / `or` (`Formal.BoolOps`), `add32` (`Formal.Add32`),
  `reduce::<N>` (`Formal.Reduce`), `xor3` / `maj3` / `chi` / `ch` (`Formal.HashOps`), the AES
  S-box (`Formal.AesSbox`), `cond_swap` (`Formal.CondSwap`; `root_binds` composes the Merkle
  levels, assuming, not proving over its rows, that `hash2` computes a function), the
  Grumpkin scalar multiplications and Pedersen hash (`Formal.SignedMul`, `ScalarMul`,
  `WideScalarMul`, `MultiScalarMul`, `PedersenHash`), and the signature gadgets listed
  under *Non-native arithmetic* below. `--coverage` checks which production calls emit
  exactly these rows.
* **Field primitives** — `boolean_sound`, `range_unique`, `bits_unique`
  (`Formal.Gadgets`): the booleanity row and `decompose_bits`, restated by hand.
* **Bitwise** — `and_sound`, `xor_sound`, `not_sound` (`Formal.Bitwise`): `Field::and`,
  the `emit_xor` row, `Field::not`, restated by hand. `add_mod_32_*` (`Formal.Arith`) is
  the ℕ fact under `add32` / `reduce`; `xor_n_parity_*` models a parity row no current
  gadget emits.
* **SHA-256** — FIPS 180-4 definitions and per-bit lemmas (`rotr_sound`, `shr_sound`,
  `xor32_sound`, …, `MessageScheduleStep_iff`) and the identities behind `compress`'s
  fused reductions (`newA_of_newE`, `feedForward_fused`) (`Formal.Sha256`). `compress`'s
  Ch, Maj and Σ/σ rows are the `ch` / `maj3` / `xor3` templates; no theorem is about its
  whole rows.
* **Concrete point groups** — `Secp256k1Point`, `Secp256r1Point`, `GrumpkinPoint`
  (`Formal.*Group`): all three are mathlib `WeierstrassCurve.Affine.Point` aliases
  inheriting `AddCommGroup` via `inferInstance`. The three base-field primes are proven
  prime by kernel-checked Pratt certificates (`Formal.Pratt`, `Formal.CurvePrimes`).
* **Poseidon2** — `sbox_sound` (the `x⁵` rows), `poseidon_permutation_determined`
  (width-polymorphic) and `poseidon2_bn254_t3_determined` (the `t = 3` instance with
  `xark-poseidon2`'s constants and matrices) (`Formal.Poseidon` + `Formal.Poseidon2Bn254T3`).
  Determinism of a Lean model; the gadget's 240 S-box gates are pinned by a snapshot test.
* **Non-native arithmetic** — the pseudo-Mersenne multiplication certificates the
  signature gadgets use (`mul_cert_k1` / `_r1` / `_25519`: `Formal.MulCertK1 / MulCertR1 /
  MulCert25519`), `range_check_limbs`, `require_lt` (`Formal.RangeCheckLimbs*`,
  `Formal.RequireLt*`), the secp256k1 / P-256 add, fused double-and-add and on-curve
  checks (`Formal.EcK1Check / EcR1Check`), Ed25519's `ed_*_check` (`Formal.EdCurveCheck`),
  and the scalar side of fake GLV (`Formal.FakeGlvK1 / FakeGlvR1 / FakeGlv25519`, with
  the group-side `FakeGlv.verify_sound` / `verify_sound_cofactored`), all over their
  exported rows.
* **secp incomplete point-add** — `ec_add_incomplete_secp256k1_sound` /
  `_secp256r1_sound` (`Formal.Secp256k1 / Secp256r1`): the field equations of
  `xark_curve`'s 3-limb `ec_add_incomplete` (`dxinv·dx = 1`, `λ·dx = dy`, the chord
  formulas) give an on-curve output with a unique slope. No theorem connects the
  gadget's limb rows (`mod_mul`, `mod_inverse`) to these equations.
* **Lemmas about models no current gadget emits** — `Formal.Curve`'s
  `ec_add_in_circuit_sound` (complete addition with infinity flags, a selector mux and
  gated slopes; `xark_grumpkin::ec_add` is incomplete) and its secp copies in
  `Formal.Secp256k1 / Secp256r1`; `Formal.Ecdsa`'s `ladder_*` (LSB-first double-and-add);
  `Formal.NonNative`'s `mul_mod_via_Fr_limbwise_constraints` (3 × 86-bit columns with
  unsigned carries; `mulmod_columns` uses biased signed carries); `Formal.EcdsaVerify`'s
  `ecdsa_verify_compose`; `Formal.Glv` / `Formal.AdvancedGadgets` (GLV algebra, comb and
  joint-ladder sums over any group); the Keccak / BLAKE round compositions over
  `xor` / `and` / `not` wires (`Formal.Keccak / Blake / Wrappers`); allocation and
  public-input bookkeeping (`Formal.Bookkeeping`, `public_input_projection_consistent`).
* **Frontend rewrites and minimizer** — `elim_sound`, `cse_sound`, `inline_sound`,
  `fold_sound`, `const_mul_sound`, `gated_sat`, `pin_dead`, `select_taken` (`Formal.Rewrites`):
  each row-reducing rewrite is exact over an R1CS model; `check_sound`, `check_complete`
  (`Formal.Minimize.Sound`): a minimizer certificate the checker accepts relates the
  minimized rows to the original ones.
* **R1CS ↔ Lean bridge** — thirteen `*_matches_lean_model` tests in
  `crates/lang/tests/snapshot.rs` pin the multiplication-gate count of Poseidon2, Merkle,
  SHA-256, Keccak, BLAKE2s, BLAKE3, AES-128/256, GHASH, AES-GCM, `fp_mul` and the
  secp256k1 / P-256 incomplete adds. A changed count forces a re-check; an unchanged one
  does not show the rows are the model's.
* **Verifier — Kani** — canonicality, fail-closed (every structural error path returns
  `Err` ≠ `Ok(true)`), strict non-malleability, arity, totality with curve-op stubs
  (`totality_verify_groth16`, `totality_verify_proof_only`), and pairing operand-assembly
  (`pairing_operand_assembly`); see `#[cfg(kani)] mod proofs` in
  `crates/verifier/src/verifier.rs` and `.github/workflows/kani.yml`.

`lean.yml` builds with `lake build` and
runs `formal/AxiomCheck.lean`: every harness under `formal/templates/` must have its
`soundness` theorem, and every declaration in `Formal` may depend only on
the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Anything else — a
`sorryAx`, a declared `axiom`, a `native_decide` — fails CI.

### Trusted base additions

There are no `axiom` declarations in `formal/`: the secp256k1, secp256r1 and BN254
primes, once trusted axioms, are theorems proven by Pratt certificates
(`Formal.CurvePrimes`, checked by the kernel with `decide`). No `sorry`/`sorryAx`.
No `native_decide` either: the legacy AES / GF(2⁸) proofs, its last users, are deleted.
Nothing is added to the kernel's trust.

This is **not** an external audit. Until an external firm reviews the code, the README's
"experimental — do not use in production" label stays.

## Where an external auditor should start

Rough order of "biggest blast radius if wrong":

### 1. Non-native arithmetic in the signature gadgets (`gadgets/xark-bignum/src/lib.rs`, `gadgets/xark-secp256k1`, `xark-secp256r1`, `xark-ed25519`)

The single largest soundness surface — every ECDSA and EdDSA proof depends on:

* `mul_cert_k1` / `mul_cert_r1` / `mul_cert_25519` — non-native multiplication by
  pseudo-Mersenne certificates over 8×32-bit limbs, each proven sound over its exported
  rows (`Formal.MulCertK1 / MulCertR1 / MulCert25519`).
* `range_check_limbs` and `require_lt` — limb range checks and `x < m` against a
  constant (`Formal.RangeCheckLimbs*`, `Formal.RequireLt*`).
* On-curve and canonical-coordinate checks — `on_curve_k1` / `on_curve_r1` (secp) and
  `point_in` (Ed25519) require each coordinate `< p` and the point on the curve, for the
  public key and for the hinted `R` alike (`Formal.EcK1Check` / `EcR1Check` /
  `EdCurveCheck`). Grumpkin's `enforce_on_curve` (`y² = x³ − 17`) is
  native-field.
* Scalar ranges — ECDSA requires `r, s, e < n` (`require_lt`) and `r, s ≠ 0`
  (`assert_nonzero_limbs`); EdDSA requires `S < L` (`assert_scalar_below_order`).
  Without them a malicious prover could exploit the hinted `s⁻¹` or malleate `S`.
* Fake GLV (ePrint 2025/933) — the prover hints a short `(A, B)`; `fake_glv_check_k1` /
  `_r1` / `_25519` pin the scalar relations (`Formal.FakeGlvK1 / FakeGlvR1 / FakeGlv25519`).
* The group side — fused double-and-add steps over signed digits (`ec_double_add_k1` /
  `_r1`, proven per step) and a fixed-base comb for the generator (`one_hot8` over
  constant tables). How the steps are chained across the loop is covered by tests, not
  by a whole-loop proof (see [`security.md` §6](security.md#6-recommended-audit-scope)).

### 2. Hint/advice trust-outputs assumption

Hint outputs (`hint_*` — inverses, bit decompositions, quotients) are allocated as fresh
witnesses with **no** in-circuit constraint at the hint itself. Soundness rests on every hint
output being pinned by surrounding R1CS constraints. Enforced by construction: the solver
reproduces each hint output, and `solve_and_check` rejects any witness violating a constraint,
so an unpinned hint output can't force a satisfying assignment. An auditor should:

* verify that *all* constraints referencing each hint output are the ones the solver checks;
* construct adversarial circuits where a hint output is **not** pinned and confirm
  `solve_and_check` still rejects a bad witness.

### 3. xark-IR → R1CS lowering (`crates/ir/`, `crates/frontend/`)

Deliberately small: **no opcode dispatch.** The circuit's wasm lowers to
`add`/`sub`/`mul`/`require_eq` + `hint_*`/advice, then directly to R1CS. Auditable points:

* **Each primitive → its expected constraint.** Fixed, small footprint; `lean-export
  --check` fails when a proven gadget's rows drift from its template, and the snapshot
  bridge tests pin the mul-gate count of the hand-restated models' circuits.
* **`mul` → fresh-var alloc + the `require_eq` merge.** A `mul` allocates one fresh witness
  and emits one `A·B = C` row; the `require_eq` merge folds a trailing equality into it (this
  is what keeps difference-of-squares at one constraint). These two rules are the whole
  compaction story — read together.
* **Hint/advice reproduction** — the solver reproduces each hint output; `solve_and_check`
  rejects any constraint-violating witness.

### 4. Trusted-setup ceremony (`crates/groth16/src/setup.rs`, `crates/backend/src/ceremony.rs`, `ptau.rs`)

* `.ptau` admissibility — degree match, subgroup membership, pairing-consistency.
* Phase-2 contribution — Schnorr PoK per δ contribution; chain verification.
* The deterministic-RNG path (`xark setup --deterministic-rng`, the only RNG path tests use)
  is explicitly *not* production-safe: setup refuses it with a `.ptau`, `xark prove` refuses a
  seeded prover RNG with a production key, and `xark export` warns about a seeded key.

All four enforcement paths (Schnorr-PoK, transcript chain, δ consistency, seeded-key guard) are
exercised by the ptau/setup paths in `gadgets/tests/tests/`.

### 5. Serialisation boundaries (`crates/backend/src/{serialization,solana}.rs`)

* Binary VK/proof format — pinned by [`serialization.md`](serialization.md), snapshot-tested.
* Solana export — little-endian uncompressed (`x || y`, each field element 32-byte LE), with
  `Fq2` components in `(c0, c1)` order. This is what `xark-verifier` consumes on chain via the
  `alt_bn128_*_le` syscalls; `assemble_{vk,proof,public_inputs}_bytes_le` in `solana.rs` is the
  canonical encoder.

### 6. On-chain verifier (`crates/verifier/src/verifier.rs`)

Fully Kani-proven for canonicality, fail-closed, strict non-malleability, arity, totality (with
stubs for `G1Point::Mul / Add / pairing`), and pairing operand assembly. The reference program
(`crates/verifier/reference-program/`) has a pinned SHA-256 in `expected.sha256` verified in CI
by `.github/workflows/reproducible-build.yml`.

`verify_groth16_batch` (several proofs of one VK in one pairing call) is new and
has had no review beyond its own tests and Kani harnesses. An auditor should
check the weight derivation (SHA-256 over the domain tag, the whole VK and the
whole batch, 252-bit weights with `r₀ = 1`), that every value the pairing sees
is covered by that hash, and the `Σ rᵢ` reduction mod `r` (`add_mod_r`).

## Out of scope

* External audit cost/scoping — not yet engaged.
* Side-channel analysis of the prover binary — Groth16 treats the prover as a black box; its
  randomness source is documented in [`security.md`](security.md).
* Fault attacks on the prover machine — deployment layer.
* Network integrity between prover and verifier — out of scope.
* Bug-bounty programme — not yet launched.
* Community review of the Lean proofs (Lean Zulip / a ZK venue) — not yet engaged.

## Trust base (we depend on but do not verify)

| Component | Mitigation |
|---|---|
| `rustc` codegen (wasm32) | Circuit ops are opaque wasm imports, so the circuit is rustc-independent (CI compares every example's digest on 1.89 / stable / beta); witness branches are guarded (Lean `gated_sat` & co.); the lowering is fuzzed against native Rust with exhaustive witness search. |
| `solana_nostd_alt_bn128` syscall ↔ Arkworks fallback | Differential test `gadgets/tests/tests/differential_alt_bn128.rs`: same fixed vectors via the Arkworks fallback (host `#[test]`s) and the on-chain syscall path (`#[svm_test]`s through Mollusk + cargo-build-sbf), asserting byte-identical results. Run under the `Solana E2E` CI workflow on every verifier change; each new `G1_ADD`/`G1_MUL`/`G2_ADD`/`PAIRING_2` vector adds an anchor. The verifier does no curve or subgroup checks of its own (its `*_strict` entry points add only an encoding check) and relies on the backend to refuse malformed points, so both paths are also tested to reject a G1 point off the curve or with a coordinate `>= q` (pairing, add, mul) and an off-subgroup G2 point (pairing). Extending to OSS-Fuzz CPU-weeks is a follow-up. |
| Groth16 (`xark-groth16`: setup, prover, verifier) | In-repo, not mechanised (cite published Groth16 mechanisations, e.g. Microsoft's verified Groth16 in F*). Cross-checked in tests against `ark-groth16` as an independent implementation: byte-identical keys and proofs for the same randomness, the same verification verdicts, and phase-2 keys byte-identical to an arkworks-based reference. |
| BN254 arithmetic (`ark-bn254`, `ark-ff`, `ark-ec`) | The field, curve and pairing operations everything above is built on. |
| Lean kernel + mathlib | Trusted base; replace via Coq cross-check if needed. |
| `rustc` / `cargo` / `lake` / `Kani` / CBMC | Toolchain trust. |

## How to update this document

When an audit happens, replace the *Has xark been externally audited?* line with the firm,
date, scope, and report link. Move findings into a new
`## Audit findings (YYYY-MM-DD, <firm>)` section. Keep this document concise — it points an
external reviewer at [`security.md`](security.md), not a restatement of it.
