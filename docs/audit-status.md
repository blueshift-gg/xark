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
Integration tests in `gadgets/tests/tests/` (`differential_alt_bn128`, `end_to_end`,
`fuzz`, `host`, `multi_function`, `ptau`, `randomness`, `sbpf`, `serialization`,
`solana_format`, `xark_ir_e2e`) plus workspace unit tests, including:

* **KAT cross-checks** against `k256`, `p256`, `sha2`, `keccak`, `blake2`, `blake3`,
  `aes`, `ark-grumpkin` — each gadget vs the published reference crate.
* **Tampering tests** — every gadget's e2e test mutates the witness and verifies the
  constraint system reports unsatisfied.
* **Adversarial inputs** — all-zero, all-FF, alternating, near-modulus, boundary-length
  vs reference crates. Fixtures are being regenerated directly from xark circuits.
* **NIST/RFC official vectors** — FIPS 180-4 §B (SHA-256), FIPS 202 §C (SHA-3), RFC 7693
  §B (BLAKE2s), official BLAKE3 `test_vectors.json`, FIPS 197 §B + CAVP (AES-128).
* **Lean ↔ R1CS bridge** (`crates/lang/tests/snapshot.rs`) — pins each frontend gadget's
  multiplication-gate count to its Lean soundness model, so any drift forces a re-check.
* **Hint/advice output-pinning** — hint outputs are pinned by surrounding R1CS
  constraints, and the solver's `solve_and_check` rejects any witness that violates a
  constraint, so an unpinned hint output can't force a satisfying assignment.
* **Ceremony enforcement** — `CeremonyError` rejection paths (Schnorr-PoK, transcript
  hash chain, δ-consistency, dev-mode guards) exercised by the ptau/setup paths.
* **cargo-fuzz smoke** (`gadgets/tests/tests/fuzz.rs`) — over the artifact parser,
  witness parser, and IR→R1CS lowering. Run manually; no CI gate yet. Production fuzzing
  is CPU-weeks.

### Lean 4 / mathlib formal proofs (`formal/`)

Per-gadget soundness, most of the on-chain-verifier proofs, and the xark-IR→R1CS
meta-theorem. CI-gated by `.github/workflows/lean.yml`; the axiom check rejects any proof
depending on `sorryAx`. Coverage (theorem names → modules):

* **Field primitives** — `boolean_sound`, `range_unique`, `bits_unique`
  (`Formal.Gadgets`).
* **Bitwise** — `and_sound`, `xor_sound`, `not_sound`, `xor_n_parity_*`, `add_mod_32_*`
  (`Formal.Bitwise` + `Formal.Arith`).
* **SHA-256 structural** — `rotr_sound`, `shr_sound`, `Ch_bit_sound`, `Maj_bit_sound`,
  `MessageScheduleStep_iff` (`Formal.Sha256`).
* **Curve** — Grumpkin `ec_add_in_circuit_sound` (full algebraic closure: generic +
  doubling + inverse + on-curve + selector mux), `secp256k1`/`secp256r1` closures
  (`Formal.Curve / Secp256k1 / Secp256r1`).
* **Concrete point groups** — `Secp256k1Point`, `Secp256r1Point`, `GrumpkinPoint`
  (`Formal.*Group`): all three are mathlib `WeierstrassCurve.Affine.Point` aliases
  inheriting `AddCommGroup` via `inferInstance`. Three trusted primality axioms (one per
  base field) — see "Trusted base additions".
* **Poseidon2** — `poseidon_permutation_determined` (width-polymorphic) and
  `poseidon2_bn254_t3_determined` (the concrete `t = 3` instance the gadget implements)
  (`Formal.Poseidon` + `Formal.Poseidon2Bn254T3`).
* **ECDSA scalar mult** — `ladder_step_correct`, `ladder_correct`, `ladder_determinism`
  (`Formal.Ecdsa`).
* **Non-native arithmetic** — `mul_mod_via_Fr_limbwise_constraints` (4×64-bit) and
  `mul_mod_via_Fr_limbwise_constraints_3` (3×86-bit, matching the `mod_mul_3` gadget the
  secp curves use) — the full ℕ + Fr no-wrap chain (`Formal.NonNative`).
* **ECDSA verifier wrapper** — `ecdsa_verify_compose` (parametric over `G : AddCommGroup`),
  specialised to secp256k1/r1/Grumpkin (`Formal.EcdsaVerify` + per-curve `*Group`).
* **GLV** — `glv_sum_eq`, `glv_via_endomorphism`, `glv_endomorphism_correct` (abstract),
  `glv_endomorphism_correct_secp256k1` (concrete φ) (`Formal.Glv` + `Formal.Secp256k1Group`).
* **Comb / Strauss-Shamir** — `windowed_scalar_mul_sound`, `joint_strauss_shamir_correct`
  (`Formal.AdvancedGadgets`).
* **Bit-hash gadgets** — per-primitive bit-soundness (`rotr_sound`, `xor32_sound`,
  `Ch_bit_sound`, `and64_sound`, …) plus whole-compression round-step composition for
  SHA-256, Keccak-f[1600], BLAKE2s, BLAKE3, AES-128, transcribed from FIPS/RFC
  (`Formal.Sha256 / Keccak / Blake / Aes`, composed in `Formal.Wrappers`). The Keccak ρ·π
  index was **corrected to `(X + 3Y) % 5`** to match the KAT-verified `xark-keccak` gadget
  across all 25 lanes.
* **AES algebraic S-box** — `gf256_pow254_eq_inv` (`b²⁵⁴ = inv b` in GF(2⁸),
  Itoh–Tsujii) and `aesSbox_pow_eq_table` prove the table-free `affine(b²⁵⁴) ⊕ 0x63` S-box
  equals the AES lookup table for every byte (`Formal.GF256`).
* **secp incomplete point-add** — `ec_add_incomplete_secp256k1_sound` /
  `_secp256r1_sound`: the flag-free 3-limb chord addition lands on the curve with a unique
  slope (no prover freedom), from the generic `Curve` algebra at `(a,b) = (0,7)` and
  `a = −3` (`Formal.Secp256k1 / Secp256r1`).
* **Lazy non-native reduction** — `mul_lazy_25519_value_correct` / `mul_lazy_k1_value_correct`
  and `weak_reduce_*_value_correct`: the quotient-free pseudo-Mersenne multiply/normalise
  the ed25519/secp256k1 incomplete-add paths use compute `a·b mod p` correctly, via the
  Mersenne relations (`2²⁵⁵ ≡ 19`, `2²⁵⁶ ≡ 2³²+977`); `lazy_t_no_wrap` bounds every
  intermediate `< 2²⁵³ < r` so the `Fr` arithmetic lifts faithfully to ℕ
  (`Formal.Lazy25519 / LazyK1`). Discharges the "non-native limb bridge" trust boundary
  `Formal.Edwards` names for the lazy path.
* **Merkle membership** — `merkle_level_swap_sound`: a boolean position bit makes the
  per-level sibling mux a genuine conditional swap (no under-constraint, no off-pair value),
  composed with Poseidon determinacy (`Formal.Merkle`).
* **R1CS ↔ Lean bridge** — ten snapshot tests in `crates/lang/tests/snapshot.rs` pin each
  frontend gadget's multiplication-gate count to its Lean soundness model.
* **Allocation bookkeeping** — `AllocState`, `alloc_witness_idempotent`,
  `alloc_witness_injective`, `AllocState.alloc_preserves_invariant`,
  `read/write_const_index_correct` (`Formal.Bookkeeping`).
* **Public-input flow** — `public_input_projection_consistent`, `buildInstance_eq_w_on_pub`,
  `alloc_state_pins_public_inputs` (`Formal.AdvancedGadgets`).
* **Verifier — Kani** — canonicality, fail-closed (every structural error path returns
  `Err` ≠ `Ok(true)`), strict non-malleability, arity, totality with curve-op stubs
  (`totality_verify_groth16`, `totality_verify_proof_only`), and pairing operand-assembly
  (`pairing_operand_assembly`); see `#[cfg(kani)] mod proofs` in
  `crates/verifier/src/verifier.rs` and `.github/workflows/kani.yml`.

`lean.yml` enumerates **all** these theorem names and rejects any proof depending on
`sorryAx`. Standard mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) are allowed.

### Trusted base additions (axiomatised)

Three axioms in `formal/`, each documented at its declaration site:

| Axiom | Scope | Why |
|---|---|---|
| `secp256k1_p_prime : Fact (Nat.Prime secp256k1_p)` | 256-bit prime | Lean's kernel can't `decide` 256-bit primality; verifiable via `openssl prime`. |
| `secp256r1_p_prime : Fact (Nat.Prime secp256r1_p)` | 256-bit prime | Same. |
| `bn254_r_prime : Fact (Nat.Prime r)` | 254-bit prime | BN254 `Fr` modulus; used by `GrumpkinPoint` and field instances. |

These are the only `axiom` declarations in `formal/`. No `sorry`/`sorryAx`. `lean.yml`
prints `#print axioms` for every load-bearing theorem and fails CI on any `sorryAx`.

### `native_decide` axioms

The GF(2^8) infrastructure in `Formal.GF256` (AES S-box) verifies key identities by
exhaustive computation over the 256-element byte range — `gf256_mul_inv` (`x·x⁻¹ = 1` for
255 nonzero bytes), `gf256_inv_unique` (over 65 536 pairs), `aesSbox_algebraic_eq_table`
(`Affine(gf256_inv x) ⊕ 0x63 = SBOX[x]` over all 256). These use `native_decide`, adding
`Lean.ofReduceBool`-style axioms — strictly weaker than `axiom`, since the propositions are
pure computations the compiled bytecode deterministically evaluates.

### AES S-box bit-level soundness

The S-box gadget uses a GF(2^8) multiplicative-inverse trick + affine transform
(`s_box_in_circuit` in `gadgets/xark-aes/src/lib.rs`): allocates `x_inv`/`is_zero` boolean
wires, enforces the inverse identity via cross-product/XOR constraints, and emits the
FIPS-197 affine transform as a per-bit XOR chain. The algebraic identities it relies on
(cross-product/XOR chain = GF(2^8) mul; `gf256_mul x x_inv = 1` uniquely pins
`x_inv = gf256_inv x`; `Affine(gf256_inv x) ⊕ 0x63 = SBOX[x]`) are **mechanically verified**
in `Formal.GF256` by `native_decide`.

The **per-row bridge** from the gadget's `Fr`-level constraint emission (64 cross-product
linear constraints, 8 parity-decomposition carry chains, 8 affine XOR-chains) to those
GF(2^8) statements is mechanised in `Formal.Aes`:

* **`IsValidSBoxByteWitness`** (structure) — encodes the full per-byte constraint chain over
  `Fr` (booleanness, `x·is_zero = 0`, `x_inv·is_zero = 0`, the 64 cross-products
  `wP a b = wX a · wX_inv b`, 8 parity rows giving `prod_bits[k]`, `prod_bits[0] = 1 − is_zero`
  and `prod_bits[k] = 0` for `k ≠ 0`, and the 8 affine XOR-with-`0x63` rows).
* **`aesSbox_byte_constraint_sound`** (theorem) — from `IsValidSBoxByteWitness x`, concludes
  `∀ j, BitOf (wOut j) ((aesSbox x) j)`, routing through
  `byteWireToNat_wX_inv_eq_gf256_inv`, `gf256_bit_aesAffine_nat` + `gf256_bit_xor_byte`, and
  `byteToNat_aesSbox` (the algebraic↔table identity from `Formal.GF256`).
* **`aesSubBytes_constraint_sound`** (theorem) — the 16-byte lift to the full SubBytes layer.

The `Fr → ℕ` no-wrap argument is the same shape as `Formal.Blake.addMod32_bit_sound`,
applied at the per-byte cross-product/parity chain level. `aesRoundStep_bit_sound` consumes
`IsValidSBoxByteWitness ×16` directly (via `aesSubBytes_constraint_sound`) — no
canonical-lift/existential intermediate. Trust that the gadget's emitted R1CS *forces* the
output wires to satisfy `IsValidSBoxByteWitness` rests on: the Rust exhaustive test
`sbox_all_inputs_match_table` (`gadgets/xark-aes/src/lib.rs`); and the pure-Lean per-bit
composition proofs in `Formal.Aes`, discharged against FIPS-197 through
`aesSubBytes_constraint_sound`, `aesShiftRows_sound`, `aesMixColumns_sound`,
`aesAddRoundKey_sound`, resting on the `Formal.GF256` S-box identities (`#print axioms` gated
by `lean.yml`).

This is **not** an external audit. Until an external firm reviews the code, the README's
"experimental — do not use in production" label stays.

## Where an external auditor should start

Rough order of "biggest blast radius if wrong":

### 1. Non-native arithmetic over secp curves (`gadgets/xark-secp256k1/src/lib.rs`, `gadgets/xark-bignum/src/lib.rs`)

The single largest soundness surface — every ECDSA proof depends on:

* `bigint256_mul_mod` — limb-by-limb non-native mul with prover-aided quotient. Mechanised
  in `Formal.NonNative.mul_mod_via_Fr_limbwise_constraints` (ℕ + Fr no-wrap, `n = 4, β = 2^64`).
* `sub_mod` — direct subtraction (`a − b + k·m − c = 0`, `k ∈ {0,1}`).
* `inv_mod` — modular inverse via `a·a_inv = 1`; reduces to `mul_mod` + a non-zero check.
* `enforce_on_curve` — `y² = x³ + a·x + b mod p`. Lean lemmas exist for all three curves
  (`enforce_on_curve_grumpkin_sound`, `Formal.Secp256k1.enforce_on_curve_secp256k1_sound`,
  secp256r1 analogue), **but were previously not wired into the gadgets.** Grumpkin now
  enforces it in-circuit (`y² = x³ − 17`, called by `scalar_mul`/`multi_scalar_mul`). The
  secp256k1/secp256r1 (ECDSA) and Ed25519 gadgets do **not** yet call an on-curve check —
  their points are public inputs, so on-curve validation is currently the caller's
  responsibility off-circuit; wiring the (Lean-proven) non-native check in is a tracked
  follow-up.
* `enforce_in_range_one_to_n` — `r, s ∈ [1, n−1]`. Without it a malicious prover could
  exploit the `inv_mod(s)` step.
* GLV decomposition (`glv_decompose_in_circuit`) — proves `k = k1 + λ·k2 (mod n)` with
  `|k1|, |k2| < 2^129`. Kernel proven (`glv_via_endomorphism` + `glv_endomorphism_correct`);
  concrete `secp256k1_phi`, homomorphism, and eigenvalue discharged in `Formal.Secp256k1Group`
  (`secp256k1_phi_hom`, `secp256k1_phi_eigenvalue_at_G`, `secp256k1_phi_acts_as_lambda`).
* Fixed-base comb tables for `u1·G` — core proven (`windowed_scalar_mul_sound`); the
  comb-row-2 doubling exception is in scope of the same proof.

### 2. Hint/advice trust-outputs assumption

Hint outputs (`hint_*` — inverses, bit decompositions, quotients) are allocated as fresh
witnesses with **no** in-circuit constraint at the hint itself. Soundness rests on every hint
output being pinned by surrounding R1CS constraints. Enforced by construction: the solver
reproduces each hint output, and `solve_and_check` rejects any witness violating a constraint,
so an unpinned hint output can't force a satisfying assignment. An auditor should:

* verify that *all* constraints referencing each hint output are the ones the solver checks;
* construct adversarial circuits where a hint output is **not** pinned and confirm
  `solve_and_check` still rejects a bad witness.

### 3. xark-IR → R1CS lowering (`crates/ir/`, `crates/lang/src/lower_mir.rs`)

Deliberately small: **no opcode dispatch, no predication.** The accepted MIR subset lowers to
`add`/`sub`/`mul`/`require_eq` + `hint_*`/advice, then directly to R1CS. Auditable points:

* **Each primitive → its expected constraint.** Fixed, small footprint; FV bridge tests pin
  every gadget's mul-gate count, so drift forces a Lean re-check.
* **`mul` → fresh-var alloc + the `require_eq` merge.** A `mul` allocates one fresh witness
  and emits one `A·B = C` row; the `require_eq` merge folds a trailing equality into it (this
  is what keeps difference-of-squares at one constraint). These two rules are the whole
  compaction story — read together.
* **Hint/advice reproduction** — the solver reproduces each hint output; `solve_and_check`
  rejects any constraint-violating witness.

### 4. Trusted-setup ceremony (`crates/backend/src/setup_phase2.rs`, `ceremony.rs`, `ptau.rs`)

* `.ptau` admissibility — degree match, subgroup membership, pairing-consistency.
* Phase-2 contribution — Schnorr PoK per δ contribution; chain verification.
* The deterministic-RNG path for `--insecure-dev-mode` (the only RNG path tests use) is
  explicitly *not* production-safe; CLI guards prevent its use outside dev mode.

All four enforcement paths (Schnorr-PoK, transcript chain, δ consistency, dev-mode guard) are
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
| `rustc` MIR shape (nightly) | Pin the nightly, validate the accepted MIR subset and reject the rest, fuzz the lowering. |
| `solana_nostd_alt_bn128` syscall ↔ Arkworks fallback | Differential test `gadgets/tests/tests/differential_alt_bn128.rs`: same fixed vectors via the Arkworks fallback (host `#[test]`s) and the on-chain syscall path (`#[svm_test]`s through Mollusk + cargo-build-sbf), asserting byte-identical results. Run under the `Solana E2E` CI workflow on every verifier change; each new `G1_ADD`/`G1_MUL`/`G2_ADD`/`PAIRING_2` vector adds an anchor. Extending to OSS-Fuzz CPU-weeks is a follow-up. |
| Arkworks Groth16 | Cite published Groth16 mechanisations (e.g. Microsoft's verified Groth16 in F*); no in-repo proof. |
| Lean kernel + mathlib | Trusted base; replace via Coq cross-check if needed. |
| `rustc` / `cargo` / `lake` / `Kani` / CBMC | Toolchain trust. |

## How to update this document

When an audit happens, replace the *Has xark been externally audited?* line with the firm,
date, scope, and report link. Move findings into a new
`## Audit findings (YYYY-MM-DD, <firm>)` section. Keep this document concise — it points an
external reviewer at [`security.md`](security.md), not a restatement of it.
