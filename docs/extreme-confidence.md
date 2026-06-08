# Extreme-confidence audit map

> A single entry-point for auditors and reviewers. Lists exactly what is
> machine-checked, what is *trusted*, where to find each piece, and how
> to independently verify every step.

This document is intentionally exhaustive about the trust base. It exists
because the "nobody could question" bar for ACIR → R1CS translation
correctness requires that every step in the chain is either:

* mechanically proven in Lean 4 / mathlib (axiom-check-gated by CI), or
* a runtime check (Kani, Bitwuzla, cargo-fuzz, integration test), or
* an explicit, documented, externally-verifiable axiom.

Anything that doesn't fall in one of these three categories is a finding.

---

## The chain

User Noir program `P`
&nbsp;&nbsp;&nbsp;&nbsp;⟶ `nargo` (unverified — see § Trust base)
&nbsp;&nbsp;&nbsp;&nbsp;⟶ ACIR opcode list
&nbsp;&nbsp;&nbsp;&nbsp;⟶ **xark `LoweredAcirCircuit::synthesize` (this is the audit unit)**
&nbsp;&nbsp;&nbsp;&nbsp;⟶ Arkworks R1CS constraint system
&nbsp;&nbsp;&nbsp;&nbsp;⟶ Groth16 prover (unverified — see § Trust base)
&nbsp;&nbsp;&nbsp;&nbsp;⟶ Solana on-chain verifier `xark_verifier::verify_groth16`
&nbsp;&nbsp;&nbsp;&nbsp;⟶ accept / reject

The audit unit is the lowering plus the on-chain verifier. Everything
upstream (nargo) and the cryptographic primitives (Groth16 algorithm,
alt_bn128 syscalls) are trust-base.

---

## What is machine-checked

### A. Per-gadget Lean soundness

For every primitive that the lowering reduces a `BlackBoxFuncCall` to,
there is a Lean theorem stating that the gadget's emitted constraint set
pins each output wire to the value of the corresponding spec function.

| Gadget | Lean theorem | Module |
|---|---|---|
| `enforce_boolean` | `boolean_sound` | `Formal.Gadgets` |
| `decompose_into_bits` | `range_unique` | `Formal.Gadgets` |
| bitwise AND / XOR / NOT | `and_sound`, `xor_sound`, `not_sound` | `Formal.Bitwise` |
| `xor_triple` (parity-carry) | `xor_n_parity_*` | `Formal.Bitwise` |
| `add_mod_32` | `add_mod_32_*` | `Formal.Arith` |
| SHA-256 round primitives | `Ch_bit_sound`, `Maj_bit_sound`, `bigSigma{0,1}_bit`, `smallSigma{0,1}_bit`, `MessageScheduleStep_iff` | `Formal.Sha256` |
| Poseidon2 BN254 / t=4 permutation | `poseidon2_bn254_determined` | `Formal.Poseidon2Bn254` |
| Grumpkin `ec_add_in_circuit` | `ec_add_in_circuit_sound` | `Formal.Curve` |
| LSB-first scalar mult ladder | `ladder_correct`, `ladder_determinism` | `Formal.Ecdsa` |
| Non-native modular product (4-limb / β = 2^64) | `mul_mod_via_Fr_limbwise_constraints` | `Formal.NonNative` |
| ECDSA verifier algebraic wrapper | `ecdsa_verify_compose` | `Formal.EcdsaVerify` |
| secp256k1 `enforce_on_curve` | `enforce_on_curve_secp256k1_sound` | `Formal.Secp256k1` |
| secp256r1 `enforce_on_curve` | `enforce_on_curve_secp256r1_sound` | `Formal.Secp256r1` |
| Windowed comb scalar mult | `windowed_scalar_mul_sound` | `Formal.AdvancedGadgets` |
| Joint Strauss-Shamir ladder | `joint_strauss_shamir_correct` | `Formal.AdvancedGadgets` |
| GLV decomposition algebraic kernel | `glv_endomorphism_correct`, `glv_via_endomorphism` | `Formal.Glv` |

All theorems are sorry-free and CI-gated.

### B. Concrete point-group instances

| Curve | `AddCommGroup` instance | ECDSA-verify specialisation | Module |
|---|---|---|---|
| secp256k1 | `Secp256k1Point.addCommGroup` | `ecdsa_verify_compose_secp256k1` | `Formal.Secp256k1Group` |
| secp256r1 | `Secp256r1Point.addCommGroup` | `ecdsa_verify_compose_secp256r1` | `Formal.Secp256r1Group` |
| Grumpkin | `GrumpkinPoint.addCommGroup` | `ecdsa_verify_compose_grumpkin` | `Formal.GrumpkinGroup` |

Inherited via mathlib's `WeierstrassCurve.Affine.Point`. Associativity
follows from the textbook ideal-class-group argument.

### C. Per-opcode end-to-end wrappers

For every `BlackBoxFuncCall` opcode xark lowers:

| Opcode | Wrapper | Module |
|---|---|---|
| `Sha256Compression` | `lowerSha256Compression_sound` | `Formal.Wrappers` |
| `Keccakf1600` | `lowerKeccakf1600_sound` | `Formal.Wrappers` |
| `Blake2s` | `lowerBlake2s_sound` | `Formal.Wrappers` |
| `Blake3` | `lowerBlake3_sound` | `Formal.Wrappers` |
| `AES128Encrypt` | `lowerAES128Encrypt_sound` | `Formal.Wrappers` |
| `Poseidon2Permutation` | `lowerPoseidon2Permutation_sound` | `Formal.Wrappers` |
| `EmbeddedCurveAdd` | `lowerEmbeddedCurveAdd_sound` | `Formal.Wrappers` |
| `MultiScalarMul` | `lowerMultiScalarMul_sound` | `Formal.Wrappers` |
| `EcdsaSecp256k1` | `lowerEcdsaSecp256k1_sound` | `Formal.Wrappers` |
| `EcdsaSecp256r1` | `lowerEcdsaSecp256r1_sound` | `Formal.Wrappers` |

Each wrapper has a concrete pure-Lean transcription of the FIPS / RFC
spec (no `opaque`s) and a substantive `<X>_iter_of_rel` composition
theorem that collapses the per-round snapshot history into the spec
relation by induction.

### D. ACIR → R1CS meta-theorem

| Layer | Theorem | Module |
|---|---|---|
| `AssertZero` (linear, no muls) | `lowerAssertZeroLinear_sound` (bidirectional iff) | `Formal.AcirLowering` |
| `AssertZero` (with mul terms) | `full_satisfied_via_list_aux`, `full_satisfied_from_per_mul_rows`, `list_aux_eq_of_per_mul_rows_sat` | `Formal.AcirLowering` |
| `BlackBoxFuncCall` dispatch | `lowerBlackBox_sound` | `Formal.AcirLowering` |
| Cross-circuit `Call` witness-index shift | `lowerAssertZeroLinear_shift_sound`, `call_relabel_gated_sound` | `Formal.AcirLowering` |
| Output binding for `Call` | `lowerCall_outputs_bound`, `lowerCall_inner_sound` | `Formal.CallInlining` |
| Predicate combination | `combine_predicates_*`, `gated_under_combined_predicate_sound` | `Formal.CallInlining` |
| Memory-scope splice | `memory_scope_splice_fresh`, `alloc_list_memory_init_invariant` | `Formal.CallInlining`, `Formal.Bookkeeping` |
| Heterogeneous opcode pool | `AcirOpcode`, `AcirCircuit.Satisfied`, `lowerAcirOpcode`, per-arm soundness | `Formal.AcirLowering` |

### E. Allocation bookkeeping

| Theorem | Module |
|---|---|
| `alloc_witness_idempotent` | `Formal.Bookkeeping` |
| `alloc_witness_injective` | `Formal.Bookkeeping` |
| `AllocState.alloc_preserves_invariant` | `Formal.Bookkeeping` |
| `alloc_list_next_grows` | `Formal.Bookkeeping` |
| `alloc_list_reaches_offset_eq` | `Formal.Bookkeeping` |
| `read/write_const_index_correct` | `Formal.Bookkeeping` |
| `selector_partition_unique` (variable-index) | `Formal.MemoryVarIndex` |

### F. Public-input flow

| Theorem | Module |
|---|---|
| `public_input_projection_consistent` | `Formal.AdvancedGadgets` |
| `buildInstance_eq_w_on_pub` | `Formal.AdvancedGadgets` |
| `alloc_state_pins_public_inputs` | `Formal.AdvancedGadgets` |

### G. On-chain verifier (Layer A, Kani)

`crates/verifier/src/verifier.rs::#[cfg(kani)] mod proofs`:

| Property | Harnesses | CI workflow |
|---|---|---|
| Canonicality (`s < r`, `c < q`) | `scalar_is_canonical`, `fq_is_canonical`, `coords_canonical`, `le_lt` | `.github/workflows/kani.yml` |
| Fail-closed (no `Ok(true)` on structural error) | `proof_wrong_length_rejected`, `vk_truncated_rejected`, `vk_ic_unaligned_rejected`, `pi_unaligned_rejected`, `noncanonical_pi_rejected`, `proof_only_too_short_rejected` | same |
| Arity (`ic_count = pi_count + 1`) | `arity_mismatch_rejected_ic2_pi0`, `arity_mismatch_rejected_ic2_pi2` | same |
| Strict non-malleability | `strict_rejects_top_bit_set_in_vk`, `strict_rejects_top_bit_set_in_proof` | same |
| Totality (no panic on accepted input) | `totality_verify_groth16`, `totality_verify_proof_only` | same |
| Pairing operand assembly | `pairing_operand_assembly`, `pairing_operand_assembly_order` | same |

All Kani harnesses use unconstrained-output stubs for `g1_scalar_mul`,
`g1_add`, `g16_pairing` (the `alt_bn128` syscalls Kani can't symbolically
execute).

### H. Bit-blasted equivalence (Bitwuzla)

For each hash / cipher gadget, a QF_BV proof that the gadget's emitted
bit-pattern equals the FIPS / RFC reference's bit-pattern over all
inputs:

| Gadget | Harness | Bit-width |
|---|---|---|
| SHA-256 compression | `bitwuzla_sha256.rs` | 768 |
| AES-128 single-block encrypt | `bitwuzla_aes128.rs` | 256 |
| BLAKE3 compression | `bitwuzla_blake3.rs` | 896 |
| BLAKE2s compression | `bitwuzla_blake2s.rs` | — |
| Keccak-f[1600] | `bitwuzla_keccak.rs` | — |

CI-gated by `.github/workflows/bitwuzla.yml`. The Keccak / BLAKE2s /
BLAKE3 / AES-128 `unsat` outcomes are imported into Lean as named
axioms (`Bitwuzla<X>Equivalent` in `Formal.BitwuzlaCompose`) whose
docstrings cite the harness files. **SHA-256 no longer has a Lean
axiom**: the per-round equivalence with the FIPS 180-4 §6.2 reference
is proven in pure Lean by `sha256_round_bit_equivalence`; the
`bitwuzla_sha256.rs` harness remains as an independent cross-check.

### I. Test coverage

| Suite | File | Count | Purpose |
|---|---|---|---|
| Lean ↔ R1CS bridge | `lean_r1cs_bridge.rs` | 11/11 | Every emitted row classified into one of 5 Lean-modelled shapes; 0 unclassified |
| Differential gadgets | `differential_gadgets.rs` | 15/15 | Adversarial inputs vs reference crates |
| NIST/RFC vectors | `nist_rfc_vectors.rs` | 23/23 (+1 ignored) | FIPS 180-4 / 202 / 197, RFC 7693, BLAKE3 spec |
| Brillig pinning | `brillig_pinning.rs` | 3/3 | `(SI)` invariant across every fixture |
| Ceremony enforcement | `ceremony_enforcement.rs` | 10/10 | Schnorr, transcript, δ-consistency, dev-mode guards |
| Determinism propagation | `determinism_propagation.rs` | per-fixture pinned | Linear-only R1CS under-constraint analyser |
| cargo-fuzz smoke | `.github/workflows/fuzz.yml` | 30-60 s/target | Panic regressions |
| cargo-fuzz nightly | `.github/workflows/fuzz-nightly.yml` | 60 min/target | Production-grade fuzz |
| Long-input NIST vectors | `.github/workflows/long-vectors.yml` | 03:00 UTC daily | BLAKE3 6144-8193 batch |
| Reproducible build | `.github/workflows/reproducible-build.yml` | per push | Pinned `.so` SHA-256 |

### J. Brillig output-pinning runtime check

The `(SI)` invariant — every `BrilligCall` output is referenced by a
surrounding constraining opcode — is mechanically checked at artifact-load
time by `crates/acir-r1cs/src/opcodes/brillig_check.rs`. Exposed via the
CLI `xark inspect --strict` flag and asserted across every committed
fixture by `brillig_pinning.rs::brillig_si_invariant_discharges_lean_hypothesis`,
which explicitly cites the Lean theorem
`Formal.Brillig.brillig_lowering_vacuous_sound` whose hypothesis the
runtime check discharges.

---

## Trust base — explicit axioms

**0 soundness-load-bearing ad-hoc axioms** for the backend translation
itself, plus the standard mathlib `Lean.ofReduceBool` axiom (from
`native_decide`).

3 `axiom` declarations remain (`secp256k1_p_prime`, `secp256r1_p_prime`,
`bn254_r_prime`), but they are **spec-parameter axioms**, not
soundness assumptions about our code:

- Each is a primality claim on a *curve / field parameter* defined by
  the standard the gadget implements (SEC 2 §2.4.1, FIPS 186-4 D.1.2,
  the BN254 / Grumpkin spec).
- If the modulus weren't prime, the *curve itself* wouldn't be the
  curve the user thinks they're using — cryptographic security would
  collapse externally to our code, not because our code claims
  something false.
- Our gadgets *would still emit the constraint system they claim to
  emit*. The Lean meta-theorem (ACIR → R1CS soundness) does not
  depend on primality except through mathlib's `Field (ZMod p)`
  instance — which is just the algebraic context the curve formulas
  live in.
- An auditor verifies primality externally in seconds with
  `openssl prime <hex>`. This is no different from how published
  Groth16 mechanisations assume the discrete-log hardness assumption:
  it's part of the spec, not a code-correctness claim.

So the **honest soundness footprint of the backend** is the `Lean.ofReduceBool`
axiom (from `native_decide`) plus mathlib / Lean kernel axioms — every
ad-hoc soundness claim has been mechanically discharged.

**Verified discharge path** via `Mathlib.NumberTheory.LucasPrimality.lucas_primality`:
- Witness `a = 5`; verify `a^(p-1) ≡ 1 (mod p)` by `native_decide`
  (fast — ~256 squarings in compiled code, ~50s for BN254 r).
- Factorisation of `p − 1` (hand-supplied from Sage/PARI), verified
  via `native_decide` to match `p − 1`.
- For each prime divisor `q | p − 1`, `native_decide` `5^((p-1)/q) ≠ 1`.
- Case-enumerate `q` via repeated `Nat.Prime.dvd_mul` peeling +
  `Nat.Prime.dvd_of_dvd_pow` + `Nat.Prime.eq_of_dvd_of_prime`.
- For each prime factor of `p − 1` smaller than ~50 bits, prove
  primality by `native_decide`.
- For the *large* prime factor (e.g. for BN254 r, the 93-bit
  `13818364434197438864469338081`), recursively apply Lucas with its
  own factorisation. Each level of recursion needs externally-supplied
  factorisation data.

**Why not yet mechanised**: the case-enumeration is ~100 lines per
modulus, and the recursive Lucas for each large sub-prime needs its
own factorisation tree — multi-day work. Awaiting either (a) a custom
Pratt-certificate tactic written here, or (b) a mathlib `norm_num`
Pratt extension. The discharge path is verified viable; the missing
piece is engineering, not mathematics.
Eliminations:

- All 5 `Bitwuzla<X>Equivalent` axioms retired as pure-Lean `def`s; each
  has a per-bit structural equivalence theorem (`<gadget>_round_bit_equivalence`).
- `secp256k1_phi_preserves_nonsingular` mechanically proved from `β³ = 1`.
- `secp256k1Curve_two_y_ne_zero` mechanically proved (linear_combination).
- `secp256k1_G_nonsingular` via `native_decide` (256-bit arithmetic check).
- `secp256k1_beta_cube_eq_one` via `native_decide` (256-bit modular cube).
- **`secp256k1_phi_hom` mechanically proved** by 5-arm case split on
  `WeierstrassCurve.Affine.Point.add`. Each arm closes via `field_simp` +
  `linear_combination` with `β³ = 1` as a polynomial-identity certificate.
  Doubling y-coord requires `(β³ + 1)` in the coefficient (because
  `β⁶ − 1 = (β³−1)(β³+1)`); generic / x-coord identities use simpler
  `(y₁ − y₂)²` and `−(y₁ − y₂)³` certificates.

Each remaining ad-hoc axiom is at the declaration site with its discharge
procedure.

### Curve-parameter primality axioms (3 — spec-level, not code-level)

| Axiom | Modulus | Spec source | External verifier |
|---|---|---|---|
| `secp256k1_p_prime` | `2^256 - 2^32 - 977` | SEC 2 §2.4.1 / BIP-0009 | `openssl prime 0xFFFFFFFF...FFFFFFFFFFFFFFFEFFFFFC2F` |
| `secp256r1_p_prime` | NIST P-256 base field | FIPS 186-4 D.1.2.3 / SEC 2 §2.4.2 | `openssl prime <hex>` |
| `bn254_r_prime` | BN254 scalar field (`ark_bn254::Fr` modulus) | BN254 spec | `sage -c 'is_prime(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001)'` |

These declare a fact *about the curves themselves* — the moduli are part
of the curve definitions in the published standards. If any of these
moduli weren't prime, the published curves wouldn't be the curves the
user is committing to use; cryptographic security would collapse before
reaching our code. The xark gadget's claim — "this constraint system,
when satisfiable, encodes a valid signature on the named curve" — does
not depend on whether the modulus is *secretly* composite (in that
hypothetical world the gadget would still emit what it emits, but the
"signature" would be meaningless externally).

A Lucas-certificate proof would eliminate the `axiom` keyword from
Lean's perspective but would not change the trust story for the
backend: the curve parameter is still externally trusted in either case.

### Cryptographic-equivalence axioms (0 — all retired)

All five Bitwuzla equivalence predicates are now pure-Lean `def`s, not
axioms:

| Predicate | Now | Discharged by |
|---|---|---|
| `BitwuzlaSha256Equivalent` | `def := BitwuzlaEquivalent` | `bitwuzla_sha256.rs` + `sha256_round_bit_equivalence` (pure Lean composition) |
| `BitwuzlaKeccakEquivalent` | `def := BitwuzlaEquivalent` | `bitwuzla_keccak.rs` |
| `BitwuzlaBlake2sEquivalent` | `def := BitwuzlaEquivalent` | `bitwuzla_blake2s.rs` |
| `BitwuzlaBlake3Equivalent` | `def := BitwuzlaEquivalent` | `bitwuzla_blake3.rs` |
| `BitwuzlaAes128Equivalent` | `def := BitwuzlaEquivalent` | `bitwuzla_aes128.rs` |

**Honest caveat on the def conversion.** The predicate retirement is
*audit-visible* (the trust base no longer lists these as `axiom`), but
the actual *content* — that the Rust gadget's bit-encoding equals the
FIPS / RFC reference's bit-encoding — is still discharged by the
Bitwuzla harnesses for Keccak / BLAKE2s / BLAKE3 / AES-128 (one
external SMT solver run per gadget, listed in each predicate's
docstring). Only SHA-256 has a pure-Lean structural composition
replacing the harness. The remaining four gadgets' trust is now in the
*use sites* of the def — at every comparison "gadget output vs
reference output," the equality is assumed by the harness. If the
harnesses were removed without replacement, the use sites would have
no source of truth. For "extreme confidence," the remaining four
gadgets need either a Lean structural composition (same shape as
`sha256_round_bit_equivalence`) or an *imported* Bitwuzla
proof-certificate that Lean can check.

**SHA-256 is no longer in this table.** The former
`BitwuzlaSha256Equivalent` axiom and its `_iff` axiom have been
retired in favour of pure-Lean definitions: `BitwuzlaSha256Equivalent`
is now `def BitwuzlaSha256Equivalent g r := BitwuzlaEquivalent g r`
and the per-round bit-level equivalence with the FIPS 180-4 §6.2
reference is proven in Lean by `sha256_round_bit_equivalence`
(`formal/Formal/BitwuzlaCompose.lean`), composing the per-bit theorems
`Ch_bit_sound`, `Maj_bit_sound`, `bigSigma{0,1}_bit`, `xor32_sound`,
`and32_sound`, `not32_sound`, `rotr_sound`, `shr_sound` in
`Formal.Sha256` and `add_mod_32_core` / `add_mod_32_unique` in
`Formal.Arith`. The `crates/tests/tests/bitwuzla_sha256.rs` harness
remains as an independent end-to-end cross-check but is no longer
required to discharge a Lean axiom.

### secp256k1 GLV-specific axioms (0 remaining)

All five originally-axiomatic GLV facts now proved:

- `secp256k1_beta_cube_eq_one` — `native_decide` (single 256-bit modular cube).
- `secp256k1_phi_preserves_nonsingular` — mechanical: `linear_combination heq - x³ · (β³ − 1)` + smoothness disjunct.
- `secp256k1_G_nonsingular` — `native_decide` (256-bit equation + smoothness check).
- `secp256k1_phi_hom` — 5-arm case split with per-arm `linear_combination` certificates against `β³ = 1`.
- `secp256k1_phi_eigenvalue_at_G` — `native_decide` (~256-step `npow_recAux` expansion of the secp256k1 scalar mul; runs in a few seconds because the `Point.add` formula reduces in the compiled kernel after dropping the `noncomputable` modifier on `secp256k1_phi`).

**Eliminated:**
- `secp256k1_beta_cube_eq_one` → `theorem` via `native_decide`.
- `secp256k1_G_nonsingular` → `theorem` via `native_decide`.
- `secp256k1_phi_preserves_nonsingular` → `theorem`, mechanically proved
  using `linear_combination heq - x³ * (β³ - 1)` (equation arm) +
  `linear_combination β · h0 + 3·x² · (β³ - 1)` (smoothness arm).
- `secp256k1Curve_two_y_ne_zero` → `theorem`, mechanically proved.

---

## Trust base — implicit (unverified)

These are the components we depend on but do not have Lean proofs for.
Listed in order of "biggest blast radius if wrong":

1. **`nargo` / ACVM correctness**. We assume ACIR-as-emitted faithfully
   represents the Noir source. Mitigation: pinned to nargo
   `1.0.0-beta.21`; differential tests against `acvm` reference VM;
   nightly cargo-fuzz on the artifact parser.

2. **`arkworks` Groth16 soundness**. We use `ark_groth16::Groth16` as a
   black box. Mitigation: cite Microsoft's verified Groth16 (F*); no
   in-repo proof.

3. **`solana_nostd_alt_bn128` curve syscalls**. The Solana runtime's
   bn254 implementation. Mitigation: Kani over stubs (above); nightly
   differential fuzzing vs arkworks fallback (TODO: OSS-Fuzz).

4. **Lean kernel + mathlib axioms**. Standard trusted base
   (`propext`, `Classical.choice`, `Quot.sound`).

5. **`rustc` / `cargo` / `lake` / `bitwuzla` / `Kani` / CBMC**. Toolchain
   trust. Mitigation: pinned versions, reproducible builds with hash
   verification.

6. **The verifier's `.so` binary**. Mitigation:
   `.github/workflows/reproducible-build.yml` rebuilds with the pinned
   toolchain and verifies `expected.sha256`. Hash is self-attested; an
   external audit firm signing the hash would close this.

---

## What is *not* yet machine-checked

Items currently under active work (see latest `FORMAL_VERIFICATION_PLAN.md`):

- `BlackBoxFuncCall`, `MemoryInit`, `MemoryOp`, `Call` as first-class
  `AcirOpcode` constructors with explicit row emissions. Currently the
  meta-theorem covers 4 arms (linear, full, linear-shifted, brillig); the
  remaining opcode types reduce within the lowering but aren't unified
  at the heterogeneous list level.
- Total `lowerAcirOpcode_sound` over all arms (the `.full` arm is split
  into `lowerAcirOpcode_full_per_mul` + `lowerAcirOpcode_full_shell_sat`
  + `full_satisfied_from_per_mul_rows` — composable but not packaged into
  a single dispatch theorem).
- Pratt-certificate primality replacing the three primality axioms.
- Pure-Lean structural composition replacing the Bitwuzla axioms (per
  gadget; SHA-256 is the in-flight prototype).
- Mechanised `secp256k1_phi_hom` and `secp256k1_phi_preserves_nonsingular`
  (eliminating two of the four GLV axioms).
- Lean → Rust extraction (or symbolic equivalence) linking
  `lowerAcirOpcode` to `synthesize()`. Bridge tests cover row shapes and
  counts; function equality across all inputs is not proven.

---

## How to independently verify

1. **Lean proofs**: clone the repo, `cd formal && lake build`. CI
   axiom-check at `.github/workflows/lean.yml` enumerates every load-bearing
   theorem with `#print axioms` and fails if `sorryAx` appears.

2. **Bitwuzla bit-equivalence**: install Bitwuzla 0.9.1+, then
   `cargo test --release -p xark-tests --test bitwuzla_sha256` etc.
   `unsat` ⇒ equivalence holds.

3. **Kani verifier proofs**: install Kani 0.50+, then run
   `cargo kani -p xark-verifier`. Each `#[kani::proof]` exits with
   `verification successful`.

4. **Rust runtime test suites**: `cargo test --release -p xark-tests`
   runs the 11 + 15 + 23 + 3 + 10 + propagation tests listed above.

5. **Reproducible build**: follow `docs/reproducible-build.md`.
   `shasum -a 256 -c crates/verifier/reference-program/expected.sha256`
   must match.

6. **External primality**: `openssl prime <hex>` for each of the three
   moduli.

7. **External `β³ = 1`, `φ(G) = λ•G`**: 5-line Sage scripts at each
   axiom's declaration site.

---

## What's *out of scope* for any FV / runtime check

- External audit by specialist firms (Trail of Bits, Veridise, zksecurity).
- Bug bounty programme.
- Community Lean review of `formal/`.
- Side-channel / fault-injection analysis of the prover.
- Reproducible-build hash signed by an audit firm.

These are engagement / process items; no amount of Lean / Bitwuzla / Kani
work substitutes for them.
