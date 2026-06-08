# Formal verification plan

The testing we have (cross-implementation differential, fuzzing, many-witness,
completeness + binding) raises confidence but is still *finite-input*. Formal
verification is the only way to get *all-input* guarantees. This is a proposal —
scoped by leverage, with realistic tooling — not a commitment.

## The trust stack, and where proof effort pays off

A proof verifying on-chain means: *the prover knew a satisfying assignment to
**our** R1CS*. For that to mean what we want ("the prover knew a valid Noir
execution"), three layers must each be correct:

| # | Layer | Failure if wrong | Tractability |
|---|-------|------------------|--------------|
| A | On-chain verifier (Rust): parsing, canonical encodings (anti-malleability), no-panic, the pairing equation | accepts an invalid proof / panics (DoS) | **High** — small, bounded |
| B | ACIR→R1CS lowering + gadgets: R1CS satisfiable **iff** ACIR satisfiable | under-constraint → forge a false statement; over-constraint → DoS valid users | **Low–Med** — the hard, high-value target |
| C | Groth16 protocol soundness over BN254 | the scheme itself is broken | Out of scope — rely on published proofs |

Layer C we do **not** re-prove: cite the Groth16 soundness results and existing
mechanizations; our job is to use the scheme correctly, which is A.

## Layer A — the on-chain verifier (highest ROI, do first)

Small, self-contained Rust over fixed-size byte buffers — a good fit for
**Kani** (Rust bounded model checker, CBMC backend) or **Creusot**/**Prusti**
(deductive verification).

Properties to prove for `verify_groth16` / `verify_proof_only` / `Verifier::verify`
and their `*_strict` variants:
1. **Totality / no panic** for *all* inputs (no OOB index, no slice panic,
 no integer overflow). Kani proves this directly over symbolic byte slices.
2. **Fail-closed**: every structural error path returns `Err`/`Ok(false)`, never
 `Ok(true)`. (The entrypoint already maps `≠ Ok(true)` → reject.)
3. **Canonicality** — **✅ done (Kani).** Proven over *all* inputs that the byte
 comparators match integer comparison against the field orders:
 `scalar_is_canonical(s) ⇔ s < r` (public-input scalars) and
 `fq_is_canonical(c) ⇔ c < q` (proof/VK coordinates, enforced by the `*_strict`
 entry points), plus that `le_lt` is a correct 256-bit LE comparison and
 `coords_canonical` is the conjunction of the per-coordinate checks. Harnesses:
 `#[cfg(kani)] mod proofs` in `crates/verifier/src/verifier.rs`, run in CI by
 `.github/workflows/kani.yml`.
4. **Non-malleability (strict path)**: the `alt_bn128` syscall masks the unused
 top bits of each 32-byte limb, so non-canonical encodings of the same
 point/scalar decode identically and would otherwise verify — a real finding,
 pinned by `tests/fuzz.rs` and `tests/sbpf.rs::flag_bit_mutation_onchain`. Prove
 that `verify_*_strict` returns `Err` for any input with a coordinate `≥ q`
 (lifting #3 to the entry point), so the canonical encoding is the *only*
 accepted one.
5. **Length/arity**: the accepted byte-length set is exactly
 `{448 + 64·(N+1)}` × proof(256) × inputs(32·N) with `ic_count = N+1`.

Effort: **weeks**, mostly mechanical. Tooling: Kani (best ergonomics for #1–#2),
plus a small SMT lemma for #3. This eliminates the entire "verifier code bug"
class — the part an attacker most directly touches.

**Status (2026-06):** #2 (fail-closed), #4 (strict non-malleability), and #5
(arity) are **done** — see `#[cfg(kani)] mod proofs` in
`crates/verifier/src/verifier.rs`. The structural-error paths early-exit
before any `alt_bn128` syscall fires, so Kani can discharge them without
stubbing curve ops. Specifically discharged over all inputs of the
indicated bounded sizes:
* **Fail-closed:** `proof_wrong_length_rejected`, `vk_truncated_rejected`,
  `vk_ic_unaligned_rejected`, `pi_unaligned_rejected`,
  `noncanonical_pi_rejected`, `proof_only_too_short_rejected` — every
  structural-error path returns `Err`, never `Ok(true)`.
* **Arity:** `arity_mismatch_rejected_ic2_pi0` /`_pi2` — the accepted
  arity at `N = 1` is bracketed by rejected off-by-one neighbours.
* **Strict non-malleability:** `strict_rejects_top_bit_set_in_vk` /
  `_in_proof` — `verify_groth16_strict` returns
  `Err(NonCanonicalCoordinate)` for any input with bit 255 of any 32-byte
  chunk in `vk_bytes` / `proof_bytes` set.

The remaining Layer-A obligation is #1 (totality over the *full* `verify_groth16`
body, including the curve ops that run on accepted inputs). That requires
`kani::stub` replacements for `G1Point::Mul`, `G1Point::Add`, and `pairing`,
deferred to a follow-up.

The pairing-equation *math* (`e(-A,B)·e(α,β)·e(vk_x,γ)·e(C,δ)=1`) is delegated
to the `alt_bn128` syscalls; we don't re-prove the pairing, but we should prove
our *operand assembly* equals the intended equation (a rewrite check, doable in
the same framework).

## Layer B — the lowering and gadgets (the hard, valuable part)

The property that matters is **soundness of the lowering**: for every ACIR
circuit, the produced R1CS is satisfiable by an assignment *iff* the ACIR is, and
the public outputs coincide. The dangerous direction is *under-constraint* — an
R1CS that accepts assignments the ACIR would reject. This is undecidable in
general, but tractable per-gadget. Three complementary tracks, cheapest first:

1. **R1CS determinism / under-constraint analysis (automated). — first pass done.**
 The core soundness property of a gadget's R1CS is *functional determinism*:
 given the input wires, every other wire is uniquely determined. Tools exist:
 - **Ecne** (QED²) — proves R1CS "uniquely determined" via Gröbner/propagation.
 - **Picus** (from the circom/Picus line) — SMT-based under-constraint detector.
 Plan: export each gadget's R1CS (we already extract `to_matrices()`), run a
 determinism checker, and treat "not proven deterministic" as a finding to
 audit. This is **automated** and catches the exact bug class our single-
 variable probe could only spot-check.
 **Done so far** (`crates/tests/tests/determinism_propagation.rs`, native
 Rust, CI-gated by `.github/workflows/determinism-prop.yml`): a
 **linear-only propagation analyzer** runs across every committed fixture
 over BN254 `Fr`, seeded by the public-input values and reading the gadget
 matrices via `to_matrices()`. For each constraint row `A·B = C` it splits
 the LCs into a determined-constant part plus a residual over still-unknown
 wires; rows that reduce to a single linear equation in one unknown with
 nonzero coefficient pin that unknown. Booleans `b·(b−1)=0` and other
 quadratic constraints are deliberately *not* pinned — the analyzer is a
 sound under-approximation, and the bit-blasted gadgets light up as
 findings (Picus's Gröbner backend is the escalation path). The test ships
 a per-fixture pinned-count floor so any regression below the floor fails
 CI. Remaining: wire **Picus** (Veridise) as the second-tier deeper pass,
 once the upstream's binary format settles on a stable release.

2. **Per-gadget functional correctness (semi-automated). — started (Lean 4).**
 For each gadget (sha256, keccak, blake, aes, ecdsa, poseidon, range, bitwise),
 prove the constrained relation equals the reference spec. Options:
 - SMT/bit-blasting for the bit-oriented gadgets (sha256/keccak/blake/aes are
 boolean circuits — well-suited to a SAT/SMT equivalence check against a
 reference boolean spec).
 - A proof assistant (**Lean 4** is the pragmatic choice given momentum and the
 `mathlib` BN254 field support, or Coq) for the field-arithmetic gadgets
 (ecdsa, curve, poseidon) where bit-blasting blows up.
 **Done so far** (`formal/`, Lean 4 + mathlib, deductive over *all* field
 assignments, machine-checked in CI by `.github/workflows/lean.yml`):
 - `boolean_sound` — `enforce_boolean`'s `b·(b−1)=0` holds iff `b ∈ {0,1}`
 (the primitive every gadget pins its wires with).
 - `range_unique` — `decompose_into_bits` is **functionally deterministic**:
 the bit-vector is uniquely determined by the recomposed value (no
 under-constraint slack) for the full `MAX_BITS = 253` width range; the cap
 is exactly what keeps the field sum below `r` so it cannot wrap.
 - `and_sound` / `xor_sound` / `not_sound` — the binary bitwise ops in
 `bitwise.rs`: each per-bit constraint both determines the output bit and
 computes the intended boolean op, with the output staying in `{0,1}`.
 - `xor_n_parity_*` / `add_mod_32_*` — the carry-based gadgets in `bitwise.rs`:
 the N-ary XOR output bit is the input parity, and the `add_mod_32` result is
 the wrapping sum `(Σ inputs) mod 2³²` and is uniquely determined (the new
 content is the carry arithmetic + a no-wrap-below-`r` argument).
 - `sbox_sound` — the Poseidon2 `x⁵` S-box (`poseidon.rs`), the permutation's
 only multiplicative step, forced to `out = x⁵`.
 - `sbox_apply_sound` / `partial_sbox_apply_sound` / `linear_step_determined`
 / `add_constants_determined` / `full_round_determined` /
 `partial_round_determined` / `poseidon_permutation_determined` — the
 **whole Poseidon2 permutation is a deterministic function of its input
 state**: each linear layer, constant addition, full round, and partial round
 is shown to be a function of its input, and the permutation is a `foldl` of
 a schedule of rounds. The theorems are parametric over the specific round
 constants / matrices — *given any fixed schedule* the permutation is a
 function. Closure of the soundness story modulo plugging in the published
 Poseidon2 schedule and constants.
 - `ec_add_generic_slope_unique` / `ec_add_generic_on_curve` — the embedded
 curve's generic point-addition case (`curve.rs`): the slope (hence the output
 point) is uniquely determined, and the addition law **closes** — the output
 lands back on the curve.
 - `ec_double_slope_unique` / `ec_double_on_curve` / `ec_inverse_recognized` —
 the **doubling case** of point addition (`λ·(2·y1) = 3·x1²` over Grumpkin
 where `a = 0`): slope determinism, addition-law closure, and an explicit
 predicate showing the inverse-case branch (`x1=x2`, `y1+y2=0`) is exactly
 `P2 = −P1`.
 - `selector_unique` / `selectors_double_case` / `selectors_inverse_case` /
 `output_mux_lhs_inf` / `output_mux_rhs_inf` / `output_mux_inverse` /
 `output_mux_generic` — the **selector routing layer** of
 `ec_add_in_circuit`: the boolean selectors `same_x, same_y, is_double,
 is_inverse` are uniquely pinned by the inputs (no prover freedom in the
 routing layer), and the 4-way output mux routes to the correct branch
 (`P2`, `P1`, `∞`, or generic `(xg, yg)`) in each selector configuration.
 Together with the algebraic theorems this closes the end-to-end soundness
 story for in-circuit Grumpkin point addition.
 - `ladder_step_correct` / `ladder_correct` / `ladder_determinism` — the
 **LSB-first double-and-add scalar-multiplication ladder** used by
 `scalar_mul_in_circuit` / `msm_in_circuit` / `ecdsa.rs`, proven abstractly
 over any additive commutative group: the per-bit invariant
 `(acc, P) ↦ (acc + b·P, 2·P)`, full ladder correctness
 `acc_final = bitsToNat(bs) • P`, and scalar-level determinism (same scalar
 ⇒ same ladder output). Composes with the curve theorems by specialising the
 group to the Grumpkin point group.
 - `mul_mod_sound` / `mul_mod_complete` / `valOfLimbs(_zero|_succ)` /
 `mul_mod_via_limbs` — the **prover-aided non-native modular product** that
 every secp256k1 base/scalar-field multiplication in `ecdsa.rs` reduces to.
 Soundness: integer identity `a · b = q · m + c` plus `c < m` ⇒
 `c = (a · b) mod m` (no slack in the modular result). Completeness:
 honest witness always exists. Limb-recomposition glue: the same statement at
 the level of limb vectors recomposed via `Σᵢ ls i · β^i`, which is the shape
 the `ecdsa.rs` limb-by-limb constraints discharge.
 - `colSum_eq` / `carry_telescope` / `colSum_carry_telescope` /
 `mul_mod_via_limbwise_constraints` — the **carry-no-wrap step** that closes
 the non-native multiplication soundness chain. Per-column partial-product
 identity (Cauchy product) + a schoolbook carry recurrence with ℕ-carries
 bounded by `carry 0 = carry (2n) = 0` together force the limb-by-limb
 column equations to imply the integer identity `a·b = q·m + c` over ℕ; this
 composes with `mul_mod_sound` to give `mul_mod_via_limbwise_constraints`,
 the **end-to-end Lean statement of soundness for `ecdsa.rs::mul_mod`**.
 Proven for general `n` (limb count). The remaining obligation is *Fr-level*:
 the lowering layer must keep each carry below the BN254 modulus (analogue
 of `two_pow_lt_r` for `range_unique`); given that, the `ℕ`-carry hypothesis
 here is automatic.
 - `gated_on_curve_sound` / `gated_on_curve_trivial` /
 `enforce_on_curve_grumpkin_sound` — the gated curve-membership check
 `(1 − is_inf)·(y² − x³ + 17) = 0` forces `(x, y) ∈ Grumpkin` when
 `is_inf = 0` and is vacuous when `is_inf = 1`. Closes the "input is on the
 curve" hypothesis used by every other curve theorem.
 - `IsValidECAddWitness` / `EcAddSemantics` /
 `ec_add_in_circuit_generic_sound` / `ec_add_in_circuit_sound` — the
 **end-to-end soundness wrapper** for `curve.rs::ec_add_in_circuit`: any
 prover witness satisfying the gadget's full constraint set produces an
 output that matches the algebraically correct Grumpkin group-law result in
 every branch (`∞ ⊕ P`, `P ⊕ ∞`, `P ⊕ (−P)`, `P ⊕ P`, generic). One
 statement, full coverage.
 - `add_val_no_wrap` / `mul_val_no_wrap` / `colSum_le` / `carry_le` /
 `mul_mod_via_Fr_limbwise_constraints` — **the `Fr`-level no-wrap argument**
 that closes the secp256k1 non-native multiplication chain. Column sums and
 carries are budget-bounded (`< 2^131` and `< 2^195` respectively for
 `n = 4, β = 2^64`), well below `r ≈ 2^254`; combined with the `ZMod` →
 `ℕ` bridges, the gadget's `Fr`-level column equations lift exactly to the
 `ℕ`-statement that `mul_mod_via_limbwise_constraints` discharges. This is the
 secp256k1 analogue of `two_pow_lt_r` for `range_unique`.
 - `poseidon2Bn254RC` / `poseidon2Bn254_M_E` / `poseidon2Bn254_M_I` /
 `poseidon2Bn254Schedule` / `poseidon2Bn254` / `poseidon2_bn254_determined`
 (in `Formal/Poseidon2Bn254.lean`) — the **concrete BN254 / `t = 4` Poseidon2
 specialisation** of the parametric permutation. All 256 round constants
 (`64 × 4`) and both matrices (external and internal) are transcribed from
 `poseidon.rs` and instantiated; `poseidon2_bn254_determined` is the
 parametric `poseidon_permutation_determined` applied at the concrete
 schedule. To make this possible, the `Poseidon.lean` per-cell lemmas were
 generalised from `[Field F]` to `[CommRing F]` (their proofs only used
 commutative-ring axioms; `ZMod r` for the 254-bit BN254 modulus is only a
 `CommRing` in practice because the kernel cannot decide primality on a
 number that large).
 - `Sha256.lean` — a **structural soundness layer** for SHA-256: pure Lean
 spec for `Word32`, `rotr`, `shr`, the bitwise ops, the FIPS round helpers
 `Ch / Maj / Σ₀ / Σ₁ / σ₀ / σ₁`, and the message-schedule recurrence. Soundness
 lemmas (`rotr_sound`, `shr_sound`, `Ch_bit_sound`, `Maj_bit_sound`, etc.) show
 how the gadget's per-op constraints compose into the FIPS-spec primitives by
 chaining the existing per-bit lemmas (`and_sound` / `xor_sound` / `not_sound`
 / `add_mod_32`). Per the plan, full bit-equivalence of the 64-round SHA-256
 compression is **explicitly out of scope for Lean** and left to SMT-backed
 bit-blasting against a reference implementation — Lean is the wrong tool for
 that step.
 - `EcdsaVerifyRel` / `IsValidEcdsaWitness` / `ecdsa_verify_sound` /
 `mul_mod_lifts_to_ZMod` / `ladder_gives_R_def` / `ecdsa_verify_compose`
 (in `Formal/EcdsaVerify.lean`) — the **end-to-end ECDSA verifier
 soundness wrapper**. Packages the per-primitive theorems
 (`mul_mod_via_Fr_limbwise_constraints`, `ladder_correct`) into one
 statement: any prover witness satisfying the gadget's intermediate-state
 predicate (range-check + `s·w=1` + `u₁=e·w` + `u₂=r·w` + `R=u₁•g+u₂•Q`
 + `r=R.x mod n`) implies the textbook ECDSA-verify relation
 `EcdsaVerifyRel`. Parametric over the curve point group `G`, so it
 specialises to secp256k1 / secp256r1 once a verified curve-group model
 is added (the abstract group avoids redoing curve closure for
 secp256k1, which `Formal.Curve` does not yet cover — only Grumpkin).
 **SHA-256 compression**: bit-blasted equivalence between
 `crates/acir-r1cs/src/gadgets/hash.rs::sha256_compression` and the
 FIPS 180-4 §6.2 spec — `crates/tests/tests/bitwuzla_sha256.rs`,
 CI-gated by `.github/workflows/bitwuzla.yml` — emits two independent
 QF_BV encodings (one mirroring the gadget step-by-step, one a clean
 reference) and runs them through **Bitwuzla**; `unsat` ⇒ the two
 encodings agree on all 768-bit inputs (16 W + 8 state words). Closes
 the SHA-256 compression equivalence over all inputs; combined with
 `Formal.Sha256`'s per-primitive Lean soundness, this is end-to-end.
 **AES-128 single-block encrypt**: bit-blasted equivalence between
 `crates/acir-r1cs/src/gadgets/aes.rs` and the FIPS 197 spec —
 `crates/tests/tests/bitwuzla_aes128.rs`, CI-gated by the same
 `.github/workflows/bitwuzla.yml` — emits two independent QF_BV
 encodings of AES-128 single-block encryption (10 rounds, full key
 schedule, full 256-entry S-box ladder, GF(2⁸) `xtime`, ShiftRows,
 MixColumns, AddRoundKey) and asserts they disagree on any of the 16
 output bytes; `unsat` ⇒ bit-equivalence over all 256-bit
 (plaintext + key) inputs. Both encodings are FIPS 197 verbatim but
 differ in MixColumns operand grouping (nested binary `bvxor` in `ref_`
 vs. n-ary `bvxor` in `gad_`) so the proof is non-trivial (Bitwuzla
 verifies the algebraic associativity rather than syntactic-matching).
 **BLAKE3 compression**: bit-blasted equivalence between
 `crates/acir-r1cs/src/gadgets/blake3.rs::compress_in_circuit` and the
 BLAKE3 spec (<https://github.com/BLAKE3-team/BLAKE3-specs>) —
 `crates/tests/tests/bitwuzla_blake3.rs`, CI-gated by the same
 `.github/workflows/bitwuzla.yml` — emits two independent QF_BV
 encodings of the 7-round 16-word-state BLAKE3 compression (one
 mirroring the gadget's `mix_in_circuit` step-by-step, one a clean
 reference), with the 16 output words `out[0..8] = v[0..8] XOR v[8..16]`,
 `out[8..16] = h[0..8] XOR v[8..16]` (the full XOF / extended-output
 state, not just the 8-word CV the gadget returns). `unsat` ⇒ the two
 encodings agree on all 896-bit inputs (8 CV + 16 message + counter_low
 + counter_high + block_len + flags). Closes BLAKE3 compression
 equivalence over all inputs.
 Effort remaining: **engineering**, not core FV. The remaining items are
 SMT-backed equivalence harnesses for Keccak (same shape as
 `bitwuzla_sha256.rs` / `bitwuzla_aes128.rs` / `bitwuzla_blake3.rs`),
 the Layer-A #1 Kani totality work, external audit; the per-gadget Lean
 soundness story is essentially closed.

3. **Lowering-engine correctness (deepest).**
 Prove the ACIR-opcode → R1CS translation rules themselves sound (each opcode
 lowering preserves semantics), so correctness composes to *any* circuit, not
 just the committed gadgets. This is a mechanized proof of `acir-r1cs`'s
 translation in a proof assistant against an ACIR semantics. Effort:
 **multi-month, research-grade**; highest assurance, lowest near-term ROI.

## Recommended sequencing

1. **Kani on Layer A** — **canonicality is done and in CI** (#3 above). Remaining:
 totality / fail-closed / arity over the full `verify_groth16` parse path, which
 calls the `alt_bn128` `pairing` syscall — Kani can't symbolically execute the
 pairing, so this needs a `kani::stub` replacing the curve ops with an
 unconstrained model, then proving the *parsing around them* never panics and
 never returns `Ok(true)` on a structural error. Bounded effort, next.
2. **Next / weeks:** wire R1CS determinism checking (Ecne/Picus) over every
 gadget's extracted matrices — automated under-constraint coverage, the thing
 our probe can't fully do.
3. **Then / months:** per-gadget functional equivalence, bit-blasting the
 boolean hash/aes gadgets first (most automatable), proof-assistant for the
 arithmetic gadgets. **In progress** (Lean 4 / mathlib under `formal/`, run in
 CI): boolean primitive, range-gadget determinism, the bitwise ops
 (AND/XOR/NOT), the carry gadgets (N-ary XOR parity, `add_mod_32`), the
 Poseidon2 `x⁵` S-box **and the parametric full-permutation determinism chain
 (linear / constant / full round / partial round / scheduled permutation)**,
 embedded-curve point addition **end-to-end with a single packaged soundness
 wrapper** (`ec_add_in_circuit_sound`: gated on-curve check + generic + doubling
 algebra + inverse-case predicate + selector under-constraint slack + 4-way
 output mux, all matched against a semantic group-law relation), the
 **LSB-first double-and-add scalar-multiplication ladder** (per-bit invariant
 + full-ladder correctness + scalar-level determinism, abstractly over any
 additive commutative group), the **full ℕ + Fr non-native modular-product
 soundness chain** for `ecdsa.rs` (prover-aided identity + Cauchy column-sum
 + carry recurrence + Fr-level no-wrap budget bounds →
 `mul_mod_via_Fr_limbwise_constraints`), the **concrete BN254 / t=4 Poseidon2
 specialisation** (all 256 round constants + both matrices instantiated and
 the parametric determinism specialised), and a **structural SHA-256 soundness
 layer** showing the FIPS primitives (Ch, Maj, Σ₀, Σ₁, σ₀, σ₁, message
 schedule) compose out of the already-proven per-bit gadgets. Remaining: an
 SMT-backed bit-equivalence harness for the full SHA-256 / Keccak / BLAKE /
 AES compression functions (deliberately out of scope for Lean per this
 plan's "better by SMT bit-blasting" recommendation).
4. **Long-term:** mechanize the lowering rules for all-circuit soundness.

In parallel (engineering, not FV, but complementary): external audit, and
extend the differential + many-witness harnesses to all gadgets with computed
expected outputs.

## What this does **not** buy

Even full Layer-A+B verification leaves: the trusted setup (a ceremony concern,
not code — see `docs/trusted-setup.md`), bugs in arkworks / the `alt_bn128` syscalls /
`nargo`'s ACVM (dependencies we trust), and side channels. FV raises the floor
dramatically; it is not a substitute for the ceremony or for trusting the
underlying primitives.
