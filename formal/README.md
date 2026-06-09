# `formal/` — Lean 4 proofs of gadget soundness

Machine-checked soundness proofs for the R1CS gadgets emitted by
[`crates/acir-r1cs`](../crates/acir-r1cs), written in **Lean 4** against
**mathlib**. Covers the field-arithmetic gadgets where SMT / bit-blasting
blows up and a proof assistant is the right tool.

Where the Kani harnesses (in `crates/verifier`) discharge the
on-chain verifier's byte logic by *bounded model checking*, these Lean
theorems are *deductive* proofs that hold over **all** field assignments —
there is no input bound.

## What is proven

Each theorem mirrors the exact constraints the Rust builder enforces.

[`Formal/Gadgets.lean`](Formal/Gadgets.lean) — boolean primitive and range gadget:

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `boolean_sound` | `gadgets/boolean.rs::enforce_boolean` | `b * (b - 1) = 0 ↔ b ∈ {0,1}` in any field |
| `range_unique` | `gadgets/range.rs::decompose_into_bits` | the bit-vector is **uniquely determined** by the recomposed value (no under-constraint slack), for widths `n ≤ 253 = MAX_BITS` |
| `bits_unique` | (lemma) | binary recomposition `Σᵢ 2ⁱ·bᵢ` is injective on bit-vectors over `ℕ` |

[`Formal/Bitwise.lean`](Formal/Bitwise.lean) — bitwise primitives (each proves
the output bit is determined *and* equals the intended boolean op, staying in `{0,1}`):

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `and_sound` | `gadgets/bitwise.rs::and` (`aᵢ·bᵢ = outᵢ`) | `out ∈ {0,1}` and `out = 1 ↔ a = 1 ∧ b = 1` |
| `xor_sound` | `gadgets/bitwise.rs::xor` (`(2a)·b = a + b − out`) | constraint pins `out = a + b − 2ab`; `out ∈ {0,1}` and `out = 0 ↔ a = b` |
| `not_sound` | `gadgets/bitwise.rs::not` (`1 − a`) | `1 − a ∈ {0,1}` and `1 − a = 1 ↔ a = 0` |

[`Formal/Arith.lean`](Formal/Arith.lean) — the carry-based gadgets (the new
content is the carry arithmetic + no-wrap-below-`r` argument):

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `xor_n_parity_core` / `xor_n_parity_field` | `bitwise.rs::xor_n_inputs` (`Σⱼ bⱼ = out + 2k`) | the output bit is the input **parity** `(Σ bⱼ) % 2`, ℕ-core and lifted to the `ZMod r` constraint |
| `add_mod_32_core` / `add_mod_32_unique` | `bitwise.rs::add_mod_32` (`Σ inputs = result + 2³²·carry`) | the result is the **wrapping sum** `(Σ inputs) % 2³²`, and is uniquely determined |

[`Formal/Poseidon.lean`](Formal/Poseidon.lean) — the Poseidon2 S-box plus a
parametric model of the round structure (linear layer, round-constant addition,
full round, partial round, full permutation):

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `sbox_sound` | `poseidon.rs::sbox` (`x·x=t, t·t=u, u·x=out`) | the three constraints force `out = x⁵` |
| `sbox_unique` | — | the S-box output carries no prover freedom |
| `sbox_apply_sound` | full-round S-box layer (componentwise on the state) | per-cell constraints force `out = applySbox s` |
| `partial_sbox_apply_sound` | partial-round S-box (cell `0` only) | first cell squared, rest pinned to input |
| `linear_step_determined` | `poseidon.rs::matrix_4x4_in_circuit` / `internal_m_in_circuit` LCs | matrix-vector product is a function of its input state |
| `add_constants_determined` | round-constant addition | componentwise `rc + s` is a function of its inputs |
| `full_round_determined` | one full round (add-RC → S-box every cell → linear) | round output is a function of the input state |
| `partial_round_determined` | one partial round (add-RC₀ → S-box cell 0 → internal linear) | same, for the partial-round variant |
| `poseidon_permutation_determined` | the whole `poseidon2_permutation_native` (initial linear + scheduled rounds) | the permutation is a function of its input — **no prover freedom anywhere outside the per-cell S-box, which `sbox_sound` already pins** |

The round/permutation theorems are parametric over the round constants, the
external 4×4 matrix, and the internal diagonal matrix. See
[`Formal/Poseidon2Bn254.lean`](Formal/Poseidon2Bn254.lean) below for the
**concrete specialisation** with the actual BN254 / `t = 4` / Poseidon2
constants and matrices used by `poseidon.rs`.

[`Formal/Poseidon2Bn254.lean`](Formal/Poseidon2Bn254.lean) — concrete
instantiation of `poseidonPermutation` to the BN254 `t = 4` Poseidon2 used by
the gadget:

| Definition / Theorem | Source | Statement |
|----------------------|--------|-----------|
| `poseidon2Bn254RC` | `poseidon.rs` lines 64–449 | the full 64 × 4 round-constant table, reduced mod the BN254 scalar modulus |
| `poseidon2Bn254_M_E` | `poseidon.rs::matrix_multiplication_4x4` | the external 4×4 matrix `[[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]]` |
| `poseidon2Bn254_M_I` | `poseidon.rs` `INTERNAL_DIAG_HEX` (lines 54–60) | the internal matrix `diag[i]·δᵢⱼ + 1` with the four diagonal entries transcribed from the Rust gadget |
| `poseidon2Bn254Schedule` | `poseidon.rs::poseidon2_permutation_native` | the length-64 round schedule (4 full + 56 partial + 4 full) |
| `poseidon2Bn254` | — | the concrete permutation `(Fin 4 → ZMod r) → (Fin 4 → ZMod r)` |
| `poseidon2_bn254_determined` | `poseidon_permutation_determined` instantiated | the concrete BN254 Poseidon2 permutation is a deterministic function of its input |

To support this concrete instantiation, the per-cell `Poseidon.lean` lemmas
were generalised from `[Field F]` to `[CommRing F]` — they only ever used the
commutative-ring axioms, and `ZMod r` for non-prime modulus is only a `CommRing`
(BN254's prime modulus is too large for `Decidable` primality without an axiom).

[`Formal/Curve.lean`](Formal/Curve.lean) — the embedded short-Weierstrass curve
point addition, generic case (`x1 ≠ x2`), doubling case (`P1 = P2`), and the
inverse-case predicate:

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `ec_add_generic_slope_unique` | `curve.rs` slope constraint `(x2−x1)·λ = y2−y1` | the slope (hence `x3,y3`) is uniquely determined when `x1 ≠ x2` |
| `ec_add_generic_on_curve` | `curve.rs` formulas `x3=λ²−x1−x2`, `y3=λ(x1−x3)−y1` | the **addition law closes**: `(x3,y3)` is back on the curve |
| `ec_double_slope_unique` | `curve.rs` doubling constraint `λ·(2·y1) = 3·x1²` | the doubling slope is uniquely determined when `2·y1 ≠ 0` |
| `ec_double_on_curve` | `curve.rs` formulas `x3=λ²−2x1`, `y3=λ(x1−x3)−y1` for Grumpkin (`a=0`) | the **addition law closes** in the doubling case: `(x3,y3)` is back on Grumpkin |
| `ec_inverse_recognized` | the inverse-case branch (`x1=x2`, `y1+y2=0`) routed to infinity | the inputs are exactly `P2 = −P1`, documenting why the selector picks `(0,0,1)` |
| `selector_unique` | `curve.rs` selector constraints (booleanness + `same_x · (x1−x2) = 0` + indicator-equation pair, products defining `is_double` / `is_inverse`) | the selector booleans are **uniquely determined by the inputs** — no prover freedom in the routing layer |
| `selectors_double_case` | the doubling-branch selector configuration | when `x1=x2`, `y1=y2`, both non-infinity: forces `same_x=1, same_y=1, is_double=1, is_inverse=0` |
| `selectors_inverse_case` | the inverse-branch selector configuration | when `x1=x2`, `y1≠y2`, both non-infinity: forces `same_x=1, same_y=0, is_double=0, is_inverse=1` |
| `output_mux_lhs_inf` / `output_mux_rhs_inf` / `output_mux_inverse` / `output_mux_generic` | `curve.rs` output mux `x3 = lhs_inf·x2 + …` etc. | one theorem per branch: given the selector boolean assignment, the mux equations force the output to the correct case (`P2`, `P1`, `∞`, or generic `(xg, yg)`) |
| `gated_on_curve_sound` / `gated_on_curve_trivial` / `enforce_on_curve_grumpkin_sound` | `curve.rs::enforce_on_curve_grumpkin` (`(1 − is_inf)·(y² − x³ + 17) = 0`) | the gated curve-membership check forces `y² = x³ − 17` (on Grumpkin) when `is_inf = 0` and is vacuous when `is_inf = 1` — closes the "input is on the curve" hypothesis used by every other curve theorem |
| `IsValidECAddWitness` / `EcAddSemantics` / `ec_add_in_circuit_generic_sound` / `ec_add_in_circuit_sound` | **the whole `ec_add_in_circuit` gadget** | **end-to-end soundness wrapper**: any prover witness satisfying the gadget's full constraint set (gated on-curve checks + booleans + selectors + gated slopes + output mux) produces an output `(x3, y3, is_inf3)` that equals the algebraically correct Grumpkin group-law result in every branch (`∞ ⊕ P`, `P ⊕ ∞`, `P ⊕ (−P)`, `P ⊕ P`, generic `P1 ⊕ P2`) |

The doubling-case closure is stated for Grumpkin (`y² = x³ + b`, `a = 0`) because
the gadget's doubling slope `λ·(2·y1) = 3·x1²` hard-codes `a = 0`; that matches
the actual constraint emitted by `curve.rs`. **`ec_add_in_circuit_sound` is the
single statement of full Grumpkin point-addition gadget soundness** — it packages
the gated curve membership, selector under-constraint slack, slope determinism,
addition-law closure, and 4-way output mux into one theorem against a
semantic Grumpkin group-law relation `EcAddSemantics`.

[`Formal/Ecdsa.lean`](Formal/Ecdsa.lean) — the LSB-first double-and-add
scalar-multiplication ladder used by `curve.rs::scalar_mul_in_circuit` /
`msm_in_circuit` and `ecdsa.rs`. Proven abstractly over any additive commutative
group `G`, so it composes with `Curve.lean` by specialising `G` to the Grumpkin
point group:

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `ladder_step_correct` | one loop body of `scalar_mul_in_circuit` | `(acc, P) ↦ (acc + b·P, 2·P)` for `b ∈ {0,1}` |
| `ladder_correct` | the whole ladder run from `(0, P)` over a bit-list `bs` | accumulator equals `bitsToNat(bs) • P`, running point equals `2^bs.length • P` |
| `ladder_determinism` | corollary | bit-vectors encoding the same scalar produce the same ladder output — combined with `bits_unique`, this closes the under-constraint story for the scalar-mul ladder |

[`Formal/NonNative.lean`](Formal/NonNative.lean) — the **prover-aided modular
product** pattern that `crates/acir-r1cs/src/gadgets/ecdsa.rs` builds every
secp256k1 base- and scalar-field multiplication on top of. The 256-bit moduli
don't fit in BN254 `Fr`, so each `c = a·b mod m` is lowered to a prover-supplied
quotient `q` and remainder `c` checked against the *integer* identity
`a·b = q·m + c` (limb-by-limb in `Fr`) plus a range check `0 ≤ c < m`:

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `mul_mod_sound` | the abstract content of `ecdsa.rs::mul_mod` | over ℕ: `0 < m`, `c < m`, `a · b = q · m + c` ⇒ `c = (a · b) % m`. The integer identity + range check fully pin the modular product; no prover slack in `c`. |
| `mul_mod_complete` | matching completeness | for any `a, b, m` with `m > 0`, a valid `(q, c)` exists (the division-algorithm pair) — the gadget admits all honest witnesses |
| `valOfLimbs` / `valOfLimbs_zero` / `valOfLimbs_succ` | `Limbs256::recompose` shape | `valOfLimbs ls β = Σᵢ ls i · β^i` over `Fin n`, plus base/cons identities so limbwise statements compose with whole-integer statements |
| `mul_mod_via_limbs` | the gluing theorem | `mul_mod_sound` lifted to limb-vectors: integer identity at the recomposed values + range ⇒ modular product at the recomposed values — the exact shape the `ecdsa.rs` limb-by-limb constraints are designed to discharge |
| `colSum_eq` | Cauchy product identity over limb base `β` | `valOfLimbs a · valOfLimbs b = Σₖ colSum a b k · β^k` — products of limb vectors expand as a sum of per-column partial-product sums |
| `carry_telescope` / `colSum_carry_telescope` | the schoolbook-multiplication carry recurrence | per-column equations `colA k + carry k = colB k + β · carry (k+1)` with boundary `carry 0 = carry (2n) = 0` ⇒ `Σₖ colA k · β^k = Σₖ colB k · β^k`. The carry-no-wrap argument is exactly that carries are plain ℕ — the gadget's `Fr`-level constraints must keep carries below the field modulus, which is the obligation owed by the lowering layer |
| `mul_mod_via_limbwise_constraints` | **full ℕ-level soundness chain** for `ecdsa.rs::mul_mod` | per-output-column equations `colSum a b k + carry k = colSum (q·m + c) k + β · carry (k+1)` + boundary carries + range `c < m` ⇒ `valOfLimbs c = (valOfLimbs a · valOfLimbs b) % valOfLimbs m`. The end-to-end ℕ statement closing secp256k1 non-native multiplication |
| `add_val_no_wrap` / `mul_val_no_wrap` | `Fr` → `ℕ` bridge | for `a, b : ZMod r` with `a.val ⊕ b.val < r` (sum or product), the field arithmetic equals the integer arithmetic — every column equation lifts to ℕ exactly |
| `colSum_le` / `carry_le` | budget bounds | column sums and carries bounded by `(k+1)·(β−1)²` and `(k+1)·(β−1)²` resp., so the entire ledger of column equations fits in `Fr` with margin (`< 2^205 < r ≈ 2^254` for secp256k1's `n=4, β=2^64`) |
| `mul_mod_via_Fr_limbwise_constraints` | **full Fr-level soundness chain** for `ecdsa.rs::mul_mod` | column equations stated **in `Fr`** for the secp256k1 case (`n=4, β=2^64`) + per-limb `< β` + carry budget hypothesis ⇒ modular product is correct. **This is the end-to-end Fr Lean statement closing the secp256k1 non-native multiplication soundness story** |

The Fr-level no-wrap chain is the analogue of `two_pow_lt_r` for `range_unique`:
the carries `carry k < (k+1)·(2^64−1)² < 2^131` and `β · carry < 2^195` plus
column sums `≤ 8 · (2^64−1)² < 2^131` all stay well below `r ≈ 2^254`, so the
`Fr` constraints lift to `ℕ` exactly and `mul_mod_via_limbwise_constraints`
finishes.

`range_unique` is the heart of the determinism story: *functional determinism* of the range
gadget — the precise property that rules out the under-constraint bug class
(a prover choosing a different witness for the same public value). The width
cap `n ≤ 253` is what keeps the field sum below the BN254 scalar modulus `r`
(`two_pow_lt_r : 2^253 < r`) so it cannot wrap.

The proofs use only the standard mathlib axioms (`propext`, `Classical.choice`,
`Quot.sound`) plus three primality axioms for the secp256k1, secp256r1, and
BN254 base-field moduli (Lean's kernel can't `decide` 254/256-bit primality;
each is documented at its declaration site). No `sorry`. CI checks this with
`#print axioms`.

## Building

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager); the pinned toolchain is in [`lean-toolchain`](lean-toolchain) and the
mathlib revision is pinned in `lake-manifest.json`.

```sh
cd formal
lake exe cache get   # download mathlib's prebuilt .olean cache (minutes)
lake build           # check all proofs (seconds, once mathlib is cached)
```

CI runs this on every push via [`.github/workflows/lean.yml`](../.github/workflows/lean.yml).

[`Formal/EcdsaVerify.lean`](Formal/EcdsaVerify.lean) — **end-to-end ECDSA
verifier soundness wrapper.** Packages the per-primitive theorems
(`mul_mod_via_Fr_limbwise_constraints` + `ladder_correct`) into one statement
against the textbook ECDSA-verify predicate `EcdsaVerifyRel`. Parametric over
the curve point group `G : Type*` `[AddCommGroup G]`; verified `AddCommGroup`
instances for secp256k1 / secp256r1 live in `Formal.Secp256k1Group` /
`Formal.Secp256r1Group` (Grumpkin is in `Formal.Curve`).

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `EcdsaVerifyRel` | textbook ECDSA-verify (FIPS 186-4 §6.4 / SEC 1 §4.1.4) | `r, s ≠ 0 ∧ ∃ w, s·w = 1 ∧ r = xProj((e·w)•g + (r·w)•Q)` |
| `IsValidEcdsaWitness` | `ecdsa_verify_with_curve` intermediate-state predicate | gadget's witness shape: range-check + `s·w=1` + `u₁=e·w` + `u₂=r·w` + `R=u₁•g+u₂•Q` + `r=xProj R` |
| `ecdsa_verify_sound` | — | any `IsValidEcdsaWitness` implies `EcdsaVerifyRel` |
| `mul_mod_lifts_to_ZMod` | bridge | `u.val = (a.val·b.val) % n ⇒ u = a·b` in `ZMod n` (composes `mul_mod_via_Fr_limbwise_constraints` into `u1_def` / `u2_def`) |
| `ladder_gives_R_def` | bridge | `acc₁ = u₁•g, acc₂ = u₂•Q, Rpt = acc₁+acc₂ ⇒ Rpt = u₁•g + u₂•Q` (composes `ladder_correct` into `R_def`) |
| `ecdsa_verify_compose` | end-to-end | takes the seven per-primitive hypotheses (range, mod-inverse, the two `mul_mod` ℕ-identities, two `ladder_correct` outputs, ec_add, final eq) and concludes `EcdsaVerifyRel` directly |

[`Formal/Sha256.lean`](Formal/Sha256.lean) — **structural** soundness layer
for `crates/acir-r1cs/src/gadgets/hash.rs`. Full bit-equivalence of SHA-256
is left to SAT/SMT bit-blasting (faster, better fit than a proof assistant);
this file builds the *compositional* story over the
already-proven per-op gadgets in [`Formal/Bitwise.lean`](Formal/Bitwise.lean)
and [`Formal/Arith.lean`](Formal/Arith.lean):

| Definition / Theorem | Source | Statement |
|----------------------|--------|-----------|
| `Word32 := Fin 32 → Bool` | `bitwise.rs::Word32` | LSB-first ordered bit-vector matching the gadget's `Word32` layout |
| `rotr` / `shr` / `not32` / `and32` / `xor32` | pure FIPS 180-4 spec | bit-level definitions of the Word32 ops |
| `Ch` / `Maj` / `Σ₀` / `Σ₁` / `σ₀` / `σ₁` | FIPS 180-4 §4.1.2 | the SHA-256 round / message-schedule helper functions |
| `rotr_sound` / `shr_sound` | `bitwise.rs::rotr` / `::shr` | per-bit constraints (boolean permutation / projection) force the output to equal the pure-spec rotation / shift |
| `not32_sound` / `and32_sound` / `xor32_sound` | `bitwise.rs::not` / `::and` / `::xor` lifted to Word32 | per-bit constraints force the output to be the spec'd boolean op |
| `Ch_bit_sound` / `Maj_bit_sound` | composition over `not32` / `and32` / `xor32` | per-bit constraints of the constituent gadget calls force the output to equal the FIPS Ch / Maj |
| `bigSigma0_bit` / `bigSigma1_bit` / `smallSigma0_bit` / `smallSigma1_bit` | composition over `rotr` / `shr` / `xor32` | the structural defining identities for the four sigma functions |
| `MessageScheduleStep` / `_iff` | `hash.rs::sha256_compression` (message-schedule loop) | predicate / equivalence capturing the message-schedule recurrence `W[t] = addMod32(W[t-16], σ₀(W[t-15]), W[t-7], σ₁(W[t-2]))` |

This is the **structural** layer — it shows the SHA-256 spec composes out of
the proven primitives without bit-blasting any 2³² × 2³² Word32 search space.
Full compression equivalence (the gadget's 64-round loop output equals the
FIPS spec output) is discharged by `Formal.Wrappers.sha256_iter_of_rel`
composed with `Formal.BitwuzlaCompose.sha256_closed_chain`;
`crates/tests/tests/bitwuzla_sha256.rs` provides an independent SMT-level
cross-check over all 768-bit inputs.

## Scope / what's next

Proven, end-to-end:
* The **boolean primitive**, **range-gadget determinism** (the heart of the
  under-constraint story), and the **bitwise / carry gadgets** in `bitwise.rs`.
* The **Poseidon2 S-box** plus the parametric full-permutation determinism
  chain (linear / constant / full-round / partial-round / permutation) **and**
  the concrete BN254 / `t = 4` Poseidon2 specialisation with all 256 round
  constants and both matrices ([`Formal/Poseidon2Bn254.lean`](Formal/Poseidon2Bn254.lean)).
* **Embedded-curve point addition** on Grumpkin end-to-end: gated curve
  membership + generic and doubling algebra closure + inverse-case predicate +
  selector under-constraint slack + 4-way output mux, packaged into one
  `ec_add_in_circuit_sound` theorem against a semantic group-law relation.
* The **LSB-first double-and-add scalar-multiplication ladder** (per-bit
  invariant + full ladder correctness + scalar-level determinism, abstractly
  over any additive commutative group — composes with the curve theorems).
* The **full non-native modular-multiplication soundness chain** for
  `ecdsa.rs::mul_mod` — abstract prover-aided identity (`mul_mod_sound`) +
  Cauchy column-sum identity (`colSum_eq`) + ℕ-carry recurrence
  (`colSum_carry_telescope` → `mul_mod_via_limbwise_constraints`) + **the
  Fr-level no-wrap argument** lifting the ℕ-carry obligation to the actual
  field-level constraints emitted by the gadget for the secp256k1 case
  (`n = 4, β = 2^64`, `mul_mod_via_Fr_limbwise_constraints`).
* A **SHA-256 structural soundness layer** ([`Formal/Sha256.lean`](Formal/Sha256.lean))
  showing the FIPS 180-4 primitives (Ch, Maj, Σ₀, Σ₁, σ₀, σ₁) and the
  message-schedule step compose out of the already-proven per-bit gadgets.

What remains scoped out of Lean:
* **External SMT cross-validation** for SHA-256, Keccak, BLAKE2s, BLAKE3,
  and AES-128 round-step bit-equivalence — handled by the QF_BV harnesses
  in `crates/tests/tests/bitwuzla_*.rs` (independent of the pure-Lean
  `<gadget>_round_bit_equivalence` theorems in `Formal.BitwuzlaCompose`).
* External audit, fuzzing-extension, and Kani work on the on-chain
  verifier — engineering, not FV.
