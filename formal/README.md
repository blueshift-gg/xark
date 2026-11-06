# `formal/` — Lean 4 proofs of gadget soundness

Machine-checked soundness proofs for the R1CS gadgets that xark compiles from
its language and frontend (`crates/lang`, `crates/frontend`), written in **Lean 4** against
**mathlib**. Covers the field-arithmetic gadgets where SMT / bit-blasting
blows up and a proof assistant is the right tool.

Where the Kani harnesses (in `crates/verifier`) discharge the
on-chain verifier's byte logic by *bounded model checking*, these Lean
theorems are *deductive* proofs that hold over **all** field assignments —
there is no input bound.

## What is proven

### Trusted, and what the statements do not say

Not proven: completeness, that the honest prover's witness satisfies the rows (the
completeness proofs were deleted to cut the Lean build; release KATs, edge cases and
random sampling exercise the honest path instead); the rows outside `#[gadget]` calls
(glue, user circuits); that the per-call specs compose (`coverage-allowlist.txt`'s
reasons are prose; `Formal/Circuits/` is the first step, below); the Groth16 layer; the
minimizer the keyed rows go through.

Trusted Rust, by line count: the recorder and exporter that cut a call's rows into a
template (`crates/frontend/src/gadgets.rs`, 794 lines; `xtask/src/lean.rs`, 663) and the
coverage classifier (`xtask/src/coverage.rs`, 992). The fixed-base
comb tables and offset points the ECDSA and Ed25519 circuits read (`COMB`, `OH`, `HH` from
`gadgets/xark-secp256k1/build.rs`, `xark-secp256r1/build.rs`, `xark-ed25519/build.rs`,
94 + 94 + 144 lines of `k256`/`p256`/`curve25519` arithmetic) are constants no Lean
theorem checks: a wrong entry would make the circuit accept a wrong `C·G`.

What a statement says less than its name suggests:

* `EcAddK1Check.Spec` ([`Formal/EcK1Check.lean`](Formal/EcK1Check.lean)) pins `(x₃, y₃)`
  only in `ZMod p` with limbs below `2⁶⁴`: no row asks `x₃ < p`, so `x₃` and `x₃ + p` both
  satisfy it when `x₃ < 2³² + 977`. The chain stays sound because every consumer reads the
  point in `ZMod p`; the hinted `R.x` that `fake_glv_check_k1` compares with `r` is the one
  coordinate the circuit forces canonical (`OnCurveK1Check.x_lt_p`).
* `require_lt::<4, 64>(x, NN1)` and `::<8, 32>(x, M1_K1)` are proven as `x ≤ m₋₁` read
  limb-wise (`RequireLt.Spec`); that the constant limbs of `NN1` are `n − 1`, so `x < n`,
  is a fact about a Rust constant with no Lean theorem yet (`M1_K1 = p − 1` has one:
  `x_lt_p`). The whole-circuit theorem needs it and will carry it.
* `ScalarMul.Spec` and `WideScalarMul.Spec` (Grumpkin) give the output as the affine
  point `s·P`, which does not exist at `s = 0`: the rows reject `s = 0`. A soundness
  statement, not a liveness one: a caller that can reach `s = 0` gets no proof, not a
  wrong one.
* `EdTorsionCheck` is the cofactored check `x·y·(x² + y²) = 0`: it accepts exactly the
  points of order dividing 8 (`Ed25519.torsion_iff`), the check RFC 8032 implementations
  make, not a prime-order-subgroup membership test.
* `Sbox.soundness` (AES) assumes its eight input plugs are bits; the producers are the
  covered `to_bits` and `xor` calls the coverage report names, not the template.

CI (`lean.yml`) runs `lake build`, then [`AxiomCheck.lean`](AxiomCheck.lean) fails unless every harness has its
`soundness` theorem (and its `Consts` module, when it has one), and
every declaration in `Formal`, legacy included, depends only on `propext`,
`Classical.choice` and `Quot.sound`: no `sorry`, no `axiom`, no `native_decide`. The
secp256k1, secp256r1 and BN254 primes are proven prime by kernel-checked Pratt
certificates ([`Formal/CurvePrimes.lean`](Formal/CurvePrimes.lean), machinery in
[`Formal/Pratt.lean`](Formal/Pratt.lean)).

Each theorem mirrors the exact constraints the Rust builder enforces.

[`Formal/Gadgets.lean`](Formal/Gadgets.lean) — boolean primitive and range gadget:

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `boolean_sound` | the booleanity row `b·b = b` (`frontend/src/builder.rs::decompose_bits`, `Field::require_bool`) | `b * (b - 1) = 0 ↔ b ∈ {0,1}` in any field |
| `range_unique` | `frontend/src/builder.rs::decompose_bits` | the bit-vector is **uniquely determined** by the recomposed value (no under-constraint slack), for widths `n ≤ 253 = MAX_BITS` |
| `bits_unique` | (lemma) | binary recomposition `Σᵢ 2ⁱ·bᵢ` is injective on bit-vectors over `ℕ` |

[`Formal/Bitwise.lean`](Formal/Bitwise.lean) — bitwise primitives (each proves
the output bit is determined *and* equals the intended boolean op, staying in `{0,1}`):

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `and_sound` | `&` on bits (`frontend/src/host.rs::int_bin`, `aᵢ·bᵢ = outᵢ`) | `out ∈ {0,1}` and `out = 1 ↔ a = 1 ∧ b = 1` |
| `xor_sound` | `frontend/src/builder.rs::emit_xor` (`(2a)·b = a + b − out`) | constraint pins `out = a + b − 2ab`; `out ∈ {0,1}` and `out = 0 ↔ a = b` |
| `not_sound` | `Field::not` (`lang/src/lang.rs`, `1 − a`) | `1 − a ∈ {0,1}` and `1 − a = 1 ↔ a = 0` |

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
product** pattern that `gadgets/xark-secp256k1/src/lib.rs` builds every
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

CI (`lean.yml`) builds with `lake build`; then [`AxiomCheck.lean`](AxiomCheck.lean)
fails unless every harness under
`templates/` has its `soundness` theorem (and its `Consts` module, when it has one), and
every declaration in `Formal` depends only on `propext`, `Classical.choice` and
`Quot.sound`: no `sorry` (its axiom `sorryAx`), no `axiom`, no `native_decide`, except the twelve hand-restated
lemmas it lists (GF(2⁸) tables, the secp256k1 GLV constants), each of which goes with the
template proof of its gadget. The secp256k1, secp256r1 and BN254 primes are proven prime
by kernel-checked Pratt certificates ([`Formal/CurvePrimes.lean`](Formal/CurvePrimes.lean),
machinery in [`Formal/Pratt.lean`](Formal/Pratt.lean)).

[`Formal/Rewrites.lean`](Formal/Rewrites.lean) — **the stable frontend's
constraint-reducing rewrites preserve the circuit.** The theorems above are stated
over the rows a gadget emits; the stable frontend (`crates/frontend`) emits fewer
rows than the MIR frontend for the same program, and each saving is one of these
rewrites. Over an explicit R1CS model (linear combinations, rows `a · b = c`, and
syntactic substitution), each is proven *exact*: the rewritten rows' solutions are
precisely the original solutions with the eliminated variable forgotten — nothing
gained for a forger, nothing lost for an honest prover. So every gadget theorem,
and the public-input relation the proof checks, carries over unchanged.

| Theorem | Mirrors | Statement |
|---------|---------|-----------|
| `eval_subst` | substituting an LC for a variable | evaluating `l[v := e]` at `τ` is evaluating `l` at `τ[v ↦ e(τ)]` |
| `elim_sound` | the common core | if the rows force `v = e` (`e` free of `v`), `Sat S[v := e] τ ↔ ∃ x, Sat S τ[v ↦ x]` |
| `cse_sound` | `builder.rs::emit_mul_var` product reuse | with `A · B = x` a row, the MIR rows `A · B = y` + uses of `y` ≡ the stable rows using `x` |
| `inline_sound` | `builder.rs::materialize` (MIR names operands over 8 terms) | the MIR `L · 1 = t` + uses of `t` ≡ the stable rows using `L` in place |
| `fold_sound` | `host.rs` `mul` with an operand constant in the field (e.g. after mod-`p` reduction zeroes a coefficient) | a row `A · B = t` whose product equals a linear form `e` + uses of `t` ≡ `e` in place |
| `const_mul_sound` | `host.rs` constant `pow` folding | a row `a · b = t` of constants + uses of `t` ≡ the constant `a·b` in place |
| `gated_sat` | `host.rs::require_gated` (a `require` in a witness-branch arm) | for a `{0,1}` guard `G`, the row `G · D = 0` holds iff `G = 1 → D = 0` |
| `guard_mul` | nested arms' guards (`host.rs::guard`) | a product of `{0,1}` values is `{0,1}`, and `1` iff both are |
| `pin_dead` | `builder.rs::gate_input` / `pin_dead` (hints in an arm) | a hint reads `g·x` and is pinned by `(1 − g)·h = 0`: `x` and no pin where taken, `0` and `h = 0` where not |
| `select_taken` / `select_untaken` | `interp.rs::merge` | the select `e + c·(t − e)` is `t` at `c = 1` and `e` at `c = 0`, whatever the other arm holds |

The last three are why a `require` may sit in a branch arm: both arms run, but the
untaken arm's requirements are vacuous and its values never reach the result.

Reducing constants modulo `p` needs no theorem: the rows are over `ZMod p`, where
`c` and `c mod p` are one element. The R1CS bridge tests in
`crates/lang/tests/snapshot.rs` pin both frontends' gate counts and name the rewrite
behind each difference (SHA-256 `Maj` reusing the previous round's `a ∧ b`, a
3-limb square's repeated cross products, Poseidon's constant capacity-lane S-box).

[`Formal/Minimize/`](Formal/Minimize/) — **the keyed rows are certified against the
minimizer's input.** Every minimizer run on the keyed path (each template body and
the top stream in `expand_function_blob_reduced`, then the global `xark_ir::minimize`)
writes a certificate: its steps (variable, defining row, substituted form) and, for each
original row, its fate and the multipliers of the substitutions made in it. The checker
[`Check.lean`](Formal/Minimize/Check.lean), compiled as `lake exe minimize_check` (it
imports only core Lean), accepts or refuses it, and
[`Sound.lean`](Formal/Minimize/Sound.lean) proves what acceptance means over `ZMod r`,
in `Rewrites.lean`'s `Sat`:

| Theorem | Statement |
|---------|-----------|
| `check_sound` | every solution `τ` of the minimized rows extends to the original rows: `Sat (orig P) (recompute P τ)`, where `recompute` sets only the eliminated variables, each to its form (`elim_sound`'s substitution, from the last step back) |
| `check_complete` | every solution `σ` of the original rows solves the minimized rows, and `recompute P σ = σ` (the checker refuses no honest certificate) |
| `check_internal` | every eliminated variable is listed `Internal`: no public or private input |
| `check_inputs` | the output lists every non-internal input variable with its visibility |

`cargo xtask minimize-check` runs the checker on every example and requires the
certified rows to hash to the example's line in `tests/stable-digests.txt`, so the
certified rows are the keyed rows. Trusted: the certificate encoding (Rust writer,
`MinimizeCheck.lean` reader) and that the writer gives the minimizer's real input and
output rows.

## Proofs over the exact R1CS: gadget templates

The theorems above restate a gadget's rows by hand. A **template** proof is about
the rows the frontend really emits, and CI fails when the code drifts from them.

* `#[gadget]` (`xark::gadget`) on a gadget function marks each call with its name
  and its inputs' and result's field elements. The markers exist only in a build
  with `--cfg xark_gadgets`, which `lean-export` uses for its harness; every
  other build compiles them to nothing (no imports, no writes, same rows). The
  frontend records the call (`crates/frontend/src/gadgets.rs`) and refuses to
  export one whose rows it can't attribute exactly to the call.
* `cargo xtask lean-export <gadget>` builds the harness
  `formal/templates/<gadget>/`, a circuit that calls the gadget once on fresh
  private inputs, and writes that call to `Formal/Templates/<Gadget>.lean` as a
  [`Xark.Template.Template`](Formal/Template.lean): its `rows` (`Xark.R1cs` rows
  `a · b = c` over `ZMod r`, so [`Formal/Rewrites.lean`](Formal/Rewrites.lean)'s
  lemmas apply; coefficients are the integers the frontend holds), its `hints`
  (the witness ops, with the solver's meaning in `Hint.run`), its `inputs` and
  `outputs` as linear combinations, and the variables' roles: `.plug i` is the
  `i`-th variable its inputs read, `.wit j` the `j`-th it allocated. `hash` is the
  sha256 of that data.
* `cargo xtask lean-export --check` (the `templates` job in `lean.yml`) re-exports
  every harness and fails, naming the gadget and both hashes, when one differs
  from its committed file.

| Theorem | Template | Statement |
|---------|----------|-----------|
| `Xark.Templates.Add32.soundness` | `xark_bits::add32` (33 booleanity rows + the recomposition) | on input words of bits, every assignment satisfying the rows outputs exactly the bits of `(a + b) mod 2³²` |
| `Xark.Templates.Xor.sat_iff` / `Or.sat_iff` | `Field::xor` / `Field::or` (one row each) | for any inputs, the row holds iff the output is `a + b − 2ab` / `a + b − ab` |
| `Xark.Templates.Xor.soundness` / `Or.soundness` | same | on input bits, every satisfying assignment outputs the bit `a ⊕ b` / `a ∨ b` |
| `Xark.Templates.{Xor3,Maj3,Chi}.soundness` | `xark_bits::xor3` / `maj3` / `chi` (one row each, `z` hinted: Verified-zkEVM/clean PR #395, zkGolf T1/T2), in `Formal/HashOps.lean` | on input bits, every satisfying assignment outputs `a ⊕ b ⊕ c` / `maj(a, b, c)` / `a ⊕ (¬b ∧ c)`: each row is linear in `z` with a multiplier in `±1…±4` on `{0,1}³`, so the hinted bit is unique |
| `Xark.Templates.Ch.sat_iff` / `soundness` | `xark_bits::ch` (`e · (f − g) = w`, output `g + w`; bellman `sha256_ch`) | for any inputs the output is `g + e·(f − g)`; on bits, `e ? f : g` |
| `Xark.Templates.{Xor3,Maj3,Chi,Ch}.outs_isBit` | `--coverage`'s bit producers | on input bits, the output is a bit |
| `Xark.Reduce.model_sound` | `xark_bits::reduce::<N>` (`N − 1` hinted bits pinned boolean, top carry `t = sum − Σ 2ⁱ·bᵢ` pinned by `t·(t − 2^(N−1)) = 0`; zkGolf 650c4497), for any `33 ≤ N ≤ 253` | with no input assumption, every satisfying assignment has `sum < 2ᴺ` and outputs its low 32 bits |
| `Xark.Templates.Reduce{33,34,35,36}.soundness` | `reduce::<N>` at each production width (harness `formal/templates/reduce__<N>`) | the two above at `N`; `rows_eq` etc. show by `decide +kernel` that the export is the model |
| `Xark.Templates.ToBits.model_sound` | every bit decomposition (`builder.rs::decompose_bits_gated`, which `Field::to_bits`, `uN` inputs, comparisons and native bitwise ops use): bits `1..n` hinted, `b₀ = x − Σ 2ⁱ·bᵢ`, row `b₀(b₀ − 1) = 0` (zkGolf T9), at any width `n ≤ 253` | every satisfying assignment has `x < 2ⁿ` and outputs exactly `x`'s `n` bits |
| `Xark.Templates.ToBits.soundness` | `Field::to_bits::<8>` (the exported template is the model at `n = 8`) | the above at `n = 8` |
| `Xark.Templates.ToBits.soundness_of` | a template equal to the model at `m + 1 ≤ 253` | the above for it, at width `m + 1` (`SpecAt (m + 1)`) |
| `Xark.Templates.ToBits{17,32,64,75,98,106,127,249}.soundness` | `Field::to_bits::<n>` at every other width production uses (harness `formal/templates/to_bits__<n>`) | `soundness_of` at `m = n − 1`; `rows_eq` etc. show by `decide +kernel` that the export is the model |
| `Xark.Templates.ToBitsCanonical.soundness` | `Field::to_bits_canonical` (bits `1..253` hinted, bit `0` = `x − Σ 2ⁱ·bᵢ`, then MSB-first against `r − 1`: `b·b = b` and `all := all·b` at its one-bits, `(1 − all − b)·b = 0` at its zero-bits; bellman `into_bits_le_strict`, ACL2 `bits-lt-prime` @ 95d4195; 353 rows) | with no input assumption, every satisfying assignment outputs exactly the 254 bits of `x.val`, `x`'s representative in `[0, r)` (bug checklist 3: no `x + r`) |
| `Xark.Templates.ToBits.spec_isBit`, `ToBitsCanonical.spec_isBit`, `Xor.outs_isBit`, `Or.outs_isBit`, `Add32.outs_isBit` | `--coverage`'s bit producers | on inputs meeting `Assumptions`, every output is a bit |
| `Xark.Templates.ToBits.spec_of_bits` | a `to_bits` the frontend answers without rows because its input is `Σ 2ⁱ·bᵢ` of proven bits (`bit_sum_shortcut`) | that input is below `2ⁿ` and the `bᵢ` are its bits |
| `Xark.Templates.Add32.isBit_one_sub` / `isBit_mul`, `isBit_of_mul_self`, `ToBits.isBit_of_mul_sub_one` | `--coverage`'s proven bits | `1 − b` and `a·b` of bits are bits; rows `x·x = x` and `x·(x − 1) = 0` pin `x` to a bit |
| `Xark.Templates.Xor.fold_lhs`, `fold_rhs` / `Or.fold_lhs`, `fold_rhs` | `host.rs` `Intr::Xor`/`Or` with a constant operand `k` | the template with `k` substituted holds iff the output is `k + (1 − 2k)·x` / `k + (1 − k)·x`, the linear form the frontend emits in place of the row (exact by `elim_sound`) |
| `Xark.Templates.Add32.soundness_consts` / `assumptions_consts` | `add32` with constant plugs | the two above for `add32`; the assumptions hold when the constants are bits (`Templates/Consts/Add32.lean`) and the other inputs are |
| `Xark.Templates.CondSwap.soundness` | `xark_merkle::cond_swap` (booleanity `s·s = s` + the product `s·(b − a)`) | every satisfying assignment has `s ∈ {0,1}` and outputs `s ? (b, a) : (a, b)`; no input assumption |
| `Xark.Templates.CondSwap.root_binds` | `xark_merkle::merkle_root`'s levels | satisfied, wired levels have bit indices and compute `merkleRoot H leaf path`, assuming (unproven) that `hash2`'s rows compute a function `H` and each level emits the template's rows |
| `Xark.Templates.ScalarToBits.soundness` | `xark_bignum::scalar_to_bits` (86 + 86 + 84 hinted bits of a 3 × 86-bit scalar) | with no input assumption, the limbs are below `2⁸⁶`, `2⁸⁶`, `2⁸⁴` and the outputs are their bits |
| `Xark.Templates.PedersenHash.soundness` | `xark_pedersen::pedersen_hash` (2 × [128-bit decomposition, 42 `lookup3_xy` + 1 two-bit window, 43 incomplete adds, the `−off·G` correction] + guard + final add; 774 rows) | with no input assumption, every assignment satisfying the rows has scalars in `[1, 2¹²⁸)` and outputs the affine coordinates of `m₀·G₀ + m₁·G₁` |
| `Xark.DoubleAdd.dblAdd_sound` | — (`Formal/DoubleAdd.lean`, any short Weierstrass curve with `2 ≠ 0` and no 2-torsion) | the fused step's rows (guard, `λ1`, `(λ1 + λ2)(x_A − x_R) = 2y_A`, `λ2`) force `(A + S) + A` |
| `Xark.Templates.MulCertK1.soundness` | `xark_bignum::mul_cert_k1` (8 × 32-bit limbs folded mod `f(Y) = Y⁸ − Y − 977` (`f(2³²) = p`): `mul_cert_r1`'s 15 product rows at `0, ±1..±7`, `to_bits::<40>` of `K + 8`, `to_bits::<47>` of `T + 8` with `T = 2⁶⁴·K − H`, the exact row `L + c·K = 2¹⁹²·T` (`c = 2³² + 977`): 103 rows) | if every limb of `a`, `b`, `t` is below `2³⁴` (inside `ec_add_k1_check`, `ec_double_add_k1_check`, `on_curve_k1_check` proven by `EcK1Check`; at `ecdsa_verify_packed`'s `phi_x` calls on `Q.x` and the hinted `R.x` by `unpack8` and `range_check_limbs::<8, 32>` rows), every satisfying assignment has `a·b ≡ t (mod p)`, `p` secp256k1's base field; the no-wrap bound (every column and both sides of the exact row below `2²⁵³`) is proven, not sampled (`lo_bds`, `hi_bds`, `int_sound`) |
| `Xark.EcK1.add_sound` | `xark_bignum::ec_add_k1` (the group-law step of `EcAddK1Check.soundness`) | on affine secp256k1 points, the guard `w·(x_Q − x_P) = 1`, slope, `x₃`, `y₃` certificates force `(x₃, y₃) = P + Q` |
| `Xark.Templates.EcDoubleAddK1Check.soundness` / `outs_lt` | `xark_bignum::ec_double_add_k1_check`, the rows of the fused step `ec_double_add_k1` (`to_bits::<32>` of `w`, `λ₁`, `x_R`, `λ₂`, `x₃`, `y₃`, and 6 nested `mul_cert_k1` rows: guard, `λ₁`, `x_R`, `λ₂`, `x₃`, `y₃`) | if the limbs of `A`, `x_S` are below `2³²` and of `y_S` below `2³³` (a caller's `2p − y`), every satisfying assignment has every hinted limb below `2³²`, `x_A ≠ x_S` and for affine `A`, `S`, `(x₃, y₃) = (A + S) + A` in `ZMod p` (via `DoubleAdd.dblAdd_sound`) |
| `Xark.OddRecode.accum_eq` / `digits_eq` / `chain_value` / `table_entry` / `odd_recode` | `xark_secp256k1::ecdsa_verify_packed`'s 65 steps over `fake_glv_check_k1`'s digits (`cₘ = kₘ + 2⁶⁴`, so `2c − (2⁶⁵ − 1) = 2kₘ + 1`) and `select8` | `n` fused steps from `O` reach `2ⁿ·O + Σⱼ 2^(n−1−j)·Sⱼ`; digits `2·bit − 1` spell `k = 2c − (2ⁿ − 1)`; the 8-entry table read at `c₁ ⊕ cⱼ`, negated at `c₁ = 0`, adds `Σₘ σ(cₘ)·Pₘ`; each odd `|k| < 2ⁿ⁺¹` has exactly one such `c` |
| `Xark.Templates.OnCurveK1Check.soundness` | `xark_bignum::on_curve_k1_check`, the curve equation of `on_curve_k1` (`to_bits::<32>` of `s`, `z`; `mul_cert_k1` rows `x·x = s`, `y·y = z`, `s·x = 2p + z − 7`) | if the limbs of `x`, `y` are below `2³²`, every satisfying assignment has `s`, `z` limbs below `2³²` and `(x, y)` a nonsingular point of secp256k1 (canonicity is `require_lt`'s, called first by `on_curve_k1`: `x_lt_p` below) |
| `Xark.Templates.OnCurveK1Check.x_lt_p` | `on_curve_k1`'s `require_lt::<8, 32>(x, M1_K1)` (the `RequireLt8x32` template with the constant plugs `p − 1`) | on `x` limbs below `2³²`, every satisfying assignment has `x < p`: the hinted `R.x` of `ecdsa_verify_packed` is canonical, so `fake_glv_check_k1`'s `x_R = r + t·n` (read from the same limbs by `x64`) cannot be met by `x_R + p` (gnark GHSA-7fx8) |
| `Xark.Templates.OneHot8.soundness` | `xark_bignum::one_hot8`, the fixed-base comb's selector (254 product rows) | on bit inputs, every satisfying assignment outputs `1` at `Σ 2ⁱbᵢ` and `0` at the other 255 positions |
| `Xark.Templates.Sbox.soundness` / `one_hot`, `Xark.Aes.table_eq` | `xark_aes::sbox`, the AES S-box as a select over its constant table (34 rows: 11-row low-nibble one-hot, 15-row mux over the high nibble, `to_bits::<8>`) | on bit inputs, every satisfying assignment outputs the bits of `S(Σ 2ⁱbᵢ)` (256 cases by `decide +kernel`), and the 16 selectors are one-hot and sum to 1; the table is `A(x⁻¹) ⊕ 0x63` over GF(2⁸) (FIPS-197 §5.1.1) |
| `Xark.Templates.FakeGlvCheckK1.soundness` / `glv_kernel` | `xark_secp256k1::fake_glv_check_k1`, the scalar side of fake GLV (ePrint 2025/933): `to_bits` of the digits `cₘ` (65 bits), `C`, `q₁`, `q₂`, the carries; `(k₂² + k₃²)·w = 1`; two carry chains; `x_R = r + t·n` by halves | if `r`, `s`, `e`, `x_R` limbs are below `2⁶⁴`: `cₘ < 2⁶⁵` and `C < 2²⁵⁶` with the outputs their bits (decomposition soundness), `A·s + B·r ≡ 0` and `C·s + B·e ≡ 0 (mod n)` for `A = k₀ + λk₁`, `B = k₂ + λk₃`, `B ≢ 0 (mod n)` (no nonzero `|k₂|, |k₃| ≤ 2⁶⁴` lies in secp256k1's GLV kernel), and `x_R = r + t·n`, `t ∈ {0, 1}`; the chains are checked as degree-2 polynomial identities in the plugs by `decide` (`csum₁`, `csum₂`, `xsum`, `closed`) |
| `Xark.FakeGlv.verify_sound` | `ecdsa_verify_packed`'s group check `M + C' = Q + φQ + R + φR`, i.e. `2·(C·G + A·Q + B·R) = O` | in a group killed by an odd prime `n`, with `A ≡ −B·u₂`, `C ≡ −B·u₁` and `B ≢ 0`, it forces `R = u₁G + u₂Q` |
| `Xark.Templates.MulCertR1.soundness` | `xark_bignum::mul_cert_r1` (8 × 32-bit limbs folded mod `f(Y) = Y⁸ − Y⁷ + Y⁶ + Y³ − 1` (`f(2³²) = p`): 15 product rows at `0, ±1..±7`, `to_bits::<43>` of `K + 2⁴²` and of `T + 2⁴²`, the exact row `L + K = 2⁹⁶·(K·p′ − H)`: 101 variables) | if every limb of `a`, `b`, `t` is below `2³⁵`, every satisfying assignment has `a·b ≡ t (mod p)`, `p` P-256's base field; the no-wrap bound (every column and both sides of the exact row below `2²⁵³`, ticket 24) is proven, not sampled (`lo_bds`, `hi_bds`, `int_sound`) |
| `Xark.Templates.RequireLt8x32.soundness` | `xark_bignum::require_lt::<8, 32>` (`on_curve_r1`'s canonicity of `Q` and the hinted `R`) | `RequireLt.Is 8 32` (`is_model`): on limbs below `2³²`, `x ≤ m − 1` |
| `Xark.EcR1.noTwoTorsion` / `short` / `add_sound` | P-256 (`Formal/DoubleAdd.lean`'s setting) | `x³ − 3x + b` has no root in `ZMod p` (kernel-checked `X^p mod f` and a Bézout identity), so P-256 is `DoubleAdd.Short`; the add certificates force `(x₃, y₃) = P + Q` |
| `Xark.Templates.EcDoubleAddR1Check.soundness` / `outs_lt` | `xark_bignum::ec_double_add_r1_check` (the fused step `(A + S) + A`: 6 range checks, 6 nested `mul_cert_r1`) | on `A`, `x_S` limbs below `2³²` and `y_S` limbs below `2³⁴`: `x_A ≠ x_S` and `(x₃, y₃) = (A + S) + A` (`DoubleAdd.dblAdd_sound` with `EcR1.short`) |
| `Xark.Templates.OnCurveR1Check.soundness` | `xark_bignum::on_curve_r1_check` (`x·x = s`, `y·y = z`, `s·x = z + 3x − b`) | on limbs below `2³²`, `(x, y)` is a nonsingular P-256 point (canonicity is `require_lt`'s, called first by `on_curve_r1`: `x_lt_p` below) |
| `Xark.Templates.OnCurveR1Check.x_lt_p` | `on_curve_r1`'s `require_lt::<8, 32>(x, M1_R1)` (the `RequireLt8x32` template with the constant plugs `p − 1`) | on `x` limbs below `2³²`, every satisfying assignment has `x < p`: the hinted `R.x` of `ecdsa_verify` is canonical, so `fake_glv_check_r1`'s `x_R = r + t·n` (read from the same limbs by `x64`) cannot be met by `x_R + p` (gnark GHSA-7fx8) |
| `Xark.Templates.FakeGlvCheckR1.soundness` | `xark_secp256r1::fake_glv_check_r1`, the 2-dim scalar side of fake GLV with no endomorphism: `to_bits` of `a`, `b` (130 bits), `C`, `q₁`, `q₂`, the carries; `(b − 2¹²⁹)·w = 1`; two carry chains; `x_R = r + t·n` by halves | on `r`, `s`, `e`, `x_R` limbs below `2⁶⁴`: `a, b < 2¹³⁰`, `C < 2²⁵⁶` with the outputs their bits, `A·s + B·r ≡ 0` and `C·s + B·e ≡ 0 (mod n)` for `A = a − 2¹²⁹`, `B = b − 2¹²⁹`, `B ≢ 0 (mod n)` (`0 < |B| ≤ 2¹²⁹ < n`), and `x_R = r + t·n`, `t ∈ {0, 1}` |
| `Xark.SignedMul.sound` | `xark_grumpkin::signed_mul`'s rows for any bit count and placement | on bits, rows that hold force `P` onto Grumpkin and the output to `s·P` |
| `Xark.Templates.ScalarMul.soundness` | `xark_grumpkin::scalar_mul` (3 on-curve rows, 128 booleanity rows, 6 + 127 × 7 fused-step rows, 10 final rows: 1036) | with no input assumption, the 128 inputs are bits, `P` is on Grumpkin and the output is the affine point `s·P` (so `s ≠ 0`) |
| `Xark.Templates.WideScalarMul.soundness` | `xark_grumpkin::wide_scalar_mul` (two `to_bits::<127>` + 254 fused steps) | with no input assumption, the limbs are below `2¹²⁷`, `P` is on Grumpkin and the output is `(lo + 2¹²⁷·hi)·P` |
| `Xark.Templates.MultiScalarMul.soundness` | `xark_grumpkin::multi_scalar_mul` (two 128-bit decompositions, the table `U = P + Q`, `V = P − Q`, 127 bit-pair steps of 10 rows, the 4-way `q`: 1569 rows) | with no input assumption, the scalars are below `2¹²⁸`, `P`, `Q` are on Grumpkin with `x_P ≠ x_Q`, and the output is `s₀·P + s₁·Q` |
| `Xark.Grumpkin.addOrderOf_eq_q` | — (`Formal/GrumpkinOrder.lean`) | a Grumpkin point `G ≠ 0` with `(q − 1)·G = −G` has order `q` (`q` prime by a Pratt certificate, `q_prime`) |
| `Xark.Grumpkin.check_sound` | — (`Formal/GrumpkinOrder.lean`) | a chain that passes `check` lists, at each index, the point `cᵢ·G` for its coefficient `cᵢ` |
| `Xark.EcK1.guard_ne`, `slope_free_without_guard`, `noTwoTorsion` | same | the guard rules out `x_P = x_Q`; without it `λ` is free (bug checklist 1); `y² = x³ + 7` has no point with `y = 0` (`−7` is not a cube mod `p`) |
| `Xark.Templates.RequireLt{3x86,3x85,4x64,24x86}.soundness` | `xark_bignum::require_lt::<L, B>` at each width production uses, on fresh `x`, `m₋₁` (chunked lexicographic compare, `4L + B` rows) | if `x`'s limbs are below `2^B`, every assignment satisfying the rows has `x ≤ m₋₁` as base-`2^B` numbers |
| `Xark.Templates.RequireLt{3x86,3x85,4x64,24x86}.soundness_consts` | same, with production's constant `m₋₁` | the above for the substituted rows; it needs nothing of the constants |
| `Xark.Templates.RequireLt{3x86,3x85,4x64,24x86}.is_model` | same | the exported rows are the parametric model of `Formal/RequireLt.lean` (`decide +kernel`); its theorems hold for every `L ≤ 32`, `B + 3 < 253`, but bind the gadget only at these widths |
| `Xark.Templates.RangeCheckLimbs{8x32,4x64,3x86}.soundness` | `xark_bignum::range_check_limbs::<L, B>` at each production width (per limb, `B` hinted bits pinned boolean and the recomposition row; `Formal/RangeCheckLimbs.lean`'s blocks) | with no input assumption, every limb is below `2^B` |
| `Xark.Templates.{Unpack,Unpack4}.soundness` | `xark_secp256k1::unpack`, `xark_secp256r1::unpack4` (the public 128-bit halves as 4 × 64-bit limbs: `divRem` hints, the limbs' range checks, one packing row per half) | with no input assumption, every limb is below `2⁶⁴` and each half is exactly its two limbs' value |
| `Xark.Templates.{Unpack8K1,Unpack8R1}.soundness` | `unpack8` of both curves (the same as 8 × 32-bit limbs, three chained splits per half) | every limb below `2³²`, each half exactly its four limbs' value |
| `Xark.Templates.{MuxpK1,MuxpR1,Mux}.soundness`, `MuxModel.select_bit` | `muxp` of both secp curves (16 limbs) and `xark_ed25519::mux` (24 limbs): one row `s·(aⱼ − bⱼ) = wⱼ` per limb, output `bⱼ + wⱼ`; `select8` is a tree of these calls | with no input assumption the outputs are `bⱼ + s·(aⱼ − bⱼ)`, so `a` at `s = 1` and `b` at `s = 0` |

### A whole circuit as its calls

`cargo xtask lean-export --example <example>` writes `Formal/Circuits/<Example>.lean` and
`Formal/Circuits/<Example>/Part<k>.lean` ([`Formal/Circuit.lean`](Formal/Circuit.lean); the
parts keep each file's elaboration small): the example's rows as segments in row
order, each a run of glue rows outside every `#[gadget]` call, a `Call` of a proven
template (the combinations its plugs carry over the circuit's variables, and the first
variable it allocated), or a `folded` call the frontend shortened at constant plugs
(its rows as emitted, which no template proof covers yet). `Circuit.rows` spells the
segments out, and `CircuitHash.lean` (the `lean` CI job) fails unless each segment's rows
hash to the hash the exporter took of the compiler's rows for it, in order, so `Sat circuit
σ` is about the production circuit; `--check` re-exports each committed circuit, and `lean.yml` runs the mutation test
`the_hash_check_refuses_a_mutated_circuit` (a bumped coefficient is refused, naming its
segment). `sat_call` hands every call's
template its satisfying assignment, so each template's `soundness` applies to its call
inside the circuit. secp256k1_ecdsa: 619 template calls of 12 templates, 4 folded
`mul_cert_k1` calls (`phi_x`'s multiplication by the constant `β`), 745 glue rows (the
`xor` and `d·(2y − 2p)` products of the digit selectors). Not yet proven: that each
call's plugs meet its `Assumptions` (the allowlist's prose), and the top-level statement.


### Adding a proven gadget

1. Put `#[gadget]` on the function. Its parameters and result must implement
   `xark::Input`. `cargo xtask digests --check` must still pass unchanged.
2. Add its harness `formal/templates/<function>/`: copy `add32`'s two files and
   call the gadget exactly once on `Private` inputs.
3. Run `cargo xtask lean-export <function>` and commit `Formal/Templates/<Function>.lean`.
   The export refuses a call that reads a variable none of its inputs carries (a
   product or bit decomposition reused from outside the call), a row rewritten
   after the call returned, and the big-integer hints (`MulModDivMod`,
   `ModInverse`, `Sub2`), which have no Lean meaning yet: add them to `Hint` and
   `Hint.run` first.
4. Write `Formal/<Function>.lean` with an `Assumptions` that lists every input
   assumption (each one enforced in-circuit by the gadget or its callers) and a
   `Spec` that pins the outputs to unique, canonical values. Reuse a zkGolf spec
   where one exists: Clean and its mathlib are this package's dependencies, so a
   zkGolf `Challenge/Specs/*.lean` file compiles here unchanged. Prove
   `soundness : Assumptions (t.ins σ) → t.Sat σ → Spec (t.ins σ) (t.outs σ)`.
   Soundness is the claim; completeness (the honest witness satisfies the rows) is
   left to the release tests, which exercise the honest path.
   [`Formal/Add32.lean`](Formal/Add32.lean) shows the pattern: `decide +kernel`
   proves the exported rows and hints equal a parametric model, then the proof is
   about the model.
5. Import it from `Formal.lean` and add a `#print axioms` line per theorem to
   `lean.yml`. No `sorry`, no new axioms.
6. Run `cargo xtask lean-export --coverage` (below) and make every production
   call of the gadget covered, or allowlist each other call site with a reason.

When the gadget changes, `--check` fails; re-export it, and the proof's
`decide +kernel` step fails until the model and proof match the new rows.

### Coverage: every production call emits the proven rows

A template is the call on fresh inputs. Inside a larger circuit the frontend can
emit other rows for the same call: a constant input folds, a decomposition memo
hit reuses bits from outside the call, a caller's `require_eq` merges into one of
its rows, a witness branch guards it. `cargo xtask lean-export --coverage` (the
`templates` job in `lean.yml`) checks what ships:

* It builds every example with the gadget markers and fails unless that build's
  flat-rows digest is the example's line in `tests/stable-digests.txt`, so the calls
  it records are the production circuit's. Not the keyed digest: the markers keep a
  gadget's body out of line, which can regroup the rows into template bodies (it
  does for `ed25519`) and so change the keyed rows the minimizer makes from the same
  flat rows; those follow from the flat rows by the minimizer, whose runs
  `cargo xtask minimize-check` certifies.
* For each gadget with a harness (whose template must still be the committed
  `Formal/Templates/*.lean`), it classifies every call, one line per gadget,
  example, call site and classification, with a count. A call site is the calling
  function, its file and `#k`, the k-th source position of that gadget's calls in
  that function (so an edit elsewhere in the file renames nothing; the allowlist and
  the circuit exports use this name); the report adds its `file:line:col`:
  * **covered**: its template, renamed as the export renames it, hashes to the
    proven one.
  * **covered with constant plugs**: it is the proven template with some input
    plugs replaced by the constants the call passes (every linear combination
    reduced mod `r`), the others plain distinct variables. `Template.soundness_inst`
    ([`Formal/Template.lean`](Formal/Template.lean), on top of `Rewrites.lean`'s
    `eval_subst`) carries the proof over to the substituted rows whenever the
    substituted inputs meet `Assumptions`; for add32, `Add32.soundness_consts` and
    `assumptions_consts`. The
    constants' `Assumptions` are per-vector theorems in the generated
    `Formal/Templates/Consts/<Gadget>.lean` (`cargo xtask lean-export --coverage
    --update` writes it; `--coverage` fails when it is missing, stale or not
    imported from `Formal.lean`, and `lake build` fails when a constant doesn't
    meet them). 
  * **covered with folded constants**: after substituting the constant plugs, it
    replays the frontend's folds on the proven template, in hint order: a hint whose
    value is now a constant or affine in the call's wires (`hint_bit` of a constant,
    XOR/OR/product with a constant operand) is dropped and its witness replaced by
    that value everywhere, and each row this leaves holding at every assignment
    (closed and true mod `r`, or an identity) is dropped; a closed row that is false
    fails the check. Witnesses nothing reads or writes any more are dropped, the
    rest renumbered in order, and the result must equal the call. One fold is
    `Template.foldAt`; `soundness_foldAt` and `sat_foldAt_of_sat` carry the proof
    over, and the constants' `Assumptions` are the same per-vector obligations as
    above (for a gadget with none, the `soundness_free` obligation). This covers
    `add32`'s all-constant calls (no rows left) and `xor` with a constant operand.
  * **covered: reuses a covered decomposition**: a `to_bits` that emits nothing
    because the frontend's memo (keyed by input and width) returned earlier bits;
    the tool checks its outputs are exactly those of a covered `to_bits` call on the
    same input linear combination at the same width. (A wider decomposition's low
    bits would not prove the narrower range, so only equal widths count.)
  * **covered: bits of producer bits**: a `to_bits` that emits nothing because its
    input is `Σ 2ⁱ·bᵢ` of proven bits (below); the tool checks that sum and that
    each `bᵢ` is a proven bit (`ToBits.spec_of_bits`).
  * **covered with LC plugs (assumptions discharged by producers[ and booleanity
    rows])**: LC plugs to a gadget whose `Assumptions` are that its inputs are bits
    (`xor`, `or`, `add32`, `xor3`, `maj3`, `chi`, `ch`), where each such input is a proven
    bit: a 0/1 constant, an output of a covered `to_bits`, `to_bits_canonical` or
    `reduce` call, or of a covered `xor`, `or`, `add32`, `xor3`, `maj3`, `chi` or `ch`
    call whose own inputs are proven bits (`*.outs_isBit`, `ToBits.spec_isBit`,
    `ToBitsCanonical.spec_isBit`, `Reduce.spec_isBit`), one minus a proven bit, or a
    wire a row of the circuit pins: `x · x = x`, `x · (x − 1) = 0`, or `a · b = v`
    with `a` and `b` proven bits (`LowerOutput::gadget_rows`; rows are never dropped
    after recording, so each is in the circuit).
  * **covered with LC plugs (no assumptions)**: the proven template with plugs
    replaced by any linear combinations (a sum of earlier wires, a repeated
    variable), for a gadget whose `soundness` assumes nothing of its inputs.
  * **covered: inside a covered / an allowlisted `G` call**: a call nested in a
    call of proven gadget `G` (the recorder's gadget stack) whose class is covered,
    or LC plugs with an allowlist entry: its rows are part of that call's, which
    `G`'s proof is about (`Template.soundness_inst` carries it over at LC plugs on
    inputs meeting `G`'s `Assumptions`, whose enforcers the entry names). The same
    call outside such a parent is classified on its own.
  * **LC plugs: the caller must enforce Assumptions**: the same substitution for a
    gadget whose proof has input assumptions. This is merge-gate item 6: it fails
    unless an allowlist entry names the caller rows that enforce them.
  * **refused**: the recorder can't attribute its rows exactly to the call; the
    reason says why (a value read from outside its inputs, a merged row, a witness
    branch, …).
  * **different rows**: none of the above.
* Any class but the covered ones fails the check unless
  [`coverage-allowlist.txt`](coverage-allowlist.txt) lists it with a reason
  (a refused or LC-plugs entry also pins its call count: a refused call's rows are
  unknown, and an LC-plugs entry's reason names the producers of the calls it lists,
  while its site is often a one-line wrapper that a new caller goes through). Over the
  examples, an entry that matches no call fails too. A later ticket proves the
  variant (a second template, or a lemma that reduces it to the proven one) and
  deletes the entry, or the reason says why the rows are sound without one.

* It counts, per example, the keyed rows (the globally minimized form) whose flat row
  lies inside a call of a covered class (one nested in an allowlisted LC-plug call
  included; that call's own rows are not), out of all keyed rows (each keyed row is one
  flat row with eliminated variables substituted; `expand_function_blob_reduced_origins`
  and the minimizer's trace name it), and prints `row coverage: <example>: k of n`.
  Rows outside every covered call are glue or user code, or calls the allowlist
  accepts.

Covered means the call emits the proven rows. Plain variable plugs still need the
proof's `Assumptions` (for `add32`, input words of bits): each assumption's
enforcer is the gadget's own rows or named caller rows, reviewed with the proof.

Every bit decomposition the frontend makes outside a `#[gadget]` call (an input's
range check, a native bitwise op's bits, `Field::to_bits`) is recorded as an
`xark::lang::to_bits` call, so each is checked against the `to_bits` template at its
width. The obligations file of a template is generated next to it, importing the
proof file that imports the template (`Formal.BoolOps` for `xor` and `or`).

`--circuit <dir>` checks other circuit crates instead (their digest is compared
with the same crate built without markers).

A constant XOR/OR operand folds to a linear form with no row: `Xor.fold_lhs`/`fold_rhs`
and `Or.fold_lhs`/`fold_rhs` prove that form is exactly what the template with the
constant substituted allows, and `const_hint_sound` covers a `hint_bit` of a constant.

## Building

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager); the pinned toolchain (Lean 4.33.1) is in [`lean-toolchain`](lean-toolchain).
mathlib and [Clean](https://github.com/Verified-zkEVM/clean) are pinned to commits in
`lakefile.toml` (the zkGolf specs' setup: Clean `93c9d1e`, built against mathlib
`0df444a`), the rest in `lake-manifest.json`.

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
for `gadgets/xark-sha256/src/lib.rs`. Full bit-equivalence of SHA-256
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
composed with `Formal.BitwuzlaCompose.sha256_closed_chain` — the latter
is a pure-Lean structural proof through `sha256_round_bit_equivalence`
(the file name is historical; no external SMT solver is involved).

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
* External audit, fuzzing-extension, and Kani work on the on-chain
  verifier — engineering, not FV.
