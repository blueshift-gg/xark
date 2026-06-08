/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

-- The `style.header` linter hard-codes mathlib's Apache license string; this is
-- an MIT project, so disable that house-style check (it is not a correctness lint).
set_option linter.style.header false

/-!
# xark elliptic-curve addition soundness — Layer B, mechanised in Lean 4 / mathlib

`crates/acir-r1cs/src/gadgets/curve.rs` adds points on the embedded short
Weierstrass curve `y² = x³ + a·x + b` (Grumpkin, the BN254 embedded curve).
The generic (distinct-`x`) case supplies a slope witness `λ` constrained by

    (x2 − x1)·λ = y2 − y1,

and the standard output formulas

    x3 = λ² − x1 − x2,    y3 = λ·(x1 − x3) − y1.

We prove the soundness facts that matter for the generic add and the
doubling case, over any field (so they apply to Grumpkin's base field `Fq`):

* `ec_add_generic_slope_unique` — when `x1 ≠ x2` the slope constraint pins `λ`
  uniquely, hence `x3, y3` are determined: **no under-constraint slack**.
* `ec_add_generic_on_curve` — the **addition law closes**: the output point
  `(x3, y3)` lies back on the curve. This is the algebraic heart of EC
  correctness; the gadget computes a real curve point, not an off-curve forgery.
* `ec_double_slope_unique` — same uniqueness property for the doubling slope
  `λ·(2·y1) = 3·x1²`: provided `2·y1 ≠ 0` the gadget's slope witness is pinned.
* `ec_double_on_curve` — addition-law closure for the doubling case: when the
  prover supplies `P1 = P2` on Grumpkin and a slope satisfying the doubling
  constraint, `(x3, y3) = (λ² − 2x1, λ(x1 − x3) − y1)` is again on Grumpkin.
* `ec_inverse_recognized` — when `x1 = x2` and `y1 + y2 = 0` the input pair is
  exactly the inverse case `P2 = −P1`; this documents the selector branch
  that routes such inputs to the point at infinity.

We also mechanise the **selector-routing layer** that picks between the four
branches (lhs-at-infinity, rhs-at-infinity, inverse, generic/doubling):

* `IsSelectorWitness` — predicate capturing the in-circuit constraints on the
  selector booleans `same_x, same_y, is_double, is_inverse` together with the
  hinted-inverse witnesses `inv_dx, inv_dy` for the `same_x`/`same_y` indicator
  pairs.
* `selector_unique` — given the same inputs `(x1, y1, x2, y2, lhs_inf, rhs_inf)`,
  any two selector witnesses agree: there is **no prover freedom** at the
  routing layer. This is the under-constraint slack theorem for selectors.
* `selectors_double_case` / `selectors_inverse_case` — the selector–input
  algebraic correspondence: at coinciding finite inputs `is_double = 1`, and
  at `(x1, y1), (x1, −y1)` with `y1 ≠ 0` we get `is_inverse = 1`.
* `output_mux_lhs_inf`, `output_mux_rhs_inf`, `output_mux_inverse`,
  `output_mux_generic` — for the output-mux relations the gadget emits
  (`x3 = take_p2·x2 + take_p1·x1 + take_generic·xg`, etc.), one theorem per
  routing branch verifying that the mux outputs the intended value.

Finally, the layer-B story is closed by tying these per-piece theorems into
the end-to-end soundness story for the `ec_add_in_circuit` gadget:

* `gated_on_curve_sound` / `gated_on_curve_trivial` /
  `enforce_on_curve_grumpkin_sound` — the gated curve-membership constraint
  `(1 − is_infinity) · (y² − x³ + 17) = 0` forces curve membership exactly
  when `is_infinity = 0` and is vacuous otherwise. This is the algebraic
  content of `enforce_on_curve_grumpkin` in `curve.rs` and is what discharges
  the "inputs are on the curve" hypothesis used by every preceding theorem.
* `IsValidECAddWitness` — packaged predicate bundling: both inputs are
  on Grumpkin (or at infinity), all booleans are boolean, the selector
  layer constraints (an `IsSelectorWitness` instance), the two gated slope
  constraints from `curve.rs` (generic and doubling branches), and the
  output-mux equations (an `IsOutputMux` instance).
* `EcAddSemantics` — Lean-side specification of what the gadget *ought*
  to compute. Stated as a relation `EcAddSemantics in1 in2 out` between
  input/output triples `(x, y, is_inf)`, using the gadget's `(0, 0, 1)`
  encoding for the point at infinity. Phrased as a relation (rather than a
  function) so we never need `DecidableEq F` to dispatch the cases.
* `ec_add_in_circuit_generic_sound` — end-to-end composition wrapper for
  the generic (distinct-`x`) branch: any prover witness satisfying
  `IsValidECAddWitness` with `is_inf1 = is_inf2 = is_inverse = 0` and
  `x1 ≠ x2` produces `(x3, y3, 0)` matching the standard
  `(λ² − x1 − x2, λ·(x1 − x3) − y1, 0)` formulas, with `(x3, y3)` again on
  Grumpkin. This is the simplest non-trivial composition and demonstrates
  the pattern.
* `ec_add_in_circuit_sound` — the full 4-way wrapper: under
  `IsValidECAddWitness`, the output triple stands in the `EcAddSemantics`
  relation to the inputs, by case-split on `is_inf1, is_inf2, is_inverse`.

Scope: the scalar-multiplication ladder in `ecdsa.rs` built on top of point
addition is not covered here — see the Layer-B section of
`docs/FORMAL_VERIFICATION_PLAN.md`.
-/

namespace Xark

/-- **Generic-case slope determinism.** With distinct `x`-coordinates the slope
constraint `λ·(x2 − x1) = y2 − y1` has a unique solution `λ`, so the gadget's
slope witness — and therefore the output coordinates — carry no prover freedom. -/
theorem ec_add_generic_slope_unique {F : Type*} [Field F]
    (x1 y1 x2 y2 lam lam' : F) (hx : x1 ≠ x2)
    (h : lam * (x2 - x1) = y2 - y1) (h' : lam' * (x2 - x1) = y2 - y1) :
    lam = lam' := by
  have hd : x2 - x1 ≠ 0 := sub_ne_zero.mpr fun e => hx e.symm
  apply mul_right_cancel₀ hd
  rw [h, h']

/-- **Generic-case addition law closure.** If `(x1, y1)` and `(x2, y2)` are on
the curve `y² = x³ + a·x + b`, `x1 ≠ x2`, and `λ` is the slope
`λ·(x2 − x1) = y2 − y1`, then the output `(x3, y3)` produced by the gadget's
formulas is on the curve as well. -/
theorem ec_add_generic_on_curve {F : Type*} [Field F]
    (a b x1 y1 x2 y2 lam : F) (hx : x1 ≠ x2)
    (hE1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (hE2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b)
    (hS : lam * (x2 - x1) = y2 - y1) :
    (lam * (x1 - (lam ^ 2 - x1 - x2)) - y1) ^ 2
      = (lam ^ 2 - x1 - x2) ^ 3 + a * (lam ^ 2 - x1 - x2) + b := by
  have hd : x2 - x1 ≠ 0 := sub_ne_zero.mpr fun e => hx e.symm
  -- Multiply the two curve equations through the slope relation; the result,
  -- after cancelling the common `(x2 − x1)` factor, is the key slope identity.
  have key : (lam * (x2 - x1)) * (lam * (x2 - x1) + 2 * y1)
           = (x2 - x1) * (x1 ^ 2 + x1 * x2 + x2 ^ 2 + a) := by
    linear_combination hE2 - hE1 + (2 * y2 + lam * (x2 - x1) - (y2 - y1)) * hS
  have hR : lam ^ 2 * (x2 - x1) + 2 * lam * y1 = x1 ^ 2 + x1 * x2 + x2 ^ 2 + a := by
    apply mul_left_cancel₀ hd
    linear_combination key
  -- Substitute `b` (via the curve eq at P1) and the slope identity `hR`.
  linear_combination hE1 + ((lam ^ 2 - x1 - x2) - x1) * hR

/-- **Doubling-case slope determinism.** With `2·y1 ≠ 0` the doubling-slope
constraint `λ·(2·y1) = 3·x1²` has a unique solution `λ`, so the gadget's
doubling-branch slope witness — and therefore the output coordinates — carry
no prover freedom. The hypothesis `2·y1 ≠ 0` covers exactly the two cases the
gadget excludes: the curve point is not `y1 = 0` (a 2-torsion point) and the
field characteristic is not 2 (Grumpkin's base field has odd characteristic). -/
theorem ec_double_slope_unique {F : Type*} [Field F]
    (x1 y1 lam lam' : F) (h2y : (2 : F) * y1 ≠ 0)
    (h : lam * (2 * y1) = 3 * x1 ^ 2) (h' : lam' * (2 * y1) = 3 * x1 ^ 2) :
    lam = lam' := by
  apply mul_right_cancel₀ h2y
  rw [h, h']

/-- **Doubling-case addition law closure.** If `(x1, y1)` is on Grumpkin
(`y1² = x1³ + b`) and `λ` is the doubling slope `λ·(2·y1) = 3·x1²`, then the
output `(x3, y3) = (λ² − 2·x1, λ·(x1 − x3) − y1)` produced by the gadget's
formulas lies back on the curve. Concretely: the doubling branch of
`ec_add_in_circuit` cannot forge an off-curve point. The statement is for the
`a = 0` form of short Weierstrass (Grumpkin); the gadget's doubling constraint
`2·y1·λ = 3·x1²` matches this slope exactly. -/
theorem ec_double_on_curve {F : Type*} [Field F]
    (b x1 y1 lam : F)
    (hE1 : y1 ^ 2 = x1 ^ 3 + b)
    (hS : lam * (2 * y1) = 3 * x1 ^ 2) :
    (lam * (x1 - (lam ^ 2 - 2 * x1)) - y1) ^ 2
      = (lam ^ 2 - 2 * x1) ^ 3 + b := by
  -- Direct closure: the doubling output's curve equation factors as `hE1`
  -- plus a `(lam² − 3·x1)`-multiple of the slope identity. No intermediate
  -- cancellation is needed because the slope already pins `2·λ·y1`.
  linear_combination hE1 + (lam ^ 2 - 3 * x1) * hS

/-- **Inverse-case recognition.** If `x1 = x2`, `y1 + y2 = 0`, and `y1 ≠ 0`
(so we are *not* in the doubling sub-case `y1 = 0` that maps to itself), then
the second input is exactly the negation of the first: `(x2, y2) = (x1, −y1)`.
This documents the algebraic content of the gadget's `is_inverse` selector
branch, which routes such pairs to the point at infinity. -/
theorem ec_inverse_recognized {F : Type*} [Field F]
    (x1 y1 x2 y2 : F) (_hy : y1 ≠ 0)
    (hx : x1 = x2) (hy_sum : y1 + y2 = 0) :
    x2 = x1 ∧ y2 = -y1 := by
  refine ⟨hx.symm, ?_⟩
  linear_combination hy_sum

/-! ### Selector layer

The gadget allocates booleans `same_x, same_y, is_double, is_inverse`
plus hinted-inverse witnesses `inv_dx, inv_dy`, and gates the routing
between the four addition branches with their products. The constraints
the prover must satisfy are encoded by `IsSelectorWitness` below; we
then prove (a) that this predicate determines the selector booleans
uniquely from the inputs, and (b) the algebraic relationship between
selectors and the doubling / inverse / generic cases.
-/

/-- **Selector witness predicate.** Captures exactly the in-circuit
constraints `curve.rs` emits on the routing selectors:

* `same_x, same_y, is_double, is_inverse, lhs_inf, rhs_inf` are booleans;
* `same_x · (x2 − x1) = 0` and `(x2 − x1) · inv_dx = 1 − same_x` form
  the indicator-pair that pins `same_x ↔ (x1 = x2)`;
* analogous indicator pair for `same_y ↔ (y1 = y2)`;
* `is_double = same_x · same_y · (1 − lhs_inf) · (1 − rhs_inf)`;
* `is_inverse = same_x · (1 − same_y) · (1 − lhs_inf) · (1 − rhs_inf)`.

The hinted inverses `inv_dx, inv_dy` are *witness-only* (the prover
chooses them); they are existentially captured here as fields of the
predicate. -/
structure IsSelectorWitness {F : Type*} [Field F]
    (x1 y1 x2 y2 lhs_inf rhs_inf
     same_x same_y is_double is_inverse inv_dx inv_dy : F) : Prop where
  same_x_bool   : same_x * (same_x - 1) = 0
  same_y_bool   : same_y * (same_y - 1) = 0
  lhs_inf_bool  : lhs_inf * (lhs_inf - 1) = 0
  rhs_inf_bool  : rhs_inf * (rhs_inf - 1) = 0
  same_x_zero   : same_x * (x2 - x1) = 0
  same_x_inv    : (x2 - x1) * inv_dx = 1 - same_x
  same_y_zero   : same_y * (y2 - y1) = 0
  same_y_inv    : (y2 - y1) * inv_dy = 1 - same_y
  is_double_def : is_double = same_x * same_y * (1 - lhs_inf) * (1 - rhs_inf)
  is_inverse_def : is_inverse = same_x * (1 - same_y) * (1 - lhs_inf) * (1 - rhs_inf)

/-- The `same_x` indicator pair pins `same_x = 1` exactly when `x1 = x2`. -/
lemma same_x_eq_one_of_x_eq {F : Type*} [Field F]
    {x1 x2 same_x inv_dx : F}
    (h : (x2 - x1) * inv_dx = 1 - same_x) (hxeq : x1 = x2) :
    same_x = 1 := by
  have h0 : x2 - x1 = 0 := by rw [hxeq]; ring
  have hz : (1 : F) - same_x = 0 := by
    rw [← h, h0]; ring
  linear_combination -hz

/-- The `same_x` indicator pair pins `same_x = 0` when `x1 ≠ x2`. -/
lemma same_x_eq_zero_of_x_ne {F : Type*} [Field F]
    {x1 x2 same_x : F}
    (h : same_x * (x2 - x1) = 0) (hxne : x1 ≠ x2) :
    same_x = 0 := by
  have hd : x2 - x1 ≠ 0 := sub_ne_zero.mpr fun e => hxne e.symm
  exact (mul_eq_zero.mp h).resolve_right hd

/-- **Selector witness uniqueness.** Given the same inputs
`(x1, y1, x2, y2, lhs_inf, rhs_inf)`, any two selector witnesses agree
on every selector boolean (`same_x, same_y, is_double, is_inverse`).
This is the under-constraint slack theorem for the routing layer: the
prover has no freedom in choosing selectors. The hinted inverses
`inv_dx, inv_dy` are *not* forced to be equal — they can differ when
`x1 = x2` (resp. `y1 = y2`) because the constraint `0 · inv = 0` is
trivial — but they do not affect any other circuit output.

Proof sketch: split on `x1 = x2` vs `x1 ≠ x2` (and likewise for `y`).
When equal, the inverse-witness equation forces `same = 1`; when
unequal, the product equation forces `same = 0`. With `same_x, same_y`
determined, `is_double` and `is_inverse` are forced by their product
defining equations. -/
theorem selector_unique {F : Type*} [Field F]
    {x1 y1 x2 y2 lhs_inf rhs_inf
     same_x same_y is_double is_inverse inv_dx inv_dy
     same_x' same_y' is_double' is_inverse' inv_dx' inv_dy' : F}
    (h : IsSelectorWitness x1 y1 x2 y2 lhs_inf rhs_inf
            same_x same_y is_double is_inverse inv_dx inv_dy)
    (h' : IsSelectorWitness x1 y1 x2 y2 lhs_inf rhs_inf
            same_x' same_y' is_double' is_inverse' inv_dx' inv_dy') :
    same_x = same_x' ∧ same_y = same_y' ∧
    is_double = is_double' ∧ is_inverse = is_inverse' := by
  classical
  -- Pin `same_x = same_x'`.
  have hsx : same_x = same_x' := by
    by_cases hxeq : x1 = x2
    · have h1 : same_x  = 1 := same_x_eq_one_of_x_eq h.same_x_inv  hxeq
      have h2 : same_x' = 1 := same_x_eq_one_of_x_eq h'.same_x_inv hxeq
      rw [h1, h2]
    · have h1 : same_x  = 0 := same_x_eq_zero_of_x_ne h.same_x_zero  hxeq
      have h2 : same_x' = 0 := same_x_eq_zero_of_x_ne h'.same_x_zero hxeq
      rw [h1, h2]
  -- Pin `same_y = same_y'` by the same argument.
  have hsy : same_y = same_y' := by
    by_cases hyeq : y1 = y2
    · have h1 : same_y  = 1 := same_x_eq_one_of_x_eq h.same_y_inv  hyeq
      have h2 : same_y' = 1 := same_x_eq_one_of_x_eq h'.same_y_inv hyeq
      rw [h1, h2]
    · have h1 : same_y  = 0 := same_x_eq_zero_of_x_ne h.same_y_zero  hyeq
      have h2 : same_y' = 0 := same_x_eq_zero_of_x_ne h'.same_y_zero hyeq
      rw [h1, h2]
  -- `is_double` and `is_inverse` are pinned by their product defs.
  refine ⟨hsx, hsy, ?_, ?_⟩
  · rw [h.is_double_def, h'.is_double_def, hsx, hsy]
  · rw [h.is_inverse_def, h'.is_inverse_def, hsx, hsy]

/-- **Doubling-case selector values.** When both inputs are finite
(`lhs_inf = rhs_inf = 0`) and the points coincide (`x1 = x2 ∧ y1 = y2`),
a selector witness has `same_x = same_y = 1` and so `is_double = 1`,
`is_inverse = 0`. -/
theorem selectors_double_case {F : Type*} [Field F]
    {x1 y1 x2 y2 same_x same_y is_double is_inverse inv_dx inv_dy : F}
    (h : IsSelectorWitness x1 y1 x2 y2 0 0
            same_x same_y is_double is_inverse inv_dx inv_dy)
    (hx : x1 = x2) (hy : y1 = y2) :
    same_x = 1 ∧ same_y = 1 ∧ is_double = 1 ∧ is_inverse = 0 := by
  have hsx : same_x = 1 := same_x_eq_one_of_x_eq h.same_x_inv hx
  have hsy : same_y = 1 := same_x_eq_one_of_x_eq h.same_y_inv hy
  refine ⟨hsx, hsy, ?_, ?_⟩
  · rw [h.is_double_def, hsx, hsy]; ring
  · rw [h.is_inverse_def, hsy]; ring

/-- **Inverse-case selector values.** When both inputs are finite,
`x1 = x2`, and `y1 ≠ y2` (so the points are *not* equal — in the
inverse case `y2 = −y1`, so `y1 ≠ y2` follows whenever `2 · y1 ≠ 0`,
which is the same regularity hypothesis the doubling slope lemma
needs), a selector witness has `same_x = 1`, `same_y = 0`, and
therefore `is_double = 0`, `is_inverse = 1`.

Compose with `ec_inverse_recognized` to dispatch the `y2 = −y1`
algebraic side of the inverse case. -/
theorem selectors_inverse_case {F : Type*} [Field F]
    {x1 y1 x2 y2 same_x same_y is_double is_inverse inv_dx inv_dy : F}
    (h : IsSelectorWitness x1 y1 x2 y2 0 0
            same_x same_y is_double is_inverse inv_dx inv_dy)
    (hx : x1 = x2) (hy_ne : y1 ≠ y2) :
    same_x = 1 ∧ same_y = 0 ∧ is_double = 0 ∧ is_inverse = 1 := by
  have hsx : same_x = 1 := same_x_eq_one_of_x_eq h.same_x_inv hx
  have hsy : same_y = 0 := same_x_eq_zero_of_x_ne h.same_y_zero hy_ne
  refine ⟨hsx, hsy, ?_, ?_⟩
  · rw [h.is_double_def, hsy]; ring
  · rw [h.is_inverse_def, hsx, hsy]; ring

/-! ### Output mux

The gadget computes the final output `(x3, y3, is_inf3)` from the four
branch values using selector products:

```text
take_p2      = lhs_inf
take_p1      = (1 − lhs_inf) · rhs_inf
take_generic = (1 − lhs_inf) · (1 − rhs_inf) · (1 − is_inverse)
take_inverse = (1 − lhs_inf) · (1 − rhs_inf) · is_inverse

x3      = take_p2 · x2 + take_p1 · x1 + take_generic · xg
y3      = take_p2 · y2 + take_p1 · y1 + take_generic · yg
is_inf3 = take_p2 · rhs_inf + take_inverse
```

We package these into a single predicate `IsOutputMux` and prove
one theorem per branch: under the boolean-selector assignment of that
branch, the mux outputs the intended value. -/

/-- **Output-mux predicate.** Captures the relations the in-circuit
output coordinates satisfy:

```text
x3      = lhs_inf · x2 + (1 − lhs_inf) · rhs_inf · x1
        + (1 − lhs_inf) · (1 − rhs_inf) · (1 − is_inverse) · xg
y3      = lhs_inf · y2 + (1 − lhs_inf) · rhs_inf · y1
        + (1 − lhs_inf) · (1 − rhs_inf) · (1 − is_inverse) · yg
is_inf3 = lhs_inf · rhs_inf
        + (1 − lhs_inf) · (1 − rhs_inf) · is_inverse
```

(The `take_p1 · lhs_inf` term is omitted from `is_inf3` because
`take_p1` already carries the `(1 − lhs_inf)` factor, making the
product identically zero — matching `curve.rs` exactly.) -/
structure IsOutputMux {F : Type*} [Field F]
    (x1 y1 x2 y2 xg yg lhs_inf rhs_inf is_inverse
     x3 y3 is_inf3 : F) : Prop where
  x3_def : x3 = lhs_inf * x2 + (1 - lhs_inf) * rhs_inf * x1
              + (1 - lhs_inf) * (1 - rhs_inf) * (1 - is_inverse) * xg
  y3_def : y3 = lhs_inf * y2 + (1 - lhs_inf) * rhs_inf * y1
              + (1 - lhs_inf) * (1 - rhs_inf) * (1 - is_inverse) * yg
  is_inf3_def : is_inf3 = lhs_inf * rhs_inf
                       + (1 - lhs_inf) * (1 - rhs_inf) * is_inverse

/-- **lhs-at-infinity branch.** When `lhs_inf = 1` the mux outputs
`(x2, y2, rhs_inf)`: the result is `P2` (with its infinity flag
preserved). -/
theorem output_mux_lhs_inf {F : Type*} [Field F]
    {x1 y1 x2 y2 xg yg rhs_inf is_inverse x3 y3 is_inf3 : F}
    (h : IsOutputMux x1 y1 x2 y2 xg yg 1 rhs_inf is_inverse x3 y3 is_inf3) :
    x3 = x2 ∧ y3 = y2 ∧ is_inf3 = rhs_inf := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.x3_def]; ring
  · rw [h.y3_def]; ring
  · rw [h.is_inf3_def]; ring

/-- **rhs-at-infinity branch.** When `lhs_inf = 0` and `rhs_inf = 1`
the mux outputs `(x1, y1, 0)`: the result is `P1` and the output is
finite. -/
theorem output_mux_rhs_inf {F : Type*} [Field F]
    {x1 y1 x2 y2 xg yg is_inverse x3 y3 is_inf3 : F}
    (h : IsOutputMux x1 y1 x2 y2 xg yg 0 1 is_inverse x3 y3 is_inf3) :
    x3 = x1 ∧ y3 = y1 ∧ is_inf3 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.x3_def]; ring
  · rw [h.y3_def]; ring
  · rw [h.is_inf3_def]; ring

/-- **Inverse branch.** When both inputs are finite (`lhs_inf = 0`,
`rhs_inf = 0`) and `is_inverse = 1`, the mux outputs `(0, 0, 1)`: the
point at infinity in the Noir / `curve.rs` encoding. -/
theorem output_mux_inverse {F : Type*} [Field F]
    {x1 y1 x2 y2 xg yg x3 y3 is_inf3 : F}
    (h : IsOutputMux x1 y1 x2 y2 xg yg 0 0 1 x3 y3 is_inf3) :
    x3 = 0 ∧ y3 = 0 ∧ is_inf3 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.x3_def]; ring
  · rw [h.y3_def]; ring
  · rw [h.is_inf3_def]; ring

/-- **Generic / doubling branch.** When both inputs are finite and
`is_inverse = 0`, the mux outputs `(xg, yg, 0)`: the generic-add /
doubling slope formulas are routed through. This is the branch that
composes with `ec_add_generic_slope_unique` / `ec_add_generic_on_curve`
and the analogous doubling lemmas to give end-to-end soundness. -/
theorem output_mux_generic {F : Type*} [Field F]
    {x1 y1 x2 y2 xg yg x3 y3 is_inf3 : F}
    (h : IsOutputMux x1 y1 x2 y2 xg yg 0 0 0 x3 y3 is_inf3) :
    x3 = xg ∧ y3 = yg ∧ is_inf3 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.x3_def]; ring
  · rw [h.y3_def]; ring
  · rw [h.is_inf3_def]; ring

/-! ### Gated curve membership

The gadget enforces input curve membership via the gated constraint

    (1 − is_infinity) · (y² − x³ + 17) = 0

emitted by `enforce_on_curve_grumpkin` in `curve.rs`. Grumpkin is the
short-Weierstrass curve `y² = x³ − 17` (so `a = 0`, `b = −17`) over the
proving-system base field. The two lemmas below close the two cases:

* `is_infinity = 1`: the constraint is trivially `0 · _ = 0`.
* `is_infinity = 0`: the constraint reduces to `y² = x³ − 17`.

These are the algebraic content that discharges the "inputs on the curve"
hypothesis used everywhere above. -/

/-- **Gated curve check — non-infinity branch.** Given the boolean
witness for `is_infinity` and the gated curve constraint, when
`is_infinity = 0` we have `y² = x³ − 17`, i.e. `(x, y) ∈ Grumpkin`. -/
theorem gated_on_curve_sound {F : Type*} [Field F]
    (x y is_inf : F)
    (_hbool : is_inf * (is_inf - 1) = 0)
    (hgate : (1 - is_inf) * (y ^ 2 - x ^ 3 + 17) = 0)
    (hzero : is_inf = 0) :
    y ^ 2 = x ^ 3 - 17 := by
  -- Substitute `is_inf = 0` into the gated equation to get `y² − x³ + 17 = 0`.
  have h : y ^ 2 - x ^ 3 + 17 = 0 := by
    have := hgate
    rw [hzero] at this
    linear_combination this
  linear_combination h

/-- **Gated curve check — infinity branch (vacuity).** When
`is_infinity = 1` the gated constraint `(1 − is_infinity) · _ = 0` holds
trivially: no curve-membership condition is imposed on `(x, y)`. The
gadget thus correctly allows arbitrary witness coordinates at the point
at infinity (we use the `(0, 0, 1)` encoding in practice, but the
constraint does not force this). -/
theorem gated_on_curve_trivial {F : Type*} [Field F] (x y : F) :
    (1 - (1 : F)) * (y ^ 2 - x ^ 3 + 17) = 0 := by
  ring

/-- **Packaged gated-curve soundness.** Combines `gated_on_curve_sound`
and `gated_on_curve_trivial` into the disjunction the rest of the
soundness story actually consumes: a boolean `is_infinity` satisfying
the gated curve constraint is either the point at infinity
(`is_infinity = 1`) or a finite Grumpkin point (`y² = x³ − 17`). -/
theorem enforce_on_curve_grumpkin_sound {F : Type*} [Field F]
    (x y is_inf : F)
    (hbool : is_inf * (is_inf - 1) = 0)
    (hgate : (1 - is_inf) * (y ^ 2 - x ^ 3 + 17) = 0) :
    is_inf = 1 ∨ y ^ 2 = x ^ 3 - 17 := by
  -- `hbool` says `is_inf ∈ {0, 1}`.
  have hcases : is_inf = 0 ∨ is_inf = 1 := by
    rcases mul_eq_zero.mp hbool with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases hcases with h0 | h1
  · exact Or.inr (gated_on_curve_sound x y is_inf hbool hgate h0)
  · exact Or.inl h1

/-! ### End-to-end composition wrapper

We now bundle the per-piece theorems into the full soundness statement
for `ec_add_in_circuit`. The bundling has three parts:

1. `IsValidECAddWitness` — the predicate the prover must satisfy. It
   contains the gated curve checks for both inputs, the `IsSelectorWitness`
   instance for the routing layer, the two gated slope constraints
   (`generic_active · ((x2 − x1)·λ − (y2 − y1)) = 0` and
   `is_double · (2·y1·λ − 3·x1²) = 0`), and the `IsOutputMux` instance
   for the final coordinate selection.
2. `EcAddSemantics` — a *relation* on input/output triples saying "the
   output is the algebraically-correct group sum of the inputs". Stated
   as a relation rather than a function so we never need `DecidableEq F`
   to dispatch the four routing branches; the case-split is a `match`
   on `is_inf1`, `is_inf2`, `same_x`, and `same_y`.
3. `ec_add_in_circuit_generic_sound` (scope-down) /
   `ec_add_in_circuit_sound` (full) — the wrapper theorems.

We model the `(0, 0, 1)` infinity encoding directly in the constructors
of `EcAddSemantics` so the relation matches `curve.rs` exactly. -/

/-- **Packaged witness predicate** for the entire `ec_add_in_circuit`
gadget. A prover who satisfies all of the gadget's R1CS constraints
yields a Lean witness of this predicate (with the bookkeeping
auxiliaries `xg`, `yg`, plus the slope `lambda`).

Bundle:

* `on_curve1`, `on_curve2` — the gated curve-membership constraint from
  `enforce_on_curve_grumpkin`, one per input.
* `is_inf1_bool`, `is_inf2_bool` — boolean booleans for the infinity flags.
* `sel` — the routing selector witness (`IsSelectorWitness`).
* `slope_generic` — gated generic-slope constraint
  `(1 − lhs_inf)·(1 − rhs_inf)·(1 − is_double)·(1 − is_inverse)
   · ((x2 − x1)·λ − (y2 − y1)) = 0`.
* `slope_double` — gated doubling-slope constraint
  `is_double · (2·y1·λ − 3·x1²) = 0`.
* `xg_def`, `yg_def` — the generic output coordinates the gadget computes:
  `xg = λ² − x1 − x2`, `yg = λ·(x1 − xg) − y1`.
* `mux` — the output-mux relation (`IsOutputMux`).

We do NOT bundle the curve membership of the output `(x3, y3, is_inf3)`;
that is the *conclusion* of the soundness theorem. -/
structure IsValidECAddWitness {F : Type*} [Field F]
    (x1 y1 is_inf1 x2 y2 is_inf2 lambda
     same_x same_y is_double is_inverse inv_dx inv_dy
     xg yg x3 y3 is_inf3 : F) : Prop where
  on_curve1     : (1 - is_inf1) * (y1 ^ 2 - x1 ^ 3 + 17) = 0
  on_curve2     : (1 - is_inf2) * (y2 ^ 2 - x2 ^ 3 + 17) = 0
  is_inf1_bool  : is_inf1 * (is_inf1 - 1) = 0
  is_inf2_bool  : is_inf2 * (is_inf2 - 1) = 0
  sel           : IsSelectorWitness x1 y1 x2 y2 is_inf1 is_inf2
                      same_x same_y is_double is_inverse inv_dx inv_dy
  slope_generic : (1 - is_inf1) * (1 - is_inf2) * (1 - is_double) * (1 - is_inverse)
                    * ((x2 - x1) * lambda - (y2 - y1)) = 0
  slope_double  : is_double * (2 * y1 * lambda - 3 * x1 ^ 2) = 0
  xg_def        : xg = lambda ^ 2 - x1 - x2
  yg_def        : yg = lambda * (x1 - xg) - y1
  mux           : IsOutputMux x1 y1 x2 y2 xg yg is_inf1 is_inf2 is_inverse x3 y3 is_inf3

/-- **Algebraic group-operation specification.** Relation between two
input curve triples and an output triple — "the output is the group sum
of the inputs". Cases (matching the gadget exactly):

* `lhs_inf` (`P1 = ∞`): output = `P2` (with its infinity flag preserved).
* `rhs_inf` (`P2 = ∞`, `P1` finite): output = `P1`.
* Inverse (both finite, `x1 = x2`, `y1 + y2 = 0`): output is `∞`,
  encoded `(0, 0, 1)`.
* Generic (both finite, `x1 ≠ x2`): output = `(λ² − x1 − x2,
  λ·(x1 − xg) − y1, 0)` for the unique slope
  `λ = (y2 − y1) / (x2 − x1)`.
* Doubling (both finite, `x1 = x2`, `y1 = y2`, `2·y1 ≠ 0`): output =
  the doubling formulas with `λ = 3·x1² / (2·y1)`.

We give this as inductive constructors rather than a function so no
field-element equality test is required. -/
inductive EcAddSemantics {F : Type*} [Field F] :
    F × F × F → F × F × F → F × F × F → Prop where
  | lhs_inf {x1 y1 x2 y2 is_inf2 : F} :
      EcAddSemantics (x1, y1, 1) (x2, y2, is_inf2) (x2, y2, is_inf2)
  | rhs_inf {x1 y1 x2 y2 : F} :
      EcAddSemantics (x1, y1, 0) (x2, y2, 1) (x1, y1, 0)
  | inverse {x1 y1 x2 y2 : F} (_hx : x1 = x2) (_hy : y1 + y2 = 0) :
      EcAddSemantics (x1, y1, 0) (x2, y2, 0) (0, 0, 1)
  | generic {x1 y1 x2 y2 lambda : F} (_hx : x1 ≠ x2)
      (_hS : lambda * (x2 - x1) = y2 - y1) :
      EcAddSemantics (x1, y1, 0) (x2, y2, 0)
        (lambda ^ 2 - x1 - x2,
         lambda * (x1 - (lambda ^ 2 - x1 - x2)) - y1,
         0)
  | doubling {x1 y1 lambda : F} (_h2y : (2 : F) * y1 ≠ 0)
      (_hS : lambda * (2 * y1) = 3 * x1 ^ 2) :
      EcAddSemantics (x1, y1, 0) (x1, y1, 0)
        (lambda ^ 2 - 2 * x1,
         lambda * (x1 - (lambda ^ 2 - 2 * x1)) - y1,
         0)

/-- **End-to-end soundness — generic branch.** Under
`IsValidECAddWitness` with both inputs finite (`is_inf1 = is_inf2 = 0`),
the inverse selector off (`is_inverse = 0`), and distinct x-coordinates
(`x1 ≠ x2`), the gadget output `(x3, y3, is_inf3)` is the
algebraically-correct generic-add result:

* `is_inf3 = 0` (the sum of two finite distinct-x points is finite);
* `x3 = λ² − x1 − x2`, `y3 = λ·(x1 − x3) − y1` for the slope `λ` pinned
  by `λ·(x2 − x1) = y2 − y1` (with `λ` unique by
  `ec_add_generic_slope_unique`);
* `(x3, y3)` lies on Grumpkin (`y3² = x3³ − 17`) by
  `ec_add_generic_on_curve`.

This is the simplest non-trivial composition wrapper: it ties the
selector, slope, output-mux, and addition-law theorems into one
self-contained statement. The full 4-way wrapper is
`ec_add_in_circuit_sound`. -/
theorem ec_add_in_circuit_generic_sound {F : Type*} [Field F]
    {x1 y1 x2 y2 lambda same_x same_y is_double is_inverse
     inv_dx inv_dy xg yg x3 y3 is_inf3 : F}
    (h : IsValidECAddWitness x1 y1 0 x2 y2 0 lambda
            same_x same_y is_double is_inverse inv_dx inv_dy
            xg yg x3 y3 is_inf3)
    (hxne : x1 ≠ x2) :
    is_inf3 = 0 ∧
    x3 = lambda ^ 2 - x1 - x2 ∧
    y3 = lambda * (x1 - x3) - y1 ∧
    lambda * (x2 - x1) = y2 - y1 ∧
    y3 ^ 2 = x3 ^ 3 - 17 := by
  -- From x1 ≠ x2 the selector layer pins same_x = 0, hence is_double = 0
  -- and is_inverse = 0 — but we also assume is_inverse = 0 explicitly via
  -- the witness shape. Let's derive same_x, is_double, is_inverse.
  have hsx : same_x = 0 := same_x_eq_zero_of_x_ne h.sel.same_x_zero hxne
  -- is_double = same_x * same_y * (1 - lhs_inf) * (1 - rhs_inf), and same_x = 0.
  have hid : is_double = 0 := by
    rw [h.sel.is_double_def, hsx]; ring
  have hii : is_inverse = 0 := by
    rw [h.sel.is_inverse_def, hsx]; ring
  -- Slope: the generic-slope gate fires because all four factors are 1.
  have hS : lambda * (x2 - x1) = y2 - y1 := by
    -- (1 − is_inf1)(1 − is_inf2)(1 − is_double)(1 − is_inverse) = 1 here.
    have hg := h.slope_generic
    -- Substitute the values.
    rw [hid, hii] at hg
    -- Now hg : (1 - 0)*(1 - 0)*(1 - 0)*(1 - 0) * ((x2 - x1)*lambda - (y2 - y1)) = 0
    have : (x2 - x1) * lambda - (y2 - y1) = 0 := by linear_combination hg
    linear_combination this
  -- Output mux: lhs_inf = 0, rhs_inf = 0, is_inverse = 0 ⇒ output = (xg, yg, 0).
  have hmux : x3 = xg ∧ y3 = yg ∧ is_inf3 = 0 := by
    -- Need is_inverse = 0 in the mux; we have hii.
    have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 0 0 0 x3 y3 is_inf3 := by
      refine ⟨?_, ?_, ?_⟩
      · have := h.mux.x3_def; rw [hii] at this; exact this
      · have := h.mux.y3_def; rw [hii] at this; exact this
      · have := h.mux.is_inf3_def; rw [hii] at this; exact this
    exact output_mux_generic hmux_at
  obtain ⟨hx3, hy3, hi3⟩ := hmux
  -- Substitute xg, yg into x3, y3 to get the generic formulas.
  have hx3' : x3 = lambda ^ 2 - x1 - x2 := by rw [hx3, h.xg_def]
  have hy3' : y3 = lambda * (x1 - x3) - y1 := by
    rw [hy3, h.yg_def, hx3, h.xg_def]
  -- On-curve: discharge the input curve membership and feed into
  -- `ec_add_generic_on_curve` (specialized to `a = 0`, `b = −17`).
  have hC1 : y1 ^ 2 = x1 ^ 3 - 17 :=
    gated_on_curve_sound x1 y1 0 h.is_inf1_bool h.on_curve1 rfl
  have hC2 : y2 ^ 2 = x2 ^ 3 - 17 :=
    gated_on_curve_sound x2 y2 0 h.is_inf2_bool h.on_curve2 rfl
  -- Cast to the `y² = x³ + a·x + b` form used by `ec_add_generic_on_curve`.
  have hE1 : y1 ^ 2 = x1 ^ 3 + (0 : F) * x1 + (-17) := by linear_combination hC1
  have hE2 : y2 ^ 2 = x2 ^ 3 + (0 : F) * x2 + (-17) := by linear_combination hC2
  have hOC :=
    ec_add_generic_on_curve (a := (0 : F)) (b := (-17 : F))
      x1 y1 x2 y2 lambda hxne hE1 hE2 hS
  -- Translate back: `(... + a·x3 + b)` with `a = 0, b = -17` is `... - 17`.
  have hy3_sq : y3 ^ 2 = x3 ^ 3 - 17 := by
    rw [hy3', hx3']
    linear_combination hOC
  exact ⟨hi3, hx3', hy3', hS, hy3_sq⟩

/-- **End-to-end soundness — full 4-way wrapper.** Under
`IsValidECAddWitness`, the output triple `(x3, y3, is_inf3)` is the
algebraically-correct group sum of the inputs in every routing branch
(infinity, inverse, generic, doubling), as captured by `EcAddSemantics`.

Proof: case-split on `is_inf1`, `is_inf2`, and the selector booleans
that the witness derives (`is_inverse`, `is_double`); apply the
appropriate per-branch theorem (output-mux lemmas, slope lemmas,
selector-correspondence lemmas) to discharge each case. The two
infinity branches reduce directly via the mux. For both-finite, we
dispatch by `same_x` and `same_y` derived from the selector layer:

* `same_x = 0` (so `x1 ≠ x2`) → generic branch.
* `same_x = 1, same_y = 0` → inverse branch.
* `same_x = 1, same_y = 1` → doubling branch.

The `same_x = 1` cases use `same_x_inv : (x2 − x1)·inv_dx = 1 − same_x`
to recover `x1 = x2` algebraically without `DecidableEq F`. The
doubling sub-case additionally requires `2·y1 ≠ 0` (i.e. `y1 ≠ 0` over
the odd-characteristic Grumpkin base field) for the slope to be
well-defined; this matches `ec_double_slope_unique`. -/
theorem ec_add_in_circuit_sound {F : Type*} [Field F]
    {x1 y1 is_inf1 x2 y2 is_inf2 lambda
     same_x same_y is_double is_inverse inv_dx inv_dy
     xg yg x3 y3 is_inf3 : F}
    (h : IsValidECAddWitness x1 y1 is_inf1 x2 y2 is_inf2 lambda
            same_x same_y is_double is_inverse inv_dx inv_dy
            xg yg x3 y3 is_inf3)
    (h2y : is_inf1 = 0 → is_inf2 = 0 → x1 = x2 → y1 = y2 → (2 : F) * y1 ≠ 0) :
    EcAddSemantics (x1, y1, is_inf1) (x2, y2, is_inf2) (x3, y3, is_inf3) := by
  classical
  -- The infinity flags are boolean.
  have hi1 : is_inf1 = 0 ∨ is_inf1 = 1 := by
    rcases mul_eq_zero.mp h.is_inf1_bool with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have hi2 : is_inf2 = 0 ∨ is_inf2 = 1 := by
    rcases mul_eq_zero.mp h.is_inf2_bool with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases hi1 with hi1 | hi1
  · rcases hi2 with hi2 | hi2
    · -- both finite: split further on selector cases
      subst hi1; subst hi2
      -- Dispatch by same_x.
      by_cases hxeq : x1 = x2
      · -- same_x = 1 case.
        have hsx : same_x = 1 := same_x_eq_one_of_x_eq h.sel.same_x_inv hxeq
        by_cases hyeq : y1 = y2
        · -- same_y = 1: doubling branch.
          have hsy : same_y = 1 := same_x_eq_one_of_x_eq h.sel.same_y_inv hyeq
          -- is_double = 1, is_inverse = 0.
          have hid : is_double = 1 := by
            rw [h.sel.is_double_def, hsx, hsy]; ring
          have hii : is_inverse = 0 := by
            rw [h.sel.is_inverse_def, hsy]; ring
          -- Doubling slope holds.
          have h2y' : (2 : F) * y1 ≠ 0 := h2y rfl rfl hxeq hyeq
          have hSd : lambda * (2 * y1) = 3 * x1 ^ 2 := by
            have hd := h.slope_double
            rw [hid] at hd
            have : (2 * y1 * lambda - 3 * x1 ^ 2) = 0 := by linear_combination hd
            linear_combination this
          -- Output mux: generic branch since is_inverse = 0.
          have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 0 0 0 x3 y3 is_inf3 := by
            refine ⟨?_, ?_, ?_⟩
            · have := h.mux.x3_def; rw [hii] at this; exact this
            · have := h.mux.y3_def; rw [hii] at this; exact this
            · have := h.mux.is_inf3_def; rw [hii] at this; exact this
          obtain ⟨hx3, hy3, hi3⟩ := output_mux_generic hmux_at
          -- Now x3 = xg = λ² − x1 − x2 = λ² − 2·x1 (since x1 = x2).
          have hx3' : x3 = lambda ^ 2 - 2 * x1 := by
            rw [hx3, h.xg_def, ← hxeq]; ring
          have hy3' : y3 = lambda * (x1 - (lambda ^ 2 - 2 * x1)) - y1 := by
            rw [hy3, h.yg_def, h.xg_def, ← hxeq]; ring
          -- Rewrite the inputs: P2 = P1 (since x1 = x2, y1 = y2).
          rw [← hxeq, ← hyeq, hx3', hy3', hi3]
          exact EcAddSemantics.doubling h2y' hSd
        · -- same_y = 0: inverse branch.
          have hsy : same_y = 0 := same_x_eq_zero_of_x_ne h.sel.same_y_zero hyeq
          have hid : is_double = 0 := by
            rw [h.sel.is_double_def, hsy]; ring
          have hii : is_inverse = 1 := by
            rw [h.sel.is_inverse_def, hsx, hsy]; ring
          -- Output mux: inverse branch.
          have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 0 0 1 x3 y3 is_inf3 := by
            refine ⟨?_, ?_, ?_⟩
            · have := h.mux.x3_def; rw [hii] at this; exact this
            · have := h.mux.y3_def; rw [hii] at this; exact this
            · have := h.mux.is_inf3_def; rw [hii] at this; exact this
          obtain ⟨hx3, hy3, hi3⟩ := output_mux_inverse hmux_at
          rw [hx3, hy3, hi3]
          -- For inverse: need x1 = x2 (given) and y1 + y2 = 0.
          -- From same_y = 0 and same_y_zero we have same_y*(y2-y1) = 0
          -- which is trivial. We need a separate argument.
          -- Actually: in the inverse branch the gadget routes to `∞` for ANY
          -- finite (x1, y1), (x2, y2) with same_x = 1, same_y = 0. To match
          -- EcAddSemantics.inverse we need y1 + y2 = 0; this is NOT forced
          -- by the gadget alone — it's forced by the on-curve constraints
          -- combined with x1 = x2.
          --
          -- y1² = x1³ − 17 and y2² = x2³ − 17 = x1³ − 17 (since x1 = x2),
          -- so y1² = y2², i.e. (y1 − y2)(y1 + y2) = 0. Since y1 ≠ y2, we
          -- get y1 + y2 = 0.
          have hC1 : y1 ^ 2 = x1 ^ 3 - 17 :=
            gated_on_curve_sound x1 y1 0 h.is_inf1_bool h.on_curve1 rfl
          have hC2 : y2 ^ 2 = x2 ^ 3 - 17 :=
            gated_on_curve_sound x2 y2 0 h.is_inf2_bool h.on_curve2 rfl
          have hyy : y1 ^ 2 = y2 ^ 2 := by
            rw [hC1, hC2, hxeq]
          have hfact : (y1 - y2) * (y1 + y2) = 0 := by linear_combination hyy
          have hyne : y1 - y2 ≠ 0 := sub_ne_zero.mpr hyeq
          have hysum : y1 + y2 = 0 := (mul_eq_zero.mp hfact).resolve_left hyne
          exact EcAddSemantics.inverse hxeq hysum
      · -- same_x = 0: generic branch.
        have hsx : same_x = 0 := same_x_eq_zero_of_x_ne h.sel.same_x_zero hxeq
        have hid : is_double = 0 := by
          rw [h.sel.is_double_def, hsx]; ring
        have hii : is_inverse = 0 := by
          rw [h.sel.is_inverse_def, hsx]; ring
        have hS : lambda * (x2 - x1) = y2 - y1 := by
          have hg := h.slope_generic
          rw [hid, hii] at hg
          have : (x2 - x1) * lambda - (y2 - y1) = 0 := by linear_combination hg
          linear_combination this
        have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 0 0 0 x3 y3 is_inf3 := by
          refine ⟨?_, ?_, ?_⟩
          · have := h.mux.x3_def; rw [hii] at this; exact this
          · have := h.mux.y3_def; rw [hii] at this; exact this
          · have := h.mux.is_inf3_def; rw [hii] at this; exact this
        obtain ⟨hx3, hy3, hi3⟩ := output_mux_generic hmux_at
        have hx3' : x3 = lambda ^ 2 - x1 - x2 := by rw [hx3, h.xg_def]
        have hy3' : y3 = lambda * (x1 - (lambda ^ 2 - x1 - x2)) - y1 := by
          rw [hy3, h.yg_def, h.xg_def]
        rw [hx3', hy3', hi3]
        exact EcAddSemantics.generic hxeq hS
    · -- rhs_inf = 1, lhs_inf = 0.
      subst hi1; subst hi2
      have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 0 1 is_inverse x3 y3 is_inf3 := h.mux
      obtain ⟨hx3, hy3, hi3⟩ := output_mux_rhs_inf hmux_at
      rw [hx3, hy3, hi3]
      exact EcAddSemantics.rhs_inf
  · -- lhs_inf = 1.
    subst hi1
    have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 1 is_inf2 is_inverse x3 y3 is_inf3 := h.mux
    obtain ⟨hx3, hy3, hi3⟩ := output_mux_lhs_inf hmux_at
    rw [hx3, hy3, hi3]
    exact EcAddSemantics.lhs_inf

end Xark
