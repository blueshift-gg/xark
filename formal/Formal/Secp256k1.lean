/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Curve
import Formal.EcdsaVerify
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# secp256k1 in-circuit point-addition soundness (Layer B)

`crates/acir-r1cs/src/gadgets/ecdsa.rs::ec_add_in_circuit` (specialised for the
secp256k1 curve via `CurveParams::secp256k1()`) adds points on

    y² = x³ + 7

over the secp256k1 base field. The gadget shape — gated on-curve check,
generic and doubling slope constraints, selector layer, 4-way output mux —
is identical to the Grumpkin gadget in `Formal.Curve`; only the curve
constant changes (`b = 7` instead of Grumpkin's `b = −17`). Because the
Grumpkin theorems

* `ec_add_generic_slope_unique`  — *curve-agnostic* (works in any field)
* `ec_add_generic_on_curve`      — *parametric in `(a, b)`*
* `ec_double_slope_unique`       — *curve-agnostic*
* `ec_double_on_curve`           — *parametric in `b`* (`a = 0` hard-coded;
                                    matches secp256k1's short Weierstrass form)
* `IsSelectorWitness` / `selector_unique` / `IsOutputMux` / `output_mux_*`
                                 — *curve-agnostic* (selector + mux layer)

are already general enough, this file only needs to re-instantiate the
**curve-equation-specific** pieces:

* `gated_on_curve_secp256k1_sound` / `_trivial` / `enforce_on_curve_secp256k1_sound`
  — the gated curve-membership check with `y² − x³ − 7 = 0`.
* `IsValidECAddWitness_secp256k1` — the bundled witness predicate, with the
  curve constraint `(1 − is_inf) · (y² − x³ − 7) = 0`.
* `EcAddSemantics_secp256k1` — the group-law relation; structurally
  identical to `Formal.Curve.EcAddSemantics` because secp256k1 also has
  `a = 0` (so the doubling slope is `λ·(2·y₁) = 3·x₁²`, same as Grumpkin).
* `ec_add_in_circuit_secp256k1_sound` — the end-to-end soundness wrapper.

Together with the `ecdsa_verify_compose` theorem in `Formal.EcdsaVerify`
(parametric over the curve group `G : Type*` `[AddCommGroup G]`), this
closes the chain for **concrete secp256k1 ECDSA verification** in Lean,
modulo:

* The Solana `alt_bn128` syscall ↔ Arkworks fallback agreement
  (residual trust assumption — out of scope for FV).
* The `secp256k1` point-group structure existing as an `AddCommGroup`
  instance over `(x, y) | y² = x³ + 7` ∪ {∞}. The group-law associativity
  and identity laws are standard textbook results; the gadget faithfully
  implements them per the per-branch soundness wrapper here.

## Theorem index

| Name                                       | Statement |
|--------------------------------------------|-----------|
| `gated_on_curve_secp256k1_sound`           | `is_inf = 0 ⇒ y² = x³ + 7`               |
| `gated_on_curve_secp256k1_trivial`         | constraint is vacuous when `is_inf = 1`  |
| `enforce_on_curve_secp256k1_sound`         | `is_inf = 1 ∨ y² = x³ + 7`               |
| `IsValidECAddWitness_secp256k1`            | gadget intermediate-state predicate      |
| `EcAddSemantics_secp256k1`                 | group-law spec relation                  |
| `ec_add_in_circuit_secp256k1_generic_sound`| generic-branch end-to-end                |
| `ec_add_in_circuit_secp256k1_sound`        | full 4-way end-to-end                    |
-/

namespace Xark

/-! ## Gated curve check at `y² = x³ + 7` -/

/-- **Gated curve check — non-infinity branch (secp256k1).** Given the boolean
witness for `is_infinity` and the gated curve constraint, when `is_infinity = 0`
we have `y² = x³ + 7`, i.e. `(x, y) ∈ secp256k1`. -/
theorem gated_on_curve_secp256k1_sound {F : Type*} [Field F]
    (x y is_inf : F)
    (_hbool : is_inf * (is_inf - 1) = 0)
    (hgate : (1 - is_inf) * (y ^ 2 - x ^ 3 - 7) = 0)
    (hzero : is_inf = 0) :
    y ^ 2 = x ^ 3 + 7 := by
  have h : y ^ 2 - x ^ 3 - 7 = 0 := by
    have := hgate
    rw [hzero] at this
    linear_combination this
  linear_combination h

/-- **Gated curve check — infinity branch (vacuity).** When `is_infinity = 1`
the gated constraint `(1 − is_infinity) · _ = 0` holds trivially. -/
theorem gated_on_curve_secp256k1_trivial {F : Type*} [Field F] (x y : F) :
    (1 - (1 : F)) * (y ^ 2 - x ^ 3 - 7) = 0 := by
  ring

/-- **Packaged gated-curve soundness (secp256k1).** A boolean `is_infinity`
satisfying the gated curve constraint is either the point at infinity or a
finite secp256k1 point. -/
theorem enforce_on_curve_secp256k1_sound {F : Type*} [Field F]
    (x y is_inf : F)
    (hbool : is_inf * (is_inf - 1) = 0)
    (hgate : (1 - is_inf) * (y ^ 2 - x ^ 3 - 7) = 0) :
    is_inf = 1 ∨ y ^ 2 = x ^ 3 + 7 := by
  have hcases : is_inf = 0 ∨ is_inf = 1 := by
    rcases mul_eq_zero.mp hbool with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases hcases with h0 | h1
  · exact Or.inr (gated_on_curve_secp256k1_sound x y is_inf hbool hgate h0)
  · exact Or.inl h1

/-! ## Bundled witness predicate

Mirrors `IsValidECAddWitness` (Grumpkin) line-for-line; the only change is the
curve constraint `y² = x³ + 7` instead of `y² = x³ − 17`. The doubling slope
`λ·(2·y₁) = 3·x₁²` matches the gadget because secp256k1 has `a = 0`. -/

/-- **Bundled witness predicate** for `ec_add_in_circuit` on secp256k1. -/
structure IsValidECAddWitness_secp256k1 {F : Type*} [Field F]
    (x1 y1 is_inf1 x2 y2 is_inf2 lambda
     same_x same_y is_double is_inverse inv_dx inv_dy
     xg yg x3 y3 is_inf3 : F) : Prop where
  on_curve1     : (1 - is_inf1) * (y1 ^ 2 - x1 ^ 3 - 7) = 0
  on_curve2     : (1 - is_inf2) * (y2 ^ 2 - x2 ^ 3 - 7) = 0
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

/-! ## Group-law specification

Identical structure to `Formal.Curve.EcAddSemantics`: both Grumpkin and
secp256k1 have `a = 0`, so the generic-slope, doubling-slope, and inverse-
case branches all share the same algebraic form. We re-state with the
`_secp256k1` suffix to keep the proof of `ec_add_in_circuit_secp256k1_sound`
self-contained. -/

/-- **Algebraic group-operation specification (secp256k1).** Same structure
as `EcAddSemantics` from `Formal.Curve`. -/
inductive EcAddSemantics_secp256k1 {F : Type*} [Field F] :
    F × F × F → F × F × F → F × F × F → Prop where
  | lhs_inf {x1 y1 x2 y2 is_inf2 : F} :
      EcAddSemantics_secp256k1 (x1, y1, 1) (x2, y2, is_inf2) (x2, y2, is_inf2)
  | rhs_inf {x1 y1 x2 y2 : F} :
      EcAddSemantics_secp256k1 (x1, y1, 0) (x2, y2, 1) (x1, y1, 0)
  | inverse {x1 y1 x2 y2 : F} (_hx : x1 = x2) (_hy : y1 + y2 = 0) :
      EcAddSemantics_secp256k1 (x1, y1, 0) (x2, y2, 0) (0, 0, 1)
  | generic {x1 y1 x2 y2 lambda : F} (_hx : x1 ≠ x2)
      (_hS : lambda * (x2 - x1) = y2 - y1) :
      EcAddSemantics_secp256k1 (x1, y1, 0) (x2, y2, 0)
        (lambda ^ 2 - x1 - x2,
         lambda * (x1 - (lambda ^ 2 - x1 - x2)) - y1,
         0)
  | doubling {x1 y1 lambda : F} (_h2y : (2 : F) * y1 ≠ 0)
      (_hS : lambda * (2 * y1) = 3 * x1 ^ 2) :
      EcAddSemantics_secp256k1 (x1, y1, 0) (x1, y1, 0)
        (lambda ^ 2 - 2 * x1,
         lambda * (x1 - (lambda ^ 2 - 2 * x1)) - y1,
         0)

/-! ## End-to-end soundness, generic branch -/

/-- **End-to-end soundness — generic branch (secp256k1).** Mirrors
`Formal.Curve.ec_add_in_circuit_generic_sound`. Under
`IsValidECAddWitness_secp256k1` with both inputs finite and `x1 ≠ x2`,
the gadget output is the generic-add result with `(x3, y3)` on secp256k1. -/
theorem ec_add_in_circuit_secp256k1_generic_sound {F : Type*} [Field F]
    {x1 y1 x2 y2 lambda same_x same_y is_double is_inverse
     inv_dx inv_dy xg yg x3 y3 is_inf3 : F}
    (h : IsValidECAddWitness_secp256k1 x1 y1 0 x2 y2 0 lambda
            same_x same_y is_double is_inverse inv_dx inv_dy
            xg yg x3 y3 is_inf3)
    (hxne : x1 ≠ x2) :
    is_inf3 = 0 ∧
    x3 = lambda ^ 2 - x1 - x2 ∧
    y3 = lambda * (x1 - x3) - y1 ∧
    lambda * (x2 - x1) = y2 - y1 ∧
    y3 ^ 2 = x3 ^ 3 + 7 := by
  -- selector layer: same_x = 0 ⇒ is_double = 0, is_inverse = 0.
  have hsx : same_x = 0 := same_x_eq_zero_of_x_ne h.sel.same_x_zero hxne
  have hid : is_double = 0 := by
    rw [h.sel.is_double_def, hsx]; ring
  have hii : is_inverse = 0 := by
    rw [h.sel.is_inverse_def, hsx]; ring
  -- generic slope identity fires:
  have hS : lambda * (x2 - x1) = y2 - y1 := by
    have hg := h.slope_generic
    rw [hid, hii] at hg
    have : (x2 - x1) * lambda - (y2 - y1) = 0 := by linear_combination hg
    linear_combination this
  -- output mux routes to generic branch:
  have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 0 0 0 x3 y3 is_inf3 := by
    refine ⟨?_, ?_, ?_⟩
    · have := h.mux.x3_def; rw [hii] at this; exact this
    · have := h.mux.y3_def; rw [hii] at this; exact this
    · have := h.mux.is_inf3_def; rw [hii] at this; exact this
  obtain ⟨hx3, hy3, hi3⟩ := output_mux_generic hmux_at
  have hx3' : x3 = lambda ^ 2 - x1 - x2 := by rw [hx3, h.xg_def]
  have hy3' : y3 = lambda * (x1 - x3) - y1 := by
    rw [hy3, h.yg_def, hx3, h.xg_def]
  -- discharge on-curve hypotheses for the two inputs (curve eqn y² = x³ + 7):
  have hC1 : y1 ^ 2 = x1 ^ 3 + 7 :=
    gated_on_curve_secp256k1_sound x1 y1 0 h.is_inf1_bool h.on_curve1 rfl
  have hC2 : y2 ^ 2 = x2 ^ 3 + 7 :=
    gated_on_curve_secp256k1_sound x2 y2 0 h.is_inf2_bool h.on_curve2 rfl
  -- recast to `y² = x³ + a·x + b` form (a = 0, b = 7):
  have hE1 : y1 ^ 2 = x1 ^ 3 + (0 : F) * x1 + 7 := by linear_combination hC1
  have hE2 : y2 ^ 2 = x2 ^ 3 + (0 : F) * x2 + 7 := by linear_combination hC2
  -- apply the parametric Grumpkin generic-on-curve theorem with (a, b) = (0, 7):
  have hOC :=
    ec_add_generic_on_curve (a := (0 : F)) (b := (7 : F))
      x1 y1 x2 y2 lambda hxne hE1 hE2 hS
  have hy3_sq : y3 ^ 2 = x3 ^ 3 + 7 := by
    rw [hy3', hx3']
    linear_combination hOC
  exact ⟨hi3, hx3', hy3', hS, hy3_sq⟩

/-! ## End-to-end soundness, full 4-way wrapper

Mirrors `Formal.Curve.ec_add_in_circuit_sound` with the curve equation
swapped from `y² = x³ − 17` to `y² = x³ + 7`. -/

/-- **End-to-end soundness — full 4-way wrapper (secp256k1).** Under
`IsValidECAddWitness_secp256k1`, the output triple satisfies the group-law
relation `EcAddSemantics_secp256k1`. -/
theorem ec_add_in_circuit_secp256k1_sound {F : Type*} [Field F]
    {x1 y1 is_inf1 x2 y2 is_inf2 lambda
     same_x same_y is_double is_inverse inv_dx inv_dy
     xg yg x3 y3 is_inf3 : F}
    (h : IsValidECAddWitness_secp256k1 x1 y1 is_inf1 x2 y2 is_inf2 lambda
            same_x same_y is_double is_inverse inv_dx inv_dy
            xg yg x3 y3 is_inf3)
    (h2y : is_inf1 = 0 → is_inf2 = 0 → x1 = x2 → y1 = y2 → (2 : F) * y1 ≠ 0) :
    EcAddSemantics_secp256k1 (x1, y1, is_inf1) (x2, y2, is_inf2) (x3, y3, is_inf3) := by
  classical
  -- infinity flags are boolean (mirrors Grumpkin proof structure).
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
    · -- both finite: split by selector.
      subst hi1; subst hi2
      by_cases hxeq : x1 = x2
      · have hsx : same_x = 1 := same_x_eq_one_of_x_eq h.sel.same_x_inv hxeq
        by_cases hyeq : y1 = y2
        · -- doubling.
          have hsy : same_y = 1 := same_x_eq_one_of_x_eq h.sel.same_y_inv hyeq
          have hid : is_double = 1 := by
            rw [h.sel.is_double_def, hsx, hsy]; ring
          have hii : is_inverse = 0 := by
            rw [h.sel.is_inverse_def, hsy]; ring
          have h2y' : (2 : F) * y1 ≠ 0 := h2y rfl rfl hxeq hyeq
          have hSd : lambda * (2 * y1) = 3 * x1 ^ 2 := by
            have hd := h.slope_double
            rw [hid] at hd
            have : (2 * y1 * lambda - 3 * x1 ^ 2) = 0 := by linear_combination hd
            linear_combination this
          have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 0 0 0 x3 y3 is_inf3 := by
            refine ⟨?_, ?_, ?_⟩
            · have := h.mux.x3_def; rw [hii] at this; exact this
            · have := h.mux.y3_def; rw [hii] at this; exact this
            · have := h.mux.is_inf3_def; rw [hii] at this; exact this
          obtain ⟨hx3, hy3, hi3⟩ := output_mux_generic hmux_at
          have hx3' : x3 = lambda ^ 2 - 2 * x1 := by
            rw [hx3, h.xg_def, ← hxeq]; ring
          have hy3' : y3 = lambda * (x1 - (lambda ^ 2 - 2 * x1)) - y1 := by
            rw [hy3, h.yg_def, h.xg_def, ← hxeq]; ring
          rw [← hxeq, ← hyeq, hx3', hy3', hi3]
          exact EcAddSemantics_secp256k1.doubling h2y' hSd
        · -- inverse.
          have hsy : same_y = 0 := same_x_eq_zero_of_x_ne h.sel.same_y_zero hyeq
          have hid : is_double = 0 := by
            rw [h.sel.is_double_def, hsy]; ring
          have hii : is_inverse = 1 := by
            rw [h.sel.is_inverse_def, hsx, hsy]; ring
          have hmux_at : IsOutputMux x1 y1 x2 y2 xg yg 0 0 1 x3 y3 is_inf3 := by
            refine ⟨?_, ?_, ?_⟩
            · have := h.mux.x3_def; rw [hii] at this; exact this
            · have := h.mux.y3_def; rw [hii] at this; exact this
            · have := h.mux.is_inf3_def; rw [hii] at this; exact this
          obtain ⟨hx3, hy3, hi3⟩ := output_mux_inverse hmux_at
          rw [hx3, hy3, hi3]
          -- need: y1 + y2 = 0. Same argument as Grumpkin but with curve eqn y² = x³ + 7:
          -- y1² = x1³ + 7, y2² = x2³ + 7 = x1³ + 7, so y1² = y2², factor.
          have hC1 : y1 ^ 2 = x1 ^ 3 + 7 :=
            gated_on_curve_secp256k1_sound x1 y1 0 h.is_inf1_bool h.on_curve1 rfl
          have hC2 : y2 ^ 2 = x2 ^ 3 + 7 :=
            gated_on_curve_secp256k1_sound x2 y2 0 h.is_inf2_bool h.on_curve2 rfl
          have hyy : y1 ^ 2 = y2 ^ 2 := by
            rw [hC1, hC2, hxeq]
          have hfact : (y1 - y2) * (y1 + y2) = 0 := by linear_combination hyy
          have hyne : y1 - y2 ≠ 0 := sub_ne_zero.mpr hyeq
          have hysum : y1 + y2 = 0 := (mul_eq_zero.mp hfact).resolve_left hyne
          exact EcAddSemantics_secp256k1.inverse hxeq hysum
      · -- generic.
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
        exact EcAddSemantics_secp256k1.generic hxeq hS
    · -- rhs_inf branch: is_inf1 = 0, is_inf2 = 1.
      subst hi1; subst hi2
      -- Output mux routes via rhs_inf.
      have hmux := h.mux
      -- The mux relation gives x3 = ..., y3 = ..., is_inf3 = ... explicitly
      -- in the rhs_inf case. Extract via output_mux_rhs_inf.
      obtain ⟨hx3, hy3, hi3⟩ := output_mux_rhs_inf hmux
      rw [hx3, hy3, hi3]
      exact EcAddSemantics_secp256k1.rhs_inf
  · -- lhs_inf branch: is_inf1 = 1.
    subst hi1
    obtain ⟨hx3, hy3, hi3⟩ := output_mux_lhs_inf h.mux
    rw [hx3, hy3, hi3]
    exact EcAddSemantics_secp256k1.lhs_inf

end Xark
