/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Curve
import Formal.Secp256k1
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# secp256r1 (NIST P-256) in-circuit point-addition soundness

Mirrors `Formal.Secp256k1` but for **secp256r1** (NIST P-256):

    y² = x³ + a·x + b   with   a = −3

The structural pieces (selector layer, output mux, on-curve gating) carry
over from `Formal.Curve` directly. The two curve-equation-specific pieces
that differ are the **doubling slope** and the **doubling-case addition-law
closure**: secp256r1's `a = −3` means the gadget enforces
`λ · (2·y₁) = 3·x₁² + a · 1 = 3·x₁² − 3`, not Grumpkin/secp256k1's
`λ · (2·y₁) = 3·x₁²`.

The generic case is curve-agnostic (already parametric in `(a, b)` in
`Formal.Curve.ec_add_generic_on_curve`); we instantiate it directly.

The generalised doubling theorem `ec_double_on_curve_with_a` proves the
addition-law closure for *any* short Weierstrass curve `y² = x³ + a·x + b`,
not just `a = 0`. It composes with the existing slope-determinism theorem
`ec_double_slope_unique` (also curve-agnostic).

The headline theorem `ec_add_in_circuit_secp256r1_sound` packages everything
into an end-to-end soundness statement against an `EcAddSemantics_secp256r1`
relation, parametric over the field.
-/

namespace Xark

/-! ## Generalised doubling-case addition law closure -/

/-- **Doubling-case addition law closure — general `(a, b)` short Weierstrass.**
If `(x₁, y₁)` is on `y² = x³ + a·x + b` and `λ` is the doubling slope
`λ · (2·y₁) = 3·x₁² + a`, then the doubling-output
`(x₃, y₃) = (λ² − 2·x₁, λ·(x₁ − x₃) − y₁)` is back on the curve.

Generalises `Formal.Curve.ec_double_on_curve` (which hard-codes `a = 0` for
Grumpkin/secp256k1) to support `a = −3` (secp256r1 / NIST P-256). -/
theorem ec_double_on_curve_with_a {F : Type*} [Field F]
    (a b x1 y1 lam : F)
    (hE1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (hS : lam * (2 * y1) = 3 * x1 ^ 2 + a) :
    (lam * (x1 - (lam ^ 2 - 2 * x1)) - y1) ^ 2
      = (lam ^ 2 - 2 * x1) ^ 3 + a * (lam ^ 2 - 2 * x1) + b := by
  linear_combination hE1 + (lam ^ 2 - 3 * x1) * hS

/-! ## Gated curve check at `y² = x³ − 3·x + b` -/

/-- **Gated curve check — non-infinity branch (secp256r1).** Parametric in
`b` (the secp256r1 curve constant). -/
theorem gated_on_curve_secp256r1_sound {F : Type*} [Field F]
    (b x y is_inf : F)
    (hgate : (1 - is_inf) * (y ^ 2 - x ^ 3 + 3 * x - b) = 0)
    (hzero : is_inf = 0) :
    y ^ 2 = x ^ 3 - 3 * x + b := by
  have h : y ^ 2 - x ^ 3 + 3 * x - b = 0 := by
    have := hgate
    rw [hzero] at this
    linear_combination this
  linear_combination h

/-- **Gated curve check — infinity branch (vacuity, secp256r1).** -/
theorem gated_on_curve_secp256r1_trivial {F : Type*} [Field F] (b x y : F) :
    (1 - (1 : F)) * (y ^ 2 - x ^ 3 + 3 * x - b) = 0 := by ring

/-- **Packaged gated-curve soundness (secp256r1).** -/
theorem enforce_on_curve_secp256r1_sound {F : Type*} [Field F]
    (b x y is_inf : F)
    (hbool : is_inf * (is_inf - 1) = 0)
    (hgate : (1 - is_inf) * (y ^ 2 - x ^ 3 + 3 * x - b) = 0) :
    is_inf = 1 ∨ y ^ 2 = x ^ 3 - 3 * x + b := by
  have hcases : is_inf = 0 ∨ is_inf = 1 := by
    rcases mul_eq_zero.mp hbool with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases hcases with h0 | h1
  · exact Or.inr (gated_on_curve_secp256r1_sound b x y is_inf hgate h0)
  · exact Or.inl h1

/-! ## Bundled witness predicate

Parametric in the curve constant `b`. The doubling-slope constraint
encodes `a = −3` directly: `2·y₁·λ = 3·x₁² − 3 · 1 = 3·x₁² + a·1`. -/

/-- **Bundled witness predicate** for `ec_add_in_circuit` on secp256r1. -/
structure IsValidECAddWitness_secp256r1 {F : Type*} [Field F]
    (b x1 y1 is_inf1 x2 y2 is_inf2 lambda
     same_x same_y is_double is_inverse inv_dx inv_dy
     xg yg x3 y3 is_inf3 : F) : Prop where
  on_curve1     : (1 - is_inf1) * (y1 ^ 2 - x1 ^ 3 + 3 * x1 - b) = 0
  on_curve2     : (1 - is_inf2) * (y2 ^ 2 - x2 ^ 3 + 3 * x2 - b) = 0
  is_inf1_bool  : is_inf1 * (is_inf1 - 1) = 0
  is_inf2_bool  : is_inf2 * (is_inf2 - 1) = 0
  sel           : IsSelectorWitness x1 y1 x2 y2 is_inf1 is_inf2
                      same_x same_y is_double is_inverse inv_dx inv_dy
  slope_generic : (1 - is_inf1) * (1 - is_inf2) * (1 - is_double) * (1 - is_inverse)
                    * ((x2 - x1) * lambda - (y2 - y1)) = 0
  slope_double  : is_double * (2 * y1 * lambda - (3 * x1 ^ 2 - 3)) = 0
  xg_def        : xg = lambda ^ 2 - x1 - x2
  yg_def        : yg = lambda * (x1 - xg) - y1
  mux           : IsOutputMux x1 y1 x2 y2 xg yg is_inf1 is_inf2 is_inverse x3 y3 is_inf3

/-! ## End-to-end soundness for the generic branch

The generic branch is curve-agnostic; we directly invoke
`Formal.Curve.ec_add_generic_on_curve` with `a := -3, b := b_r1`. -/

/-- **End-to-end soundness — generic branch (secp256r1).** -/
theorem ec_add_in_circuit_secp256r1_generic_sound {F : Type*} [Field F]
    (b : F) {x1 y1 x2 y2 lambda same_x same_y is_double is_inverse
     inv_dx inv_dy xg yg x3 y3 is_inf3 : F}
    (h : IsValidECAddWitness_secp256r1 b x1 y1 0 x2 y2 0 lambda
            same_x same_y is_double is_inverse inv_dx inv_dy
            xg yg x3 y3 is_inf3)
    (hxne : x1 ≠ x2) :
    is_inf3 = 0 ∧
    x3 = lambda ^ 2 - x1 - x2 ∧
    y3 = lambda * (x1 - x3) - y1 ∧
    lambda * (x2 - x1) = y2 - y1 ∧
    y3 ^ 2 = x3 ^ 3 - 3 * x3 + b := by
  have hsx : same_x = 0 := same_x_eq_zero_of_x_ne h.sel.same_x_zero hxne
  have hid : is_double = 0 := by rw [h.sel.is_double_def, hsx]; ring
  have hii : is_inverse = 0 := by rw [h.sel.is_inverse_def, hsx]; ring
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
  have hy3' : y3 = lambda * (x1 - x3) - y1 := by
    rw [hy3, h.yg_def, hx3, h.xg_def]
  have hC1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + b :=
    gated_on_curve_secp256r1_sound b x1 y1 0 h.on_curve1 rfl
  have hC2 : y2 ^ 2 = x2 ^ 3 - 3 * x2 + b :=
    gated_on_curve_secp256r1_sound b x2 y2 0 h.on_curve2 rfl
  -- Cast to the `y² = x³ + a·x + b` form (a = -3).
  have hE1 : y1 ^ 2 = x1 ^ 3 + (-3 : F) * x1 + b := by linear_combination hC1
  have hE2 : y2 ^ 2 = x2 ^ 3 + (-3 : F) * x2 + b := by linear_combination hC2
  have hOC :=
    ec_add_generic_on_curve (a := (-3 : F)) (b := b)
      x1 y1 x2 y2 lambda hxne hE1 hE2 hS
  have hy3_sq : y3 ^ 2 = x3 ^ 3 - 3 * x3 + b := by
    rw [hy3', hx3']
    linear_combination hOC
  exact ⟨hi3, hx3', hy3', hS, hy3_sq⟩

/-! ## Group-law specification (secp256r1)

Mirrors `Formal.Curve.EcAddSemantics` and `Formal.Secp256k1.EcAddSemantics_secp256k1`,
but with the doubling-case slope `λ·(2·y₁) = 3·x₁² + a = 3·x₁² − 3` for
secp256r1's `a = −3` (vs `3·x₁²` for `a = 0` curves like Grumpkin/k1). -/

/-- **Algebraic group-operation specification (secp256r1).** Same case
structure as `EcAddSemantics_secp256k1`; the doubling slope changes to
`λ · (2·y₁) = 3·x₁² − 3` to reflect `a = −3`. -/
inductive EcAddSemantics_secp256r1 {F : Type*} [Field F] :
    F × F × F → F × F × F → F × F × F → Prop where
  | lhs_inf {x1 y1 x2 y2 is_inf2 : F} :
      EcAddSemantics_secp256r1 (x1, y1, 1) (x2, y2, is_inf2) (x2, y2, is_inf2)
  | rhs_inf {x1 y1 x2 y2 : F} :
      EcAddSemantics_secp256r1 (x1, y1, 0) (x2, y2, 1) (x1, y1, 0)
  | inverse {x1 y1 x2 y2 : F} (_hx : x1 = x2) (_hy : y1 + y2 = 0) :
      EcAddSemantics_secp256r1 (x1, y1, 0) (x2, y2, 0) (0, 0, 1)
  | generic {x1 y1 x2 y2 lambda : F} (_hx : x1 ≠ x2)
      (_hS : lambda * (x2 - x1) = y2 - y1) :
      EcAddSemantics_secp256r1 (x1, y1, 0) (x2, y2, 0)
        (lambda ^ 2 - x1 - x2,
         lambda * (x1 - (lambda ^ 2 - x1 - x2)) - y1,
         0)
  | doubling {x1 y1 lambda : F} (_h2y : (2 : F) * y1 ≠ 0)
      (_hS : lambda * (2 * y1) = 3 * x1 ^ 2 - 3) :
      EcAddSemantics_secp256r1 (x1, y1, 0) (x1, y1, 0)
        (lambda ^ 2 - 2 * x1,
         lambda * (x1 - (lambda ^ 2 - 2 * x1)) - y1,
         0)

/-! ## End-to-end soundness, full 4-way wrapper

Same case-split as the Grumpkin / secp256k1 wrappers; the only differences
are (a) the curve equation `y² = x³ − 3·x + b` (changes the inverse-case
`y² = y²` factoring; still works because `x₁ = x₂` and same RHS), and
(b) the doubling-slope identity passes through `ec_double_on_curve_with_a`
specialised at `a = −3`. -/

/-- **End-to-end soundness — full 4-way wrapper (secp256r1).** Under
`IsValidECAddWitness_secp256r1`, the output triple satisfies
`EcAddSemantics_secp256r1`. -/
theorem ec_add_in_circuit_secp256r1_sound {F : Type*} [Field F]
    (b : F) {x1 y1 is_inf1 x2 y2 is_inf2 lambda
     same_x same_y is_double is_inverse inv_dx inv_dy
     xg yg x3 y3 is_inf3 : F}
    (h : IsValidECAddWitness_secp256r1 b x1 y1 is_inf1 x2 y2 is_inf2 lambda
            same_x same_y is_double is_inverse inv_dx inv_dy
            xg yg x3 y3 is_inf3)
    (h2y : is_inf1 = 0 → is_inf2 = 0 → x1 = x2 → y1 = y2 → (2 : F) * y1 ≠ 0) :
    EcAddSemantics_secp256r1 (x1, y1, is_inf1) (x2, y2, is_inf2) (x3, y3, is_inf3) := by
  classical
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
    · -- both finite.
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
          -- doubling slope: 2·y1·λ = 3·x1² − 3.
          have hSd : lambda * (2 * y1) = 3 * x1 ^ 2 - 3 := by
            have hd := h.slope_double
            rw [hid] at hd
            have : (2 * y1 * lambda - (3 * x1 ^ 2 - 3)) = 0 := by linear_combination hd
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
          exact EcAddSemantics_secp256r1.doubling h2y' hSd
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
          have hC1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + b :=
            gated_on_curve_secp256r1_sound b x1 y1 0 h.on_curve1 rfl
          have hC2 : y2 ^ 2 = x2 ^ 3 - 3 * x2 + b :=
            gated_on_curve_secp256r1_sound b x2 y2 0 h.on_curve2 rfl
          have hyy : y1 ^ 2 = y2 ^ 2 := by
            rw [hC1, hC2, hxeq]
          have hfact : (y1 - y2) * (y1 + y2) = 0 := by linear_combination hyy
          have hyne : y1 - y2 ≠ 0 := sub_ne_zero.mpr hyeq
          have hysum : y1 + y2 = 0 := (mul_eq_zero.mp hfact).resolve_left hyne
          exact EcAddSemantics_secp256r1.inverse hxeq hysum
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
        exact EcAddSemantics_secp256r1.generic hxeq hS
    · -- rhs_inf branch.
      subst hi1; subst hi2
      obtain ⟨hx3, hy3, hi3⟩ := output_mux_rhs_inf h.mux
      rw [hx3, hy3, hi3]
      exact EcAddSemantics_secp256r1.rhs_inf
  · -- lhs_inf branch.
    subst hi1
    obtain ⟨hx3, hy3, hi3⟩ := output_mux_lhs_inf h.mux
    rw [hx3, hy3, hi3]
    exact EcAddSemantics_secp256r1.lhs_inf

/-- **secp256r1 (P-256) incomplete-affine addition soundness (base-field level).**
Same flag-free 3-limb `ec_add_incomplete` shape as secp256k1, but over the P-256
curve `y² = x³ − 3·x + b` (`a = −3`). The gadget enforces `dxinv·(x2−x1) = 1`,
`λ·(x2−x1) = y2−y1`, `x3 = λ²−x1−x2`, `y3 = λ·(x1−x3)−y1`; given both inputs on the
curve, the output is on the curve and the slope is unique. Proved from the generic
`Curve` algebra at `a = −3` (the `−3·x` term flows through unchanged). -/
theorem ec_add_incomplete_secp256r1_sound {F : Type*} [Field F] (b : F)
    (x1 y1 x2 y2 x3 y3 lam dxinv : F)
    (hdx : dxinv * (x2 - x1) = 1)
    (hE1 : y1 ^ 2 = x1 ^ 3 + (-3) * x1 + b) (hE2 : y2 ^ 2 = x2 ^ 3 + (-3) * x2 + b)
    (hS : lam * (x2 - x1) = y2 - y1)
    (hx3 : x3 = lam ^ 2 - x1 - x2) (hy3 : y3 = lam * (x1 - x3) - y1) :
    y3 ^ 2 = x3 ^ 3 + (-3) * x3 + b ∧ ∀ lam', lam' * (x2 - x1) = y2 - y1 → lam' = lam := by
  have hx : x1 ≠ x2 := by
    intro e
    rw [e, sub_self, mul_zero] at hdx
    exact zero_ne_one hdx
  refine ⟨?_, fun lam' hS' => ec_add_generic_slope_unique x1 y1 x2 y2 lam' lam hx hS' hS⟩
  have hoc := ec_add_generic_on_curve (-3) b x1 y1 x2 y2 lam hx hE1 hE2 hS
  subst hx3
  subst hy3
  linear_combination hoc

end Xark
