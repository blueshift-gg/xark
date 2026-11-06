/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option linter.style.header false

/-!
# The fused incomplete double-and-add step `(A + S) + A`

`xark_grumpkin::dbl_add` (the step of `scalar_mul`, `wide_scalar_mul` and
`multi_scalar_mul`) computes `(A + S) + A` without materialising `R = A + S`'s `y`
(Orchard's `DoubleAndAdd`, halo2 book `var-base-scalar-mul.md`; arkworks
`double_and_add_unchecked`). Its rows, over the base field:

```text
  (x_A − x_S)·w = 1                  (x_A − x_S) is invertible: A ≠ ±S
  (y_A − y_S)·w = λ1                 λ1 = slope(A, S)
  (λ1 + λ2)·(x_A − x_R) = 2·y_A      x_R = λ1² − x_A − x_S
  λ2·(x_A − x') = y_A + y'           x' = λ2² − x_R − x_A
```

These lemmas are about any short Weierstrass curve `y² = x³ + a₄x + a₆`
(`a₁ = a₂ = a₃ = 0`) over a field where `2 ≠ 0` and no affine point has `y = 0` (no
2-torsion), so they serve Grumpkin here and a non-native curve (secp256k1) later.

* `dblAdd_sound`: rows that hold force `(x', y')` to be the affine point `(A + S) + A`.
  The third row cannot hold at `x_A = x_R`: it would make `y_A = 0`. So it needs no guard
  of its own.
-/

namespace Xark.DoubleAdd

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- A short Weierstrass curve `y² = x³ + a₄x + a₆` with no affine point of order 2 over a
field of characteristic `≠ 2`: the setting of the fused step. -/
structure Short (W : WeierstrassCurve.Affine F) : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0
  two : (2 : F) ≠ 0
  noTwoTorsion : ∀ x, ¬W.Equation x 0

/-- The sum of two affine points with distinct `x`, through a slope `l` the caller has
pinned by `l·(x₁ − x₂) = y₁ − y₂`, is the affine point `(x₃, y₃)` of the chord rule. -/
theorem add_of_slope (hW : Short W) {x₁ y₁ x₂ y₂ l x₃ y₃ : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hx₃ : x₃ = l ^ 2 - x₁ - x₂) (hy₃ : y₃ = l * (x₁ - x₃) - y₁) :
    ∃ h : W.Nonsingular x₃ y₃, Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some _ _ h := by
  have hs : W.slope x₁ x₂ y₁ y₂ = l := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx), hl]
  have e₁ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₃ := by
    rw [hs, hx₃]; simp [addX, hW.a₁, hW.a₂]
  have e₂ : W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂) = y₃ := by
    rw [hs, hy₃, hx₃]; simp only [addY, negY, negAddY, addX, hW.a₁, hW.a₂, hW.a₃]; ring
  have h := nonsingular_add h₁ h₂ fun hxy => hx hxy.1
  rw [e₁, e₂] at h
  refine ⟨h, ?_⟩
  rw [Point.add_of_X_ne hx, Point.some.injEq]
  exact ⟨e₁, e₂⟩

/-- The double of an affine point with `y ≠ 0`, through a tangent slope `l` pinned by
`l·2y = 3x² + a₄`, is the affine point `(x₃, y₃)` of the tangent rule. -/
theorem double_of_slope (hW : Short W) {x y l x₃ y₃ : F} (h : W.Nonsingular x y)
    (hy : y ≠ 0) (hl : l * (2 * y) = 3 * x ^ 2 + W.a₄)
    (hx₃ : x₃ = l ^ 2 - 2 * x) (hy₃ : y₃ = l * (x - x₃) - y) :
    ∃ h' : W.Nonsingular x₃ y₃, Point.some _ _ h + Point.some _ _ h = Point.some _ _ h' := by
  have hneg : W.negY x y = -y := by simp [negY, hW.a₁, hW.a₃]
  have h2y : 2 * y ≠ 0 := mul_ne_zero hW.two hy
  have hy' : y ≠ W.negY x y := by
    rw [hneg]; intro e; apply h2y; linear_combination e
  have hs : W.slope x x y y = l := by
    rw [slope_of_Y_ne rfl hy', hneg, hW.a₁, hW.a₂, eq_comm, eq_div_iff (by
      rw [sub_neg_eq_add, ← two_mul]; exact h2y)]
    linear_combination hl
  have e₁ : W.addX x x (W.slope x x y y) = x₃ := by
    rw [hs, hx₃]; simp [addX, hW.a₁, hW.a₂]; ring
  have e₂ : W.addY x x y (W.slope x x y y) = y₃ := by
    rw [hs, hy₃, hx₃]; simp only [addY, negY, negAddY, addX, hW.a₁, hW.a₂, hW.a₃]; ring
  have h' := nonsingular_add h h fun hxy => hy' hxy.2
  rw [e₁, e₂] at h'
  refine ⟨h', ?_⟩
  rw [Point.add_self_of_Y_ne hy', Point.some.injEq]
  exact ⟨e₁, e₂⟩

omit [DecidableEq F] in
/-- An affine point's `y` is nonzero. -/
theorem y_ne_zero (hW : Short W) {x y : F} (h : W.Nonsingular x y) : y ≠ 0 := by
  rintro rfl
  exact hW.noTwoTorsion x h.1

/-- **Soundness of the fused step.** If its rows hold for an affine `A` and `S`, then
`(x', y')` is an affine point and it is `(A + S) + A`. -/
theorem dblAdd_sound (hW : Short W) {xA yA xS yS w l1 l2 xR x' y' : F}
    (hA : W.Nonsingular xA yA) (hS : W.Nonsingular xS yS)
    (guard : (xA - xS) * w = 1) (hl1 : (yA - yS) * w = l1)
    (hxR : xR = l1 ^ 2 - xA - xS) (hl2 : (l1 + l2) * (xA - xR) = 2 * yA)
    (hx' : x' = l2 ^ 2 - xR - xA) (hy' : l2 * (xA - x') = yA + y') :
    ∃ h : W.Nonsingular x' y',
      Point.some _ _ h = Point.some _ _ hA + Point.some _ _ hS + Point.some _ _ hA := by
  have hxS : xA ≠ xS := by
    intro h; rw [h, sub_self, zero_mul] at guard; exact zero_ne_one guard
  have hs1 : l1 * (xA - xS) = yA - yS := by
    rw [← hl1, mul_assoc, mul_comm w, guard, mul_one]
  obtain ⟨hR, hAS⟩ := add_of_slope (y₃ := l1 * (xA - xR) - yA) hW hA hS hxS hs1 hxR rfl
  have hxR' : xR ≠ xA := by
    intro h
    rw [h, sub_self, mul_zero] at hl2
    rcases mul_eq_zero.mp hl2.symm with h2 | h2
    · exact hW.two h2
    · exact y_ne_zero hW hA h2
  have hs2 : l2 * (xR - xA) = l1 * (xA - xR) - yA - yA := by linear_combination -hl2
  obtain ⟨h', hRA⟩ := add_of_slope (y₃ := y') hW hR hA hxR' hs2 hx' (by
    linear_combination -hy' + hl2)
  exact ⟨h', by rw [hAS, hRA]⟩

/-! ### A chain of fused steps -/

/-- The six equations of one fused step from `(x_A, y_A)` with addend `(x_S, y_S)` to
`(x', y')`, with its hints `w, λ1, λ2` and `x_R` existentially quantified. -/
def StepEqs (xA yA xS yS x' y' : F) : Prop :=
  ∃ w l1 l2 xR : F, (xA - xS) * w = 1 ∧ (yA - yS) * w = l1 ∧ xR = l1 ^ 2 - xA - xS ∧
    (l1 + l2) * (xA - xR) = 2 * yA ∧ x' = l2 ^ 2 - xR - xA ∧ l2 * (xA - x') = yA + y'

/-- The accumulator after `j` fused steps from `A` with addends `S 0, S 1, …`. -/
def accum {G : Type*} [Add G] (A : G) (S : ℕ → G) : ℕ → G
  | 0 => A
  | j + 1 => accum A S j + S j + accum A S j

/-- **Soundness of a chain of fused steps.** If step `j` holds from accumulator `j` with
addend `S j` (an affine point) to accumulator `j + 1`, for every `j < n`, then accumulator
`n` is the affine point `accum A S n`. -/
theorem chain_sound (hW : Short W) {xA yA xS yS : ℕ → F} {S : ℕ → W.Point} (n : ℕ)
    (h0 : W.Nonsingular (xA 0) (yA 0))
    (hS : ∀ j < n, ∃ h : W.Nonsingular (xS j) (yS j), Point.some _ _ h = S j)
    (hstep : ∀ j < n, StepEqs (xA j) (yA j) (xS j) (yS j) (xA (j + 1)) (yA (j + 1))) :
    ∃ h : W.Nonsingular (xA n) (yA n), Point.some _ _ h = accum (Point.some _ _ h0) S n := by
  induction n with
  | zero => exact ⟨h0, rfl⟩
  | succ n ih =>
    obtain ⟨hA, hA'⟩ := ih (fun j hj => hS j (by omega)) fun j hj => hstep j (by omega)
    obtain ⟨hSn, hSn'⟩ := hS n (by omega)
    obtain ⟨w, l1, l2, xR, e1, e2, e3, e4, e5, e6⟩ := hstep n (by omega)
    obtain ⟨h, e⟩ := dblAdd_sound hW hA hSn e1 e2 e3 e4 e5 e6
    exact ⟨h, by rw [e, hA', hSn', accum]⟩

end Xark.DoubleAdd
