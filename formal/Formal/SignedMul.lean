/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.GrumpkinMul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The rows of `xark_grumpkin::signed_mul`, for any bit count and placement

`scalar_mul` (128 bits) and `wide_scalar_mul` (254 bits) both emit `signed_mul`: the
on-curve rows of `P`, the fused step `(O + P) + O`, the fused steps `(A ± P) + A` for
bits `n − 1, …, 1`, and the two last adds `acc + (bit₀ ? corr : corr − P)`. Their
exported templates differ only in where the rows put things (`Layout`): the bit count,
the offset of the steps' variables, the point's and the bits' variables, and `corr`.
`sound` is proven once, here, over the rows `onCurveRows L ++ smRows L`;
`Formal/ScalarMul.lean` and `Formal/WideScalarMul.lean` check by `decide` that their
templates are these rows and instantiate them.

Step `0` has its own rows (`firstRows`); step `j ≥ 1` owns the variables
`o + 13j + 1, …, o + 13j + 12` (`stepRows`); the accumulator after step `i` is
`x = w(sq2 i) − w(sq1 i) + x_P`, `y = w(yv i)`.
-/

namespace Xark.SignedMul

open Xark.Template Xark.GrumpkinMul WeierstrassCurve.Affine Xark.R1cs Xark.DoubleAdd

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

def v1 (x : TVar) : LC := ⟨0, [(1, x)]⟩

/-- `LC.eval` on a literal: unlike unfolding `LC.eval`, it leaves a bit's
`(L.bit i).eval σ` alone. -/
theorem eval_mk (c : F) (ts : List (F × TVar)) (σ : TVar → F) :
    LC.eval ⟨c, ts⟩ σ = c + (ts.map fun t => t.1 * σ t.2).sum := rfl

/-- `2·b − 1`, the signed digit of bit `b`, as the frontend writes it. -/
def digit (b : LC) : LC := ⟨2 * b.const - 1, b.terms.map fun t => (2 * t.1, t.2)⟩

theorem eval_digit (b : LC) (σ : TVar → F) : (digit b).eval σ = 2 * b.eval σ - 1 := by
  simp only [digit, LC.eval, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]
  ring

/-- Where a `signed_mul` call's rows put things. -/
structure Layout where
  /-- The number of bits. -/
  n : ℕ
  /-- The offset of the fused steps' variables. -/
  o : ℕ
  /-- `P`'s coordinates. -/
  x : TVar
  y : TVar
  /-- Bit `i`, little-endian: a variable (`v1 t`), or the linear form a `to_bits`
  leaves for its bit `0` (`x − Σ 2ⁱ·bᵢ`). -/
  bit : ℕ → LC
  /-- `corr = −(2ⁿ·O)`. -/
  cX : F
  cY : F

variable (L : Layout)

/-! ### The rows -/

def sq1 (i : ℕ) : ℕ := if i = 0 then L.o + 6 else L.o + (13 * i + 5)
def sq2 (i : ℕ) : ℕ := L.o + (13 * i + 9)
def yv (i : ℕ) : ℕ := L.o + (13 * i + 12)

def onCurveRows : List Row :=
  [⟨v1 L.y, v1 L.y, ⟨-17, [(1, .wit 2)]⟩⟩, ⟨v1 L.x, v1 L.x, v1 (.wit 1)⟩,
    ⟨v1 (.wit 1), v1 L.x, v1 (.wit 2)⟩]

def l2First : LC := ⟨0, [(-1, .wit (L.o + 5)), (2 * oY, .wit (L.o + 7))]⟩

/-- Step `0`: `(O + P) + O`. -/
def firstRows : List Row :=
  [⟨⟨5, [(-1, L.x)]⟩, v1 (.wit (L.o + 3)), ⟨1, []⟩⟩,
    ⟨⟨oY, [(-1, L.y)]⟩, v1 (.wit (L.o + 3)), v1 (.wit (L.o + 5))⟩,
    ⟨v1 (.wit (L.o + 5)), v1 (.wit (L.o + 5)), v1 (.wit (L.o + 6))⟩,
    ⟨⟨0, [(2 * oY, .wit (L.o + 7))]⟩, ⟨10, [(1, L.x), (-1, .wit (L.o + 6))]⟩, ⟨2 * oY, []⟩⟩,
    ⟨l2First L, l2First L, v1 (.wit (L.o + 9))⟩,
    ⟨l2First L, ⟨5, [(-1, L.x), (1, .wit (L.o + 6)), (-1, .wit (L.o + 9))]⟩,
      ⟨oY, [(1, .wit (L.o + 12))]⟩⟩]

def l2Step (j : ℕ) : LC := ⟨0, [(-1, .wit (L.o + (13 * j + 4))), (1, .wit (L.o + (13 * j + 7)))]⟩

/-- Step `j ≥ 1`: `(A ± P) + A` with the digit of bit `n − j`. -/
def stepRows (j : ℕ) : List Row :=
  let b := 13 * j
  let p1 : TVar := .wit (sq1 L (j - 1))
  let p2 : TVar := .wit (sq2 L (j - 1))
  let py : TVar := .wit (yv L (j - 1))
  [⟨(digit (L.bit (L.n - j))), v1 L.y, v1 (.wit (L.o + (b + 1)))⟩,
    ⟨⟨0, [(-1, p1), (1, p2)]⟩, v1 (.wit (L.o + (b + 2))), ⟨1, []⟩⟩,
    ⟨⟨0, [(1, py), (-1, .wit (L.o + (b + 1)))]⟩, v1 (.wit (L.o + (b + 2))),
      v1 (.wit (L.o + (b + 4)))⟩,
    ⟨v1 (.wit (L.o + (b + 4))), v1 (.wit (L.o + (b + 4))), v1 (.wit (L.o + (b + 5)))⟩,
    ⟨v1 (.wit (L.o + (b + 7))), ⟨0, [(3, L.x), (-2, p1), (2, p2), (-1, .wit (L.o + (b + 5)))]⟩,
      ⟨0, [(2, py)]⟩⟩,
    ⟨l2Step L j, l2Step L j, v1 (.wit (L.o + (b + 9)))⟩,
    ⟨l2Step L j, ⟨0, [(-1, p1), (1, p2), (1, .wit (L.o + (b + 5))), (-1, .wit (L.o + (b + 9)))]⟩,
      ⟨0, [(1, py), (1, .wit (L.o + (b + 12)))]⟩⟩]

/-- The last two adds' variables, `o + 13n + k`. -/
def fw (k : ℕ) : TVar := .wit (L.o + (13 * L.n + k))

def lam2 : LC := ⟨2 * L.cX, [(1, L.x), (-1, fw L 4)]⟩

/-- `q = bit₀ ? corr : corr − P` and `acc + q`. -/
def finalRows : List Row :=
  let p1 : TVar := .wit (sq1 L (L.n - 1))
  let p2 : TVar := .wit (sq2 L (L.n - 1))
  let py : TVar := .wit (yv L (L.n - 1))
  [⟨⟨-L.cX, [(1, L.x)]⟩, v1 (fw L 1), ⟨1, []⟩⟩,
    ⟨⟨-L.cY, [(-1, L.y)]⟩, v1 (fw L 1), v1 (fw L 3)⟩,
    ⟨v1 (fw L 3), v1 (fw L 3), v1 (fw L 4)⟩,
    ⟨v1 (fw L 3), lam2 L, v1 (fw L 5)⟩,
    ⟨L.bit 0, lam2 L, v1 (fw L 6)⟩,
    ⟨L.bit 0, ⟨2 * L.cY, [(-1, fw L 5)]⟩, v1 (fw L 7)⟩,
    ⟨⟨-L.cX, [(-2, L.x), (1, p1), (-1, p2), (1, fw L 4), (1, fw L 6)]⟩, v1 (fw L 8), ⟨1, []⟩⟩,
    ⟨⟨-L.cY, [(-1, py), (1, fw L 5), (1, fw L 7)]⟩, v1 (fw L 8), v1 (fw L 10)⟩,
    ⟨v1 (fw L 10), v1 (fw L 10), v1 (fw L 11)⟩,
    ⟨v1 (fw L 10), ⟨-L.cX, [(1, L.x), (-2, p1), (2, p2), (1, fw L 4), (1, fw L 6), (-1, fw L 11)]⟩,
      v1 (fw L 12)⟩]

/-- The rows after the on-curve check. -/
def smRows : List Row :=
  firstRows L ++ (List.range (L.n - 1)).flatMap (fun i => stepRows L (i + 1)) ++ finalRows L

/-- The output's coordinates. -/
def outX (σ : TVar → F) : F :=
  L.cX + σ (.wit (sq1 L (L.n - 1))) - σ (.wit (sq2 L (L.n - 1))) - σ (fw L 4) - σ (fw L 6) +
    σ (fw L 11)

def outY (σ : TVar → F) : F := -σ (.wit (yv L (L.n - 1))) + σ (fw L 12)

/-- The scalar the bits spell. -/
def scalar (σ : TVar → F) : ℕ := ∑ i ∈ Finset.range L.n, 2 ^ i * ((L.bit i).eval σ).val

/-! ### The rows' meaning -/

theorem mem_first {r : Row} (h : r ∈ firstRows L) : r ∈ smRows L := by
  simp only [smRows, List.mem_append]; exact Or.inl (Or.inl h)

theorem mem_step {j : ℕ} (hj : j < L.n - 1) {r : Row} (h : r ∈ stepRows L (j + 1)) :
    r ∈ smRows L := by
  simp only [smRows, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inr ⟨j, hj, h⟩)

theorem mem_final {r : Row} (h : r ∈ finalRows L) : r ∈ smRows L := by
  simp only [smRows, List.mem_append]; exact Or.inr h

/-- The accumulator after `k` steps. -/
def xA (σ : TVar → F) : ℕ → F
  | 0 => oX
  | k + 1 => σ (.wit (sq2 L k)) - σ (.wit (sq1 L k)) + σ L.x

def yA (σ : TVar → F) : ℕ → F
  | 0 => oY
  | k + 1 => σ (.wit (yv L k))

/-- Step `k`'s addend: `P` at step `0`, then `(x_P, (2·bit − 1)·y_P)`. -/
def yS (σ : TVar → F) : ℕ → F
  | 0 => σ L.y
  | k + 1 => σ (.wit (L.o + (13 * (k + 1) + 1)))

theorem sq1_succ (j : ℕ) : sq1 L (j + 1) = L.o + (13 * (j + 1) + 5) := by simp [sq1]
theorem sq1_zero : sq1 L 0 = L.o + 6 := by simp [sq1]
theorem sq2_zero : sq2 L 0 = L.o + 9 := by simp [sq2]
theorem yv_zero : yv L 0 = L.o + 12 := by simp [yv]

theorem xA_n (σ : TVar → F) (hn : 1 ≤ L.n) :
    xA L σ L.n = σ (.wit (sq2 L (L.n - 1))) - σ (.wit (sq1 L (L.n - 1))) + σ L.x := by
  conv_lhs => rw [show L.n = L.n - 1 + 1 by omega]
  rfl

theorem yA_n (σ : TVar → F) (hn : 1 ≤ L.n) : yA L σ L.n = σ (.wit (yv L (L.n - 1))) := by
  conv_lhs => rw [show L.n = L.n - 1 + 1 by omega]
  rfl

/-- Every step's rows are the fused step's equations. -/
theorem step_eqs {σ : TVar → F} (h : ∀ r ∈ smRows L, r.Sat σ) (k : ℕ) (hk : k < L.n) :
    StepEqs (xA L σ k) (yA L σ k) (σ L.x) (yS L σ k) (xA L σ (k + 1)) (yA L σ (k + 1)) := by
  cases k with
  | zero =>
    have row := fun i (hi : i < (firstRows L).length) => h _ (mem_first L (List.getElem_mem hi))
    have r1 := row 0 (by simp [firstRows])
    have r2 := row 1 (by simp [firstRows])
    have r3 := row 2 (by simp [firstRows])
    have r4 := row 3 (by simp [firstRows])
    have r5 := row 4 (by simp [firstRows])
    have r6 := row 5 (by simp [firstRows])
    simp only [firstRows, l2First, v1, Row.Sat, eval_mk, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.getElem_cons_zero,
      List.getElem_cons_succ] at r1 r2 r3 r4 r5 r6
    refine ⟨σ (.wit (L.o + 3)), σ (.wit (L.o + 5)), 2 * oY * σ (.wit (L.o + 7)) - σ (.wit (L.o + 5)),
      σ (.wit (L.o + 6)) - oX - σ L.x, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [xA, oX]; linear_combination r1
    · simp only [yA, yS]; linear_combination r2
    · simp only [xA]; linear_combination -r3
    · simp only [xA, yA, oX]; linear_combination r4
    · simp only [xA, sq1_zero, sq2_zero, oX]; linear_combination -r5
    · simp only [xA, yA, sq1_zero, sq2_zero, yv_zero, oX]; linear_combination r6
  | succ j =>
    have hj : j < L.n - 1 := by omega
    have row := fun i (hi : i < (stepRows L (j + 1)).length) =>
      h _ (mem_step L hj (List.getElem_mem hi))
    have r2 := row 1 (by simp [stepRows])
    have r3 := row 2 (by simp [stepRows])
    have r4 := row 3 (by simp [stepRows])
    have r5 := row 4 (by simp [stepRows])
    have r6 := row 5 (by simp [stepRows])
    have r7 := row 6 (by simp [stepRows])
    simp only [stepRows, l2Step, v1, Row.Sat, eval_mk, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.add_sub_cancel] at r2 r3 r4 r5 r6 r7
    refine ⟨σ (.wit (L.o + (13 * (j + 1) + 2))), σ (.wit (L.o + (13 * (j + 1) + 4))),
      σ (.wit (L.o + (13 * (j + 1) + 7))) - σ (.wit (L.o + (13 * (j + 1) + 4))),
      σ (.wit (L.o + (13 * (j + 1) + 5))) - xA L σ (j + 1) - σ L.x, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [xA]; linear_combination r2
    · simp only [yA, yS]; linear_combination r3
    · linear_combination -r4
    · simp only [xA, yA]; linear_combination r5
    · simp only [xA, sq1_succ, sq2]; linear_combination -r6
    · simp only [xA, yA, sq1_succ, sq2, yv] at r7 ⊢; linear_combination r7

/-! ### Points -/

theorem exists_some {x y x' y' : F} (h' : grumpkinCurve.Nonsingular x' y') (hx : x = x')
    (hy : y = y') : ∃ h : grumpkinCurve.Nonsingular x y,
      (Point.some _ _ h : GrumpkinPoint) = Point.some _ _ h' := by
  subst hx hy; exact ⟨h', rfl⟩

/-- `−(x, y) = (x, −y)`. -/
theorem neg_some {x y : F} (h : grumpkinCurve.Nonsingular x y)
    (h' : grumpkinCurve.Nonsingular x (-y)) :
    -(Point.some _ _ h : GrumpkinPoint) = Point.some _ _ h' := by
  rw [Point.neg_some, Point.some.injEq]
  simp [negY, grumpkinCurve]

theorem neg_ns {x y : F} (h : grumpkinCurve.Nonsingular x y) :
    grumpkinCurve.Nonsingular x (-y) :=
  Grumpkin.nonsingular_iff.mpr (by linear_combination Grumpkin.nonsingular_iff.mp h)

/-- The signed addends: `P`, then `±P` for bit `n − j`. -/
noncomputable def addend (n : ℕ) (P : GrumpkinPoint) (b : ℕ → ℕ) (j : ℕ) : GrumpkinPoint :=
  if j = 0 then P else if b (n - j) = 1 then P else -P

/-- Step `k + 1`'s addend `(x_P, (2·c − 1)·y_P)`, `c` the bit `n − (k + 1)`, is `±P`. -/
theorem addend_some {xp yp ys c : F} (hP : grumpkinCurve.Nonsingular xp yp) (hc : IsBit c)
    {n k : ℕ} {b : ℕ → ℕ} (hbc : c.val = b (n - (k + 1)))
    (hy : ys = (2 * c - 1) * yp) :
    ∃ h : grumpkinCurve.Nonsingular xp ys,
      Point.some _ _ h = addend n (Point.some _ _ hP) b (k + 1) := by
  rw [addend, if_neg (Nat.succ_ne_zero k)]
  rcases hc with hc | hc
  · rw [if_neg (by rw [← hbc, hc]; simp), neg_some hP (neg_ns hP)]
    exact exists_some (neg_ns hP) rfl (by rw [hy, hc]; ring)
  · rw [if_pos (by rw [← hbc, hc]; simp [ZMod.val_one])]
    exact exists_some hP rfl (by rw [hy, hc]; ring)

/-- `q = bit₀ ? corr : corr − P`, from its rows. -/
theorem q_point {σ : TVar → F} (hC : grumpkinCurve.Nonsingular L.cX L.cY)
    (hP : grumpkinCurve.Nonsingular (σ L.x) (σ L.y)) (hb0 : IsBit ((L.bit 0).eval σ))
    (g0 : (-L.cX + σ L.x) * σ (fw L 1) = 1)
    (f1 : (-L.cY - σ L.y) * σ (fw L 1) = σ (fw L 3))
    (f2 : σ (fw L 3) * σ (fw L 3) = σ (fw L 4))
    (f3 : σ (fw L 3) * (2 * L.cX + σ L.x - σ (fw L 4)) = σ (fw L 5))
    (f4 : (L.bit 0).eval σ * (2 * L.cX + σ L.x - σ (fw L 4)) = σ (fw L 6))
    (f5 : (L.bit 0).eval σ * (2 * L.cY - σ (fw L 5)) = σ (fw L 7)) :
    ∃ hq : grumpkinCurve.Nonsingular (σ (fw L 4) - L.cX - σ L.x + σ (fw L 6))
      (σ (fw L 5) - L.cY + σ (fw L 7)), (Point.some _ _ hq : GrumpkinPoint) =
        if ((L.bit 0).eval σ).val = 1 then Point.some _ _ hC
          else Point.some _ _ hC + -Point.some _ _ hP := by
  have hx : L.cX ≠ σ L.x := by
    intro e; rw [e, neg_add_cancel, zero_mul] at g0; exact zero_ne_one g0
  obtain ⟨h3, e3⟩ := add_of_slope (x₃ := σ (fw L 4) - L.cX - σ L.x)
    (y₃ := σ (fw L 5) - L.cY) (l := σ (fw L 3)) short hC (neg_ns hP) hx
    (by linear_combination (-(L.cX - σ L.x)) * f1 + (L.cY + σ L.y) * g0)
    (by linear_combination -f2) (by linear_combination -f3)
  rcases hb0 with hb | hb
  · rw [hb] at f4 f5
    rw [if_neg (by simp [hb]), neg_some hP (neg_ns hP), e3]
    exact exists_some h3 (by linear_combination -f4) (by linear_combination -f5)
  · rw [hb] at f4 f5
    rw [if_pos (by simp [hb, ZMod.val_one])]
    exact exists_some hC (by linear_combination -f4) (by linear_combination -f5)

/-! ### Soundness -/

/-- The last two adds: the output is `acc + q`. -/
theorem final_sound (hn : 1 ≤ L.n) (hC : grumpkinCurve.Nonsingular L.cX L.cY) {σ : TVar → F}
    (h : ∀ r ∈ smRows L, r.Sat σ)
    (hP : grumpkinCurve.Nonsingular (σ L.x) (σ L.y)) (hb0 : IsBit ((L.bit 0).eval σ))
    (hA : grumpkinCurve.Nonsingular (xA L σ L.n) (yA L σ L.n)) :
    ∃ hR : grumpkinCurve.Nonsingular (outX L σ) (outY L σ),
      (Point.some _ _ hR : GrumpkinPoint) = Point.some _ _ hA +
        (if ((L.bit 0).eval σ).val = 1 then Point.some _ _ hC
          else Point.some _ _ hC + -Point.some _ _ hP) := by
  have row := fun i (hi : i < (finalRows L).length) => h _ (mem_final L (List.getElem_mem hi))
  have f0 := row 0 (by simp [finalRows])
  have f1 := row 1 (by simp [finalRows])
  have f2 := row 2 (by simp [finalRows])
  have f3 := row 3 (by simp [finalRows])
  have f4 := row 4 (by simp [finalRows])
  have f5 := row 5 (by simp [finalRows])
  have f6 := row 6 (by simp [finalRows])
  have f7 := row 7 (by simp [finalRows])
  have f8 := row 8 (by simp [finalRows])
  have f9 := row 9 (by simp [finalRows])
  simp only [finalRows, lam2, v1, Row.Sat, eval_mk, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.getElem_cons_zero,
    List.getElem_cons_succ] at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
  obtain ⟨hq, eq⟩ := q_point L hC hP hb0 (by linear_combination f0) (by linear_combination f1)
    (by linear_combination f2) (by linear_combination f3) (by linear_combination f4)
    (by linear_combination f5)
  rw [← eq]
  have hxA := xA_n L σ hn
  have hyA := yA_n L σ hn
  have g6 : (σ (fw L 4) - L.cX - σ L.x + σ (fw L 6) - xA L σ L.n) * σ (fw L 8) = 1 := by
    rw [hxA]; linear_combination f6
  have hx' : xA L σ L.n ≠ σ (fw L 4) - L.cX - σ L.x + σ (fw L 6) := by
    intro e; rw [e, sub_self, zero_mul] at g6; exact zero_ne_one g6
  obtain ⟨hR, eR⟩ := add_of_slope (x₃ := outX L σ) (y₃ := outY L σ) (l := σ (fw L 10)) short hA hq
    hx'
    (by
      rw [hxA, hyA]
      linear_combination
        (σ (fw L 4) - L.cX - σ L.x + σ (fw L 6) -
          (σ (.wit (sq2 L (L.n - 1))) - σ (.wit (sq1 L (L.n - 1))) + σ L.x)) * f7 -
          (σ (fw L 5) - L.cY + σ (fw L 7) - σ (.wit (yv L (L.n - 1)))) * f6)
    (by rw [hxA, outX]; linear_combination -f8)
    (by rw [hxA, hyA, outX, outY]; linear_combination -f9)
  exact ⟨hR, eR.symm⟩

/-- **Soundness of `signed_mul`'s rows.** On bits, rows that hold make `P` a point of
Grumpkin and the output the affine point `s·P`, `s` the scalar of the bits. -/
theorem sound (hn : 1 ≤ L.n) (hC : grumpkinCurve.Nonsingular L.cX L.cY)
    (hCeq : (Point.some _ _ hC : GrumpkinPoint) = -((2 ^ L.n) • O)) {σ : TVar → F}
    (hon : ∀ r ∈ onCurveRows L, r.Sat σ) (h : ∀ r ∈ smRows L, r.Sat σ)
    (hbit : ∀ i < L.n, IsBit ((L.bit i).eval σ)) :
    ∃ (hP : grumpkinCurve.Nonsingular (σ L.x) (σ L.y))
      (hR : grumpkinCurve.Nonsingular (outX L σ) (outY L σ)),
      (Point.some _ _ hR : GrumpkinPoint) = scalar L σ • Point.some _ _ hP := by
  -- `P` is on the curve.
  have hP : grumpkinCurve.Nonsingular (σ L.x) (σ L.y) := by
    have row := fun i (hi : i < (onCurveRows L).length) => hon _ (List.getElem_mem hi)
    have r0 := row 0 (by simp [onCurveRows])
    have r1 := row 1 (by simp [onCurveRows])
    have r2 := row 2 (by simp [onCurveRows])
    simp only [onCurveRows, v1, Row.Sat, eval_mk, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.getElem_cons_zero, List.getElem_cons_succ] at r0 r1 r2
    exact Grumpkin.nonsingular_iff.mpr (by linear_combination r0 - r2 - σ L.x * r1)
  let bv : ℕ → ℕ := fun i => ((L.bit i).eval σ).val
  have hb : ∀ i < L.n, bv i ≤ 1 := fun i hi => by
    rcases hbit i hi with e | e <;> simp [bv, e, ZMod.val_one]
  -- Each step's addend is `±P`.
  have hS : ∀ j < L.n, ∃ h : grumpkinCurve.Nonsingular (σ L.x) (yS L σ j),
      Point.some _ _ h = addend L.n (Point.some _ _ hP) bv j := by
    intro j hj
    cases j with
    | zero => exact ⟨hP, by rw [addend, if_pos rfl]; try rfl⟩
    | succ k =>
      have r0 := h _ (mem_step L (j := k) (by omega)
        (List.getElem_mem (l := stepRows L (k + 1)) (n := 0) (by simp [stepRows])))
      simp only [stepRows, v1, Row.Sat, eval_mk, eval_digit, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.getElem_cons_zero] at r0
      exact addend_some hP (hbit _ (by omega)) rfl (by simp only [yS]; linear_combination -r0)
  -- The chain of fused steps.
  have h0 : grumpkinCurve.Nonsingular (xA L σ 0) (yA L σ 0) := oNs
  obtain ⟨hA, hAeq⟩ := DoubleAdd.chain_sound short (xS := fun _ => σ L.x) (yS := yS L σ)
    (S := addend L.n (Point.some _ _ hP) bv) L.n h0 hS (fun j hj => step_eqs L h j hj)
  set s := ∑ i ∈ Finset.range L.n, 2 ^ i * bv i with hs
  have hacc := accum_digits O (Point.some _ _ hP) L.n bv hb s hs (addend L.n _ bv)
    (by rw [addend, if_pos rfl]) (fun j hj1 _ => by rw [addend, if_neg (by omega)])
    L.n hn le_rfl
  rw [show L.n + 1 - L.n = 1 by omega, pow_one] at hacc
  rw [show (Point.some _ _ h0 : GrumpkinPoint) = O from rfl, hacc] at hAeq
  -- The last adds.
  obtain ⟨hR, hReq⟩ := final_sound L hn hC h hP (hbit 0 (by omega)) hA
  have hmod : s % 2 = ((L.bit 0).eval σ).val := by
    have := word_div_mod bv L.n hb 0 (by omega)
    simpa [← hs] using this
  rw [hAeq, ← hmod, final_eq O _ _ L.n s hCeq] at hReq
  exact ⟨hP, hR, hReq⟩

end Xark.SignedMul
