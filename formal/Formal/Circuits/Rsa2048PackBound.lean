/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048Packing

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Bounds on a packed limb

`Formal/Circuits/Rsa2048Packing.lean` proves each packed limb equal to
`Σ_t 2^t · bit`; this file turns that into `< 2^82` from the bits' `to_bits`
contract (each bit is 0 or 1). `pack_bound` is the generic argument, keyed by the
normalized-term equality and `eval_normTerms`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template

theorem sum_map_scale (l : List (F × ℕ)) (k : F) (σ : ℕ → F) :
    (l.map fun t => (k * t.1) * σ t.2).sum
      = k * ((l.map fun t => t.1 * σ t.2).sum) := by
  induction l with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_flatMapF (l : List ℕ) (g : ℕ → List (F × ℕ)) (σ : ℕ → F) :
    ((l.flatMap g).map fun t => t.1 * σ t.2).sum
      = (l.map fun a => ((g a).map fun t => t.1 * σ t.2).sum).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, ih, List.sum_append]

theorem sum_rangeF (g : ℕ → F) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem eval_packTerms (off q : ℕ) (σ : ℕ → F) :
    (packGLCAt off q).eval σ
      = ∑ t ∈ Finset.range 82,
          if 82 * q + t < 2048 then
            (↑(2 ^ t) : F)
              * ((bitTerms (off + (255 - (82 * q + t) / 8)) ((82 * q + t) % 8)).map
                  fun term => term.1 * σ term.2).sum
          else 0 := by
  simp only [packGLCAt, packTermsAt, LC.eval, List.sum_nil, zero_add]
  rw [sum_flatMapF, sum_rangeF]
  refine Finset.sum_congr rfl fun t ht => ?_
  by_cases hj : 82 * q + t < 2048
  · simp only [hj, if_pos]
    rw [List.map_map]
    exact sum_map_scale _ _ σ
  · simp only [hj, if_false, List.map_nil, List.sum_nil]

theorem weighted_lt (f : ℕ → F) (hf : ∀ t < 82, (f t).val ≤ 1) :
    (∑ t ∈ Finset.range 82, 2 ^ t * (f t).val) < 2 ^ 82 := by
  have hgeom : (∑ t ∈ Finset.range 82, 2 ^ t : ℕ) = 2 ^ 82 - 1 := by
    have h : ∀ n, (∑ t ∈ Finset.range n, 2 ^ t : ℕ) = 2 ^ n - 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; omega
    exact h 82
  have hle : (∑ t ∈ Finset.range 82, 2 ^ t * (f t).val) ≤ 2 ^ 82 - 1 := by
    calc (∑ t ∈ Finset.range 82, 2 ^ t * (f t).val) ≤ ∑ t ∈ Finset.range 82, 2 ^ t * 1 :=
          Finset.sum_le_sum fun t ht => Nat.mul_le_mul_left _ (hf t (Finset.mem_range.mp ht))
      _ = 2 ^ 82 - 1 := by simpa using hgeom
  have hsub : 2 ^ 82 - 1 < 2 ^ 82 := by
    have h : (0 : ℕ) < 2 ^ 82 := by positivity
    omega
  exact lt_of_le_of_lt hle hsub

theorem val_weighted (f : ℕ → F) (hf : ∀ t < 82, (f t).val ≤ 1) :
    ((∑ t ∈ Finset.range 82, ((2 ^ t : ℕ) : F) * f t).val)
      = ∑ t ∈ Finset.range 82, 2 ^ t * (f t).val := by
  have hcast : (∑ t ∈ Finset.range 82, ((2 ^ t : ℕ) : F) * f t)
      = ((∑ t ∈ Finset.range 82, 2 ^ t * (f t).val : ℕ) : F) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hft : f t = ((f t).val : F) := (ZMod.natCast_zmod_val (f t)).symm
    conv_lhs => rw [hft]
    exact (Nat.cast_mul (m := 2 ^ t) (n := (f t).val)).symm
  rw [hcast, ZMod.val_natCast_of_lt]
  have hlt : (∑ t ∈ Finset.range 82, 2 ^ t * (f t).val) < r := by
    have h : (0 : ℕ) < 2 ^ 82 := by positivity
    exact lt_of_lt_of_le (by omega) (le_of_lt (weighted_lt f hf))
  exact hlt

theorem pack_bound (off q : ℕ) (σ : ℕ → F)
    (hbit : ∀ b tb, ((bitGLC b tb).eval σ).val ≤ 1) :
    ((packGLCAt off q).eval σ).val < 2 ^ 82 := by
  rw [eval_packTerms]
  let f : ℕ → F := fun t =>
    if 82 * q + t < 2048 then (bitGLC (off + (255 - (82 * q + t) / 8)) ((82 * q + t) % 8)).eval σ
    else 0
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * q + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (off + (255 - (82 * q + t) / 8)) ((82 * q + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82, ((2 ^ t : ℕ) : F) * f t := by
    refine Finset.sum_congr rfl fun t ht => ?_
    dsimp [f]
    by_cases h : 82 * q + t < 2048
    · simp only [h, if_pos]
      congr 1
      simp [bitGLC, LC.eval]
    · simp only [h, if_false]
  rw [hsum]
  have hf : ∀ t < 82, (f t).val ≤ 1 := by
    intro t ht
    dsimp [f]
    by_cases h : 82 * q + t < 2048
    · rw [if_pos h]; exact hbit _ _
    · rw [if_neg h]; simp
  rw [val_weighted f hf]
  exact weighted_lt f hf

/-- `bitOf` is a bit. -/
theorem bitOf_val_le (x : F) (t : ℕ) : (Xark.Template.bitOf x t).val ≤ 1 := by
  unfold Xark.Template.bitOf
  split <;> simp

end Xark.Circuits.Rsa2048
