/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.Packing

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
  have hlt : (∑ t ∈ Finset.range 82, 2 ^ t * (f t).val) < r :=
    lt_trans (weighted_lt f hf) (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num))
  rw [hcast, ZMod.val_natCast_of_lt hlt]

theorem pack_bound (off q : ℕ) (hoff : off ≤ 288) (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
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
    · simp only [h, if_pos, bitGLC, LC.eval, zero_add, Nat.cast_pow, Nat.cast_ofNat]
    · simp only [h, if_false, mul_zero]
  rw [hsum]
  have hf : ∀ t < 82, (f t).val ≤ 1 := by
    intro t ht
    dsimp [f]
    by_cases h : 82 * q + t < 2048
    · rw [if_pos h]
      exact hbit _ _ (by omega) (by omega)
    · rw [if_neg h]; simp
  rw [val_weighted f hf]
  exact weighted_lt f hf

/-- The packed limb in canonical form, so the exported plug is compared by `decide`
rather than by normalizing the huge plug term inside a rewrite. -/
def packCanon (off q : ℕ) : GLC := ⟨0, Xark.R1cs.normTerms leNat (packTermsAt off q)⟩

theorem packCanon_eval (off q : ℕ) (σ : ℕ → F) :
    (packCanon off q).eval σ = (packGLCAt off q).eval σ := by
  simp only [packCanon, packGLCAt, LC.eval]
  congr 1
  exact (Xark.R1cs.eval_normTerms leNat (packTermsAt off q) σ)

theorem nBound0 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 0) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 0 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 0) (LC.cst 0))) = packCanon 0 0 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound1 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 1) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 1 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 1) (LC.cst 0))) = packCanon 0 1 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound2 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 2) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 2 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 2) (LC.cst 0))) = packCanon 0 2 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound3 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 3) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 3 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 3) (LC.cst 0))) = packCanon 0 3 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound4 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 4) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 4 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 4) (LC.cst 0))) = packCanon 0 4 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound5 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 5) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 5 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 5) (LC.cst 0))) = packCanon 0 5 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound6 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 6) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 6 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 6) (LC.cst 0))) = packCanon 0 6 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound7 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 7) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 7 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 7) (LC.cst 0))) = packCanon 0 7 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound8 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 8) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 8 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 8) (LC.cst 0))) = packCanon 0 8 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound9 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 9) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 9 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 9) (LC.cst 0))) = packCanon 0 9 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound10 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 10) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 10 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 10) (LC.cst 0))) = packCanon 0 10 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound11 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 11) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 11 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 11) (LC.cst 0))) = packCanon 0 11 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound12 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 12) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 12 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 12) (LC.cst 0))) = packCanon 0 12 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound13 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 13) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 13 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 13) (LC.cst 0))) = packCanon 0 13 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound14 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 14) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 14 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 14) (LC.cst 0))) = packCanon 0 14 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound15 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 15) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 15 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 15) (LC.cst 0))) = packCanon 0 15 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound16 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 16) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 16 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 16) (LC.cst 0))) = packCanon 0 16 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound17 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 17) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 17 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 17) (LC.cst 0))) = packCanon 0 17 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound18 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 18) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 18 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 18) (LC.cst 0))) = packCanon 0 18 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound19 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 19) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 19 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 19) (LC.cst 0))) = packCanon 0 19 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound20 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 20) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 20 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 20) (LC.cst 0))) = packCanon 0 20 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound21 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 21) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 21 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 21) (LC.cst 0))) = packCanon 0 21 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound22 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 22) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 22 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 22) (LC.cst 0))) = packCanon 0 22 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound23 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 23) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 23 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 23) (LC.cst 0))) = packCanon 0 23 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem nBound24 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD (25 + 24) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 0 24 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD (25 + 24) (LC.cst 0))) = packCanon 0 24 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound0 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 0 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 0 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 0 (LC.cst 0))) = packCanon 256 0 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound1 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 1 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 1 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 1 (LC.cst 0))) = packCanon 256 1 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound2 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 2 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 2 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 2 (LC.cst 0))) = packCanon 256 2 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound3 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 3 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 3 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 3 (LC.cst 0))) = packCanon 256 3 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound4 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 4 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 4 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 4 (LC.cst 0))) = packCanon 256 4 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound5 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 5 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 5 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 5 (LC.cst 0))) = packCanon 256 5 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound6 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 6 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 6 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 6 (LC.cst 0))) = packCanon 256 6 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound7 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 7 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 7 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 7 (LC.cst 0))) = packCanon 256 7 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound8 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 8 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 8 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 8 (LC.cst 0))) = packCanon 256 8 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound9 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 9 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 9 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 9 (LC.cst 0))) = packCanon 256 9 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound10 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 10 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 10 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 10 (LC.cst 0))) = packCanon 256 10 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound11 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 11 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 11 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 11 (LC.cst 0))) = packCanon 256 11 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound12 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 12 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 12 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 12 (LC.cst 0))) = packCanon 256 12 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound13 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 13 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 13 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 13 (LC.cst 0))) = packCanon 256 13 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound14 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 14 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 14 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 14 (LC.cst 0))) = packCanon 256 14 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound15 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 15 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 15 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 15 (LC.cst 0))) = packCanon 256 15 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound16 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 16 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 16 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 16 (LC.cst 0))) = packCanon 256 16 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound17 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 17 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 17 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 17 (LC.cst 0))) = packCanon 256 17 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound18 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 18 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 18 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 18 (LC.cst 0))) = packCanon 256 18 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound19 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 19 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 19 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 19 (LC.cst 0))) = packCanon 256 19 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound20 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 20 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 20 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 20 (LC.cst 0))) = packCanon 256 20 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound21 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 21 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 21 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 21 (LC.cst 0))) = packCanon 256 21 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound22 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 22 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 22 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 22 (LC.cst 0))) = packCanon 256 22 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound23 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 23 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 23 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 23 (LC.cst 0))) = packCanon 256 23 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem sigBound24 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 548).plugs.getD 24 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 256 24 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 548).plugs.getD 24 (LC.cst 0))) = packCanon 256 24 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem emBound0 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 0) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 288 0 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 0) (LC.cst 0))) = packCanon 288 0 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem emBound1 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 1) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 288 1 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 1) (LC.cst 0))) = packCanon 288 1 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem emBound2 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 2) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hp := pack_bound 288 2 (by norm_num) σ hbit
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 2) (LC.cst 0))) = packCanon 288 2 := by
    decide +kernel
  rw [hc, packCanon_eval]
  exact hp

theorem emBound4 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 4) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 4) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 4 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound5 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 5) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 5) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 5 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound6 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 6) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 6) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 6 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound7 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 7) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 7) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 7 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound8 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 8) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 8) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 8 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound9 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 9) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 9) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 9 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound10 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 10) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 10) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 10 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound11 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 11) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 11) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 11 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound12 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 12) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 12) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 12 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound13 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 13) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 13) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 13 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound14 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 14) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 14) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 14 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound15 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 15) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 15) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 15 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound16 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 16) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 16) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 16 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound17 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 17) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 17) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 17 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound18 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 18) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 18) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 18 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound19 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 19) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 19) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 19 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound20 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 20) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 20) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 20 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound21 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 21) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 21) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 21 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound22 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 22) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 22) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 22 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound23 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 23) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 23) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 23 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

theorem emBound24 (σ : ℕ → F) :
    ((ZLC.toF ((callAt 596).plugs.getD (100 + 24) (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD (100 + 24) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 24 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  rw [hc]
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero]
  decide

end Xark.Circuits.Rsa2048
