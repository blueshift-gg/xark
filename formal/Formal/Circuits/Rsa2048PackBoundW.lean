/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048PackBound

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# A packed limb of `w` bits, and the encoded message's third limb

`pack_bound` bounds a full 82-bit limb. `sha256_em_bits_82`'s limb 3 carries only
the digest's top ten bits above its constant, so this file states the same bound at
width `w` and uses it for that limb.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template

/-- The first `w` bits of limb `q`, from bytes `off .. off + 255` (big-endian). -/
def packTermsAtW (off q w : ℕ) : List (F × ℕ) :=
  (List.range w).flatMap fun t =>
    let j := 82 * q + t
    if j < 2048 then
      let b := off + (255 - j / 8)
      let tb := j % 8
      (bitTerms b tb).map fun term => (((↑(2 ^ t)) : F) * term.1, term.2)
    else []

def packGLCAtW (off q w : ℕ) : GLC := ⟨0, packTermsAtW off q w⟩

def packCanonW (off q w : ℕ) : GLC := ⟨0, Xark.R1cs.normTerms leNat (packTermsAtW off q w)⟩

theorem packCanonW_eval (off q w : ℕ) (σ : ℕ → F) :
    (packCanonW off q w).eval σ = (packGLCAtW off q w).eval σ := by
  simp only [packCanonW, packGLCAtW, LC.eval]
  congr 1
  exact (Xark.R1cs.eval_normTerms leNat (packTermsAtW off q w) σ)

theorem eval_packTermsW (off q w : ℕ) (σ : ℕ → F) :
    (packGLCAtW off q w).eval σ
      = ∑ t ∈ Finset.range w,
          if 82 * q + t < 2048 then
            (↑(2 ^ t) : F)
              * ((bitTerms (off + (255 - (82 * q + t) / 8)) ((82 * q + t) % 8)).map
                  fun term => term.1 * σ term.2).sum
          else 0 := by
  simp only [packGLCAtW, packTermsAtW, LC.eval, List.sum_nil, zero_add]
  rw [sum_flatMapF, sum_rangeF]
  refine Finset.sum_congr rfl fun t ht => ?_
  by_cases hj : 82 * q + t < 2048
  · simp only [hj, if_pos]
    rw [List.map_map]
    exact sum_map_scale _ _ σ
  · simp only [hj, if_false, List.map_nil, List.sum_nil]

theorem weighted_ltW (w : ℕ) (f : ℕ → F) (hf : ∀ t < w, (f t).val ≤ 1) :
    (∑ t ∈ Finset.range w, 2 ^ t * (f t).val) < 2 ^ w := by
  have hgeom : (∑ t ∈ Finset.range w, 2 ^ t : ℕ) = 2 ^ w - 1 := by
    have h : ∀ n, (∑ t ∈ Finset.range n, 2 ^ t : ℕ) = 2 ^ n - 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; omega
    exact h w
  have hle : (∑ t ∈ Finset.range w, 2 ^ t * (f t).val) ≤ 2 ^ w - 1 := by
    calc (∑ t ∈ Finset.range w, 2 ^ t * (f t).val) ≤ ∑ t ∈ Finset.range w, 2 ^ t * 1 :=
          Finset.sum_le_sum fun t ht => Nat.mul_le_mul_left _ (hf t (Finset.mem_range.mp ht))
      _ = 2 ^ w - 1 := by simpa using hgeom
  have hsub : 2 ^ w - 1 < 2 ^ w := by
    have h : (0 : ℕ) < 2 ^ w := by positivity
    omega
  exact lt_of_le_of_lt hle hsub

theorem val_weightedW (w : ℕ) (hw : w ≤ 82) (f : ℕ → F) (hf : ∀ t < w, (f t).val ≤ 1) :
    ((∑ t ∈ Finset.range w, ((2 ^ t : ℕ) : F) * f t).val)
      = ∑ t ∈ Finset.range w, 2 ^ t * (f t).val := by
  have hcast : (∑ t ∈ Finset.range w, ((2 ^ t : ℕ) : F) * f t)
      = ((∑ t ∈ Finset.range w, 2 ^ t * (f t).val : ℕ) : F) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hft : f t = ((f t).val : F) := (ZMod.natCast_zmod_val (f t)).symm
    conv_lhs => rw [hft]
    exact (Nat.cast_mul (m := 2 ^ t) (n := (f t).val)).symm
  have hw82 : (2 : ℕ) ^ w ≤ 2 ^ 82 := Nat.pow_le_pow_right (by norm_num) hw
  have hlt : (∑ t ∈ Finset.range w, 2 ^ t * (f t).val) < r := by
    have h1 : (∑ t ∈ Finset.range w, 2 ^ t * (f t).val) < 2 ^ w := weighted_ltW w f hf
    exact lt_of_lt_of_le h1 (le_trans hw82 (le_of_lt (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num))))
  rw [hcast, ZMod.val_natCast_of_lt hlt]

theorem pack_boundW (off q w : ℕ) (hoff : off ≤ 288) (hw : w ≤ 82) (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((packGLCAtW off q w).eval σ).val < 2 ^ w := by
  rw [eval_packTermsW]
  let f : ℕ → F := fun t =>
    if 82 * q + t < 2048 then (bitGLC (off + (255 - (82 * q + t) / 8)) ((82 * q + t) % 8)).eval σ
    else 0
  have hsum : (∑ t ∈ Finset.range w,
        if 82 * q + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (off + (255 - (82 * q + t) / 8)) ((82 * q + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range w, ((2 ^ t : ℕ) : F) * f t := by
    refine Finset.sum_congr rfl fun t ht => ?_
    dsimp [f]
    by_cases h : 82 * q + t < 2048
    · simp only [h, if_pos, bitGLC, LC.eval, zero_add, Nat.cast_pow, Nat.cast_ofNat]
    · simp only [h, if_false, mul_zero]
  rw [hsum]
  have hf : ∀ t < w, (f t).val ≤ 1 := by
    intro t ht
    dsimp [f]
    by_cases h : 82 * q + t < 2048
    · rw [if_pos h]
      exact hbit _ _ (by omega) (by omega)
    · rw [if_neg h]; simp
  rw [val_weightedW w hw f hf]
  exact weighted_ltW w f hf

/-- The encoded message's limb 3: the constant frame plus the digest's top ten bits. -/
def emCanon3 : GLC :=
  ⟨((Xark.Rsa.Em.em82 3 : ℤ) : F), Xark.R1cs.normTerms leNat (packTermsAtW 288 3 10)⟩

theorem emCanon3_eval (σ : ℕ → F) :
    (emCanon3).eval σ
      = ((Xark.Rsa.Em.em82 3 : ℤ) : F) + (packGLCAtW 288 3 10).eval σ := by
  simp only [emCanon3, packGLCAtW, LC.eval, List.sum_nil, zero_add]
  congr 1
  exact (Xark.R1cs.eval_normTerms leNat (packTermsAtW 288 3 10) σ)

/-- The encoded message's third limb is below `2^82`: its constant is the frame's
`1908058575186009548423168 + …` and the digest adds ten bits at most. -/
theorem emBound3 (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1) :
    ((ZLC.toF ((callAt 596).plugs.getD 103 (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hc : (ZLC.toF ((callAt 596).plugs.getD 103 (LC.cst 0))) = emCanon3 := by
    decide +kernel
  rw [hc, emCanon3_eval]
  have hS := pack_boundW 288 3 10 (by norm_num) (by norm_num) σ hbit
  have hc3 : (Xark.Rsa.Em.em82 3).toNat = 1908058575186009548423168 := by decide
  have hcval : ((Xark.Rsa.Em.em82 3 : ℤ) : F).val = 1908058575186009548423168 := by
    have h0 : (0 : ℤ) ≤ Xark.Rsa.Em.em82 3 := by decide
    have hcast : ((Xark.Rsa.Em.em82 3 : ℤ) : F)
        = (((Xark.Rsa.Em.em82 3).toNat : ℕ) : F) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    rw [hcast, hc3, ZMod.val_natCast_of_lt (by decide)]
  have hr : 1908058575186009548423168 + 1023 < r := by decide
  have hlt : 1908058575186009548423168 + ((packGLCAtW 288 3 10).eval σ).val < r := by
    omega
  rw [ZMod.val_add, hcval, Nat.mod_eq_of_lt hlt]
  omega

def bitOut (b tb : ℕ) : GLC :=
  ((callAt b).t.outputs.getD tb (LC.cst 0)).bind (callAt b).env

theorem bitOf_val_le3 (x : F) (t : ℕ) : (Xark.Template.bitOf x t).val ≤ 1 := by
  unfold Xark.Template.bitOf
  split <;> decide

theorem getD_map_eq {α β : Type} (l : List α) (g : α → β) (i : ℕ) (d : α) (z : β)
    (h : g d = z) : (l.map g).getD i z = g (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h' : l[i]? with
  | none => simp [h]
  | some a => simp

theorem bitOut_eval (b tb : ℕ) (σ : ℕ → F) :
    (bitOut b tb).eval σ = ((callAt b).t.outs ((callAt b).lift σ)).getD tb 0 := by
  simp only [bitOut, Call.outs, LC.eval_bind]
  rw [getD_map_eq _ (fun l => LC.eval l (fun v => LC.eval ((callAt b).env v) σ)) tb (LC.cst 0) 0
    (by simp [LC.cst, LC.eval])]

theorem bitGLC_eq_bitOut (b tb : ℕ) (htb : tb < 8)
    (hplugs : (callAt b).plugs = [(Xark.R1cs.LC.var b : Xark.Circuit.ZLC)])
    (hbase : (callAt b).base = bitBase b)
    (hb0 : (callAt b).t = Xark.Templates.ToBits.template) :
    bitGLC b tb = bitOut b tb := by
  interval_cases tb <;>
    simp [bitGLC, bitTerms, bitOut, Call.env, hplugs, hbase, hb0,
      Xark.Templates.ToBits.template, ZLC.toF, LC.bind, LC.var, LC.cst] <;>
    try rfl


end Xark.Circuits.Rsa2048
