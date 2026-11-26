/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.Statement

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The encoded message's integer

`sha256_em_bits_82` puts `EM82_CONST`'s limbs together with the digest's 256 bits.
`digestBits σ j` reads bit `j` of the circuit's digest (byte `512 + 31 - j/8`, bit
`j % 8`), `emCanon q` is the exported limb's canonical form, and this file proves
`emOut (digestBits σ) q = pn (fin) σ (100+q)` for every limb `q`, then
`chainEm σ = RsaEm.em (digestBits σ)`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- Bit `j` of the digest the circuit carries (bytes `512..543`, big-endian). -/
def digestBits (σ : ℕ → F) (j : ℕ) : ℤ :=
  (((bitGLC (512 + (31 - j / 8)) (j % 8)).eval σ).val : ℤ)

theorem limbOf_small (bits : ℕ → ℤ) (q w : ℕ) (hw : w ≤ 82) (h : 82 * q + w = 256) :
    Xark.Rsa.Bytes.limbOf bits 82 256 q
      = ∑ t ∈ Finset.range w, bits (82 * q + t) * 2 ^ t := by
  rw [Xark.Rsa.Bytes.limbOf]
  have hsub : Finset.range w ⊆ Finset.range 82 := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ t ∈ Finset.range 82, t ∉ Finset.range w →
      (if 82 * q + t < 256 then bits (82 * q + t) * 2 ^ t else 0) = 0 := by
    intro t ht82 htw
    simp only [Finset.mem_range] at ht82 htw
    rw [if_neg (by omega)]
  have h1 := Finset.sum_subset hsub hzero
  rw [← h1]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at ht
  rw [if_pos (by omega)]

theorem bitGLC_eval_eq (b tb : ℕ) (σ : ℕ → F) :
    (List.map (fun term => term.1 * σ term.2) (bitTerms b tb)).sum = (bitGLC b tb).eval σ := by
  simp only [bitGLC, LC.eval, zero_add]

/-- The encoded message's limb `q` in canonical form. -/
def emCanon (q : ℕ) : GLC :=
  ⟨((Xark.Rsa.Em.em82 q : ℤ) : F), Xark.R1cs.normTerms leNat (emTerms q)⟩

theorem emCanon_eval (q : ℕ) (σ : ℕ → F) :
    (emCanon q).eval σ
      = ((Xark.Rsa.Em.em82 q : ℤ) : F) + (⟨0, Xark.R1cs.normTerms leNat (emTerms q)⟩ : GLC).eval σ := by
  simp only [emCanon, LC.eval, zero_add]

theorem pn_emOut_0 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn fin σ (100 + 0) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 0 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 0) (LC.cst 0))) = packCanon 288 0 := by
    decide +kernel
  have hval : (pn fin σ (100 + 0) : ℤ) = (((packCanon 288 0).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 0) (LC.cst 0)) = packCanon 288 0 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 0 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (288 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (288 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 0 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (288 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf digestBits
  have h0 : Xark.Rsa.Em.em82 0 = 0 := rfl
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht82 := Finset.mem_range.mp ht
  rw [if_pos (by omega : 82 * 0 + t < 256)]
  have hb' : (288 + (255 - (82 * 0 + t) / 8)) = (512 + (31 - (82 * 0 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_emOut_1 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn fin σ (100 + 1) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 1 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 1) (LC.cst 0))) = packCanon 288 1 := by
    decide +kernel
  have hval : (pn fin σ (100 + 1) : ℤ) = (((packCanon 288 1).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 1) (LC.cst 0)) = packCanon 288 1 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 1 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (288 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (288 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 1 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (288 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf digestBits
  have h0 : Xark.Rsa.Em.em82 1 = 0 := rfl
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht82 := Finset.mem_range.mp ht
  rw [if_pos (by omega : 82 * 1 + t < 256)]
  have hb' : (288 + (255 - (82 * 1 + t) / 8)) = (512 + (31 - (82 * 1 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_emOut_2 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn fin σ (100 + 2) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 2 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 2) (LC.cst 0))) = packCanon 288 2 := by
    decide +kernel
  have hval : (pn fin σ (100 + 2) : ℤ) = (((packCanon 288 2).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 2) (LC.cst 0)) = packCanon 288 2 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 2 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (288 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (288 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 2 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (288 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf digestBits
  have h0 : Xark.Rsa.Em.em82 2 = 0 := rfl
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht82 := Finset.mem_range.mp ht
  rw [if_pos (by omega : 82 * 2 + t < 256)]
  have hb' : (288 + (255 - (82 * 2 + t) / 8)) = (512 + (31 - (82 * 2 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_emOut_3 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn fin σ 103 : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 3 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 596).plugs.getD 103 (LC.cst 0))) = emCanon3 := by
    decide +kernel
  have hval : (pn fin σ 103 : ℤ) = (((emCanon3).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD 103 (LC.cst 0)) = emCanon3 from hplug]
  rw [hval, emCanon3_eval, eval_packTermsW]
  have hsum : (∑ t ∈ Finset.range 10,
        if 82 * 3 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (288 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 10,
          ((2 ^ t : ℕ) : F) * (bitGLC (288 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht10 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 3 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 10,
      ((bitGLC (288 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  have hS := val_weightedW 10 (by norm_num)
    (fun t => (bitGLC (288 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ) hf
  have hSlt : (∑ t ∈ Finset.range 10,
      2 ^ t * ((bitGLC (288 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ).val) < 2 ^ 10 :=
    weighted_ltW 10 _ hf
  have hc3 : ((Xark.Rsa.Em.em82 3 : ℤ) : F).val = 1908058575186009548423168 := by
    have h0 : (0 : ℤ) ≤ Xark.Rsa.Em.em82 3 := by decide
    have hcast : ((Xark.Rsa.Em.em82 3 : ℤ) : F)
        = (((Xark.Rsa.Em.em82 3).toNat : ℕ) : F) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    rw [hcast, show (Xark.Rsa.Em.em82 3).toNat = 1908058575186009548423168 by decide,
      ZMod.val_natCast_of_lt (by decide)]
  have hSle : (∑ t ∈ Finset.range 10,
      2 ^ t * ((bitGLC (288 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ).val) ≤ 2 ^ 10 - 1 := by
    omega
  have hr : 1908058575186009548423168 + (2 ^ 10 - 1) < r := by decide
  have hlt : 1908058575186009548423168
      + (∑ t ∈ Finset.range 10,
          2 ^ t * ((bitGLC (288 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ).val) < r := by
    omega
  rw [ZMod.val_add, hS, hc3, Nat.mod_eq_of_lt hlt]
  rw [Nat.cast_add, Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold Xark.Rsa.Em.emOut
  rw [limbOf_small (digestBits σ) 3 10 (by norm_num) (by norm_num)]
  unfold digestBits
  have h0 : Xark.Rsa.Em.em82 3 = 1908058575186009548423168 := by decide
  rw [h0]
  refine congrArg (fun z => 1908058575186009548423168 + z) ?_
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht10 := Finset.mem_range.mp ht
  have hb' : (288 + (255 - (82 * 3 + t) / 8)) = (512 + (31 - (82 * 3 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_emOut_4 (σ : ℕ → F) :
    (pn fin σ (100 + 4) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 4 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 4) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 4 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 4) : ℤ) = Xark.Rsa.Em.em82 4 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 4) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 4 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 4 : ℤ) : F).val = (Xark.Rsa.Em.em82 4).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 4 + t < 256 then digestBits σ (82 * 4 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 4 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_5 (σ : ℕ → F) :
    (pn fin σ (100 + 5) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 5 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 5) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 5 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 5) : ℤ) = Xark.Rsa.Em.em82 5 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 5) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 5 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 5 : ℤ) : F).val = (Xark.Rsa.Em.em82 5).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 5 + t < 256 then digestBits σ (82 * 5 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 5 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_6 (σ : ℕ → F) :
    (pn fin σ (100 + 6) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 6 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 6) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 6 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 6) : ℤ) = Xark.Rsa.Em.em82 6 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 6) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 6 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 6 : ℤ) : F).val = (Xark.Rsa.Em.em82 6).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 6 + t < 256 then digestBits σ (82 * 6 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 6 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_7 (σ : ℕ → F) :
    (pn fin σ (100 + 7) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 7 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 7) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 7 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 7) : ℤ) = Xark.Rsa.Em.em82 7 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 7) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 7 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 7 : ℤ) : F).val = (Xark.Rsa.Em.em82 7).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 7 + t < 256 then digestBits σ (82 * 7 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 7 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_8 (σ : ℕ → F) :
    (pn fin σ (100 + 8) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 8 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 8) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 8 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 8) : ℤ) = Xark.Rsa.Em.em82 8 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 8) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 8 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 8 : ℤ) : F).val = (Xark.Rsa.Em.em82 8).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 8 + t < 256 then digestBits σ (82 * 8 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 8 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_9 (σ : ℕ → F) :
    (pn fin σ (100 + 9) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 9 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 9) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 9 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 9) : ℤ) = Xark.Rsa.Em.em82 9 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 9) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 9 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 9 : ℤ) : F).val = (Xark.Rsa.Em.em82 9).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 9 + t < 256 then digestBits σ (82 * 9 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 9 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_10 (σ : ℕ → F) :
    (pn fin σ (100 + 10) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 10 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 10) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 10 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 10) : ℤ) = Xark.Rsa.Em.em82 10 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 10) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 10 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 10 : ℤ) : F).val = (Xark.Rsa.Em.em82 10).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 10 + t < 256 then digestBits σ (82 * 10 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 10 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_11 (σ : ℕ → F) :
    (pn fin σ (100 + 11) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 11 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 11) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 11 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 11) : ℤ) = Xark.Rsa.Em.em82 11 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 11) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 11 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 11 : ℤ) : F).val = (Xark.Rsa.Em.em82 11).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 11 + t < 256 then digestBits σ (82 * 11 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 11 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_12 (σ : ℕ → F) :
    (pn fin σ (100 + 12) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 12 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 12) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 12 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 12) : ℤ) = Xark.Rsa.Em.em82 12 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 12) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 12 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 12 : ℤ) : F).val = (Xark.Rsa.Em.em82 12).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 12 + t < 256 then digestBits σ (82 * 12 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 12 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_13 (σ : ℕ → F) :
    (pn fin σ (100 + 13) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 13 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 13) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 13 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 13) : ℤ) = Xark.Rsa.Em.em82 13 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 13) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 13 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 13 : ℤ) : F).val = (Xark.Rsa.Em.em82 13).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 13 + t < 256 then digestBits σ (82 * 13 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 13 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_14 (σ : ℕ → F) :
    (pn fin σ (100 + 14) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 14 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 14) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 14 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 14) : ℤ) = Xark.Rsa.Em.em82 14 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 14) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 14 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 14 : ℤ) : F).val = (Xark.Rsa.Em.em82 14).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 14 + t < 256 then digestBits σ (82 * 14 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 14 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_15 (σ : ℕ → F) :
    (pn fin σ (100 + 15) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 15 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 15) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 15 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 15) : ℤ) = Xark.Rsa.Em.em82 15 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 15) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 15 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 15 : ℤ) : F).val = (Xark.Rsa.Em.em82 15).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 15 + t < 256 then digestBits σ (82 * 15 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 15 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_16 (σ : ℕ → F) :
    (pn fin σ (100 + 16) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 16 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 16) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 16 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 16) : ℤ) = Xark.Rsa.Em.em82 16 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 16) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 16 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 16 : ℤ) : F).val = (Xark.Rsa.Em.em82 16).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 16 + t < 256 then digestBits σ (82 * 16 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 16 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_17 (σ : ℕ → F) :
    (pn fin σ (100 + 17) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 17 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 17) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 17 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 17) : ℤ) = Xark.Rsa.Em.em82 17 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 17) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 17 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 17 : ℤ) : F).val = (Xark.Rsa.Em.em82 17).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 17 + t < 256 then digestBits σ (82 * 17 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 17 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_18 (σ : ℕ → F) :
    (pn fin σ (100 + 18) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 18 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 18) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 18 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 18) : ℤ) = Xark.Rsa.Em.em82 18 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 18) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 18 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 18 : ℤ) : F).val = (Xark.Rsa.Em.em82 18).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 18 + t < 256 then digestBits σ (82 * 18 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 18 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_19 (σ : ℕ → F) :
    (pn fin σ (100 + 19) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 19 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 19) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 19 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 19) : ℤ) = Xark.Rsa.Em.em82 19 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 19) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 19 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 19 : ℤ) : F).val = (Xark.Rsa.Em.em82 19).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 19 + t < 256 then digestBits σ (82 * 19 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 19 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_20 (σ : ℕ → F) :
    (pn fin σ (100 + 20) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 20 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 20) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 20 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 20) : ℤ) = Xark.Rsa.Em.em82 20 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 20) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 20 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 20 : ℤ) : F).val = (Xark.Rsa.Em.em82 20).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 20 + t < 256 then digestBits σ (82 * 20 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 20 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_21 (σ : ℕ → F) :
    (pn fin σ (100 + 21) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 21 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 21) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 21 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 21) : ℤ) = Xark.Rsa.Em.em82 21 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 21) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 21 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 21 : ℤ) : F).val = (Xark.Rsa.Em.em82 21).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 21 + t < 256 then digestBits σ (82 * 21 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 21 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_22 (σ : ℕ → F) :
    (pn fin σ (100 + 22) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 22 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 22) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 22 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 22) : ℤ) = Xark.Rsa.Em.em82 22 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 22) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 22 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 22 : ℤ) : F).val = (Xark.Rsa.Em.em82 22).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 22 + t < 256 then digestBits σ (82 * 22 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 22 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_23 (σ : ℕ → F) :
    (pn fin σ (100 + 23) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 23 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 23) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 23 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 23) : ℤ) = Xark.Rsa.Em.em82 23 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 23) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 23 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 23 : ℤ) : F).val = (Xark.Rsa.Em.em82 23).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 23 + t < 256 then digestBits σ (82 * 23 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 23 + t < 256)]
  rw [hsum0, add_zero]

theorem pn_emOut_24 (σ : ℕ → F) :
    (pn fin σ (100 + 24) : ℤ) = Xark.Rsa.Em.emOut (digestBits σ) 24 := by
  have hplug : (ZLC.toF ((callAt 596).plugs.getD (100 + 24) (LC.cst 0)))
      = (⟨((Xark.Rsa.Em.em82 24 : ℤ) : F), []⟩ : GLC) := by
    decide +kernel
  have hval : (pn fin σ (100 + 24) : ℤ) = Xark.Rsa.Em.em82 24 := by
    simp only [pn, Call.lift, Call.env, fin]
    rw [show ZLC.toF ((callAt 596).plugs.getD (100 + 24) (LC.cst 0))
        = (⟨((Xark.Rsa.Em.em82 24 : ℤ) : F), []⟩ : GLC) from hplug]
    simp only [LC.eval, List.map_nil, List.sum_nil, zero_add, add_zero]
    rw [show ((Xark.Rsa.Em.em82 24 : ℤ) : F).val = (Xark.Rsa.Em.em82 24).toNat by decide]
    exact Int.toNat_of_nonneg (by decide)
  rw [hval]
  unfold Xark.Rsa.Em.emOut Xark.Rsa.Bytes.limbOf
  have hsum0 : (∑ t ∈ Finset.range 82,
      if 82 * 24 + t < 256 then digestBits σ (82 * 24 + t) * 2 ^ t else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_neg (by omega : ¬ 82 * 24 + t < 256)]
  rw [hsum0, add_zero]

/-- **The encoded message's integer from the circuit's limbs.** -/
theorem val_em_limb (σ : ℕ → F) (h : Sat circuit σ) :
    val (limb fin σ 100) = val (Xark.Rsa.Em.emOut (digestBits σ)) := by
  rw [val, val]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq25 := Finset.mem_range.mp hq
  interval_cases q
  · change pv fin σ (100 + 0) * W ^ 0 = Xark.Rsa.Em.emOut (digestBits σ) 0 * W ^ 0
    rw [pv_eq_pn, pn_emOut_0 σ h]
  · change pv fin σ (100 + 1) * W ^ 1 = Xark.Rsa.Em.emOut (digestBits σ) 1 * W ^ 1
    rw [pv_eq_pn, pn_emOut_1 σ h]
  · change pv fin σ (100 + 2) * W ^ 2 = Xark.Rsa.Em.emOut (digestBits σ) 2 * W ^ 2
    rw [pv_eq_pn, pn_emOut_2 σ h]
  · change pv fin σ (100 + 3) * W ^ 3 = Xark.Rsa.Em.emOut (digestBits σ) 3 * W ^ 3
    rw [pv_eq_pn, pn_emOut_3 σ h]
  · change pv fin σ (100 + 4) * W ^ 4 = Xark.Rsa.Em.emOut (digestBits σ) 4 * W ^ 4
    rw [pv_eq_pn, pn_emOut_4 σ]
  · change pv fin σ (100 + 5) * W ^ 5 = Xark.Rsa.Em.emOut (digestBits σ) 5 * W ^ 5
    rw [pv_eq_pn, pn_emOut_5 σ]
  · change pv fin σ (100 + 6) * W ^ 6 = Xark.Rsa.Em.emOut (digestBits σ) 6 * W ^ 6
    rw [pv_eq_pn, pn_emOut_6 σ]
  · change pv fin σ (100 + 7) * W ^ 7 = Xark.Rsa.Em.emOut (digestBits σ) 7 * W ^ 7
    rw [pv_eq_pn, pn_emOut_7 σ]
  · change pv fin σ (100 + 8) * W ^ 8 = Xark.Rsa.Em.emOut (digestBits σ) 8 * W ^ 8
    rw [pv_eq_pn, pn_emOut_8 σ]
  · change pv fin σ (100 + 9) * W ^ 9 = Xark.Rsa.Em.emOut (digestBits σ) 9 * W ^ 9
    rw [pv_eq_pn, pn_emOut_9 σ]
  · change pv fin σ (100 + 10) * W ^ 10 = Xark.Rsa.Em.emOut (digestBits σ) 10 * W ^ 10
    rw [pv_eq_pn, pn_emOut_10 σ]
  · change pv fin σ (100 + 11) * W ^ 11 = Xark.Rsa.Em.emOut (digestBits σ) 11 * W ^ 11
    rw [pv_eq_pn, pn_emOut_11 σ]
  · change pv fin σ (100 + 12) * W ^ 12 = Xark.Rsa.Em.emOut (digestBits σ) 12 * W ^ 12
    rw [pv_eq_pn, pn_emOut_12 σ]
  · change pv fin σ (100 + 13) * W ^ 13 = Xark.Rsa.Em.emOut (digestBits σ) 13 * W ^ 13
    rw [pv_eq_pn, pn_emOut_13 σ]
  · change pv fin σ (100 + 14) * W ^ 14 = Xark.Rsa.Em.emOut (digestBits σ) 14 * W ^ 14
    rw [pv_eq_pn, pn_emOut_14 σ]
  · change pv fin σ (100 + 15) * W ^ 15 = Xark.Rsa.Em.emOut (digestBits σ) 15 * W ^ 15
    rw [pv_eq_pn, pn_emOut_15 σ]
  · change pv fin σ (100 + 16) * W ^ 16 = Xark.Rsa.Em.emOut (digestBits σ) 16 * W ^ 16
    rw [pv_eq_pn, pn_emOut_16 σ]
  · change pv fin σ (100 + 17) * W ^ 17 = Xark.Rsa.Em.emOut (digestBits σ) 17 * W ^ 17
    rw [pv_eq_pn, pn_emOut_17 σ]
  · change pv fin σ (100 + 18) * W ^ 18 = Xark.Rsa.Em.emOut (digestBits σ) 18 * W ^ 18
    rw [pv_eq_pn, pn_emOut_18 σ]
  · change pv fin σ (100 + 19) * W ^ 19 = Xark.Rsa.Em.emOut (digestBits σ) 19 * W ^ 19
    rw [pv_eq_pn, pn_emOut_19 σ]
  · change pv fin σ (100 + 20) * W ^ 20 = Xark.Rsa.Em.emOut (digestBits σ) 20 * W ^ 20
    rw [pv_eq_pn, pn_emOut_20 σ]
  · change pv fin σ (100 + 21) * W ^ 21 = Xark.Rsa.Em.emOut (digestBits σ) 21 * W ^ 21
    rw [pv_eq_pn, pn_emOut_21 σ]
  · change pv fin σ (100 + 22) * W ^ 22 = Xark.Rsa.Em.emOut (digestBits σ) 22 * W ^ 22
    rw [pv_eq_pn, pn_emOut_22 σ]
  · change pv fin σ (100 + 23) * W ^ 23 = Xark.Rsa.Em.emOut (digestBits σ) 23 * W ^ 23
    rw [pv_eq_pn, pn_emOut_23 σ]
  · change pv fin σ (100 + 24) * W ^ 24 = Xark.Rsa.Em.emOut (digestBits σ) 24 * W ^ 24
    rw [pv_eq_pn, pn_emOut_24 σ]

/-- **`chainEm` is the RFC 8017 encoded message.** -/
theorem chainEm_eq (σ : ℕ → F) (h : Sat circuit σ) :
    chainEm σ = Xark.Rsa.Em.EM_PREFIX
      + ∑ j ∈ Finset.range 256, digestBits σ j * 2 ^ j := by
  rw [chainEm, val_em_limb σ h]
  exact Xark.Rsa.Em.em (digestBits σ)

/-- **The chain congruence with the RFC 8017 encoded message.** -/
theorem chain_congruence_em (σ : ℕ → F) (h : Sat circuit σ) :
    Xark.Rsa.Em.EM_PREFIX + ∑ j ∈ Finset.range 256, digestBits σ j * 2 ^ j
      ≡ (val (limb sq0 σ 0)) ^ (2 ^ 16 + 1) [ZMOD chainN σ] := by
  rw [← chainEm_eq σ h]
  exact chain_congruence_sat σ h

end Xark.Circuits.Rsa2048
