/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.EmBits

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The modulus and signature integers

`bytes_to_wide` packs bytes `0..255` (the modulus) and `256..511` (the signature)
big-endian at 82-bit limbs. `nBits`/`sigBits` read the packed bit string, and this
file proves each chain call's limb is the matching `limbOf`, then
`chainN = Σ_i n_i·256^(255-i)` and the same for the signature.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- Bit `j` of the modulus's byte string (bytes `0..255`, big-endian). -/
def nBits (σ : ℕ → F) (j : ℕ) : ℤ :=
  (((bitGLC (255 - j / 8) (j % 8)).eval σ).val : ℤ)

/-- Bit `j` of the signature's byte string (bytes `256..511`, big-endian). -/
def sigBits (σ : ℕ → F) (j : ℕ) : ℤ :=
  (((bitGLC (256 + (255 - j / 8)) (j % 8)).eval σ).val : ℤ)

theorem limbOf_full (bits : ℕ → ℤ) (q N : ℕ) (h : 82 * q + 82 ≤ N) :
    Xark.Rsa.Bytes.limbOf bits 82 N q = ∑ t ∈ Finset.range 82, bits (82 * q + t) * 2 ^ t := by
  rw [Xark.Rsa.Bytes.limbOf]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at ht
  rw [if_pos (by omega)]

theorem limbOf_last (bits : ℕ → ℤ) (q w N : ℕ) (hw : w ≤ 82) (h : 82 * q + w = N) :
    Xark.Rsa.Bytes.limbOf bits 82 N q = ∑ t ∈ Finset.range w, bits (82 * q + t) * 2 ^ t := by
  rw [Xark.Rsa.Bytes.limbOf]
  have hsub : Finset.range w ⊆ Finset.range 82 := by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  have hzero : ∀ t ∈ Finset.range 82, t ∉ Finset.range w →
      (if 82 * q + t < N then bits (82 * q + t) * 2 ^ t else 0) = 0 := by
    intro t ht82 htw
    simp only [Finset.mem_range] at ht82 htw
    rw [if_neg (by omega)]
  have h1 := Finset.sum_subset hsub hzero
  rw [← h1]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at ht
  rw [if_pos (by omega)]

theorem pn_n_0 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 0) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 0 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 0) (LC.cst 0))) = packCanon 0 0 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 0) : ℤ) = (((packCanon 0 0).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 0) (LC.cst 0)) = packCanon 0 0 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 0 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 0 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 0 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 0 + t) / 8)) = (255 - (82 * 0 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_1 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 1) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 1 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 1) (LC.cst 0))) = packCanon 0 1 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 1) : ℤ) = (((packCanon 0 1).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 1) (LC.cst 0)) = packCanon 0 1 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 1 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 1 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 1 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 1 + t) / 8)) = (255 - (82 * 1 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_2 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 2) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 2 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 2) (LC.cst 0))) = packCanon 0 2 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 2) : ℤ) = (((packCanon 0 2).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 2) (LC.cst 0)) = packCanon 0 2 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 2 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 2 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 2 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 2 + t) / 8)) = (255 - (82 * 2 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_3 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 3) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 3 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 3) (LC.cst 0))) = packCanon 0 3 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 3) : ℤ) = (((packCanon 0 3).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 3) (LC.cst 0)) = packCanon 0 3 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 3 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 3 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 3 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 3 + t) / 8)) = (255 - (82 * 3 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_4 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 4) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 4 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 4) (LC.cst 0))) = packCanon 0 4 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 4) : ℤ) = (((packCanon 0 4).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 4) (LC.cst 0)) = packCanon 0 4 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 4 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 4 + t) / 8)) ((82 * 4 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 4 + t) / 8)) ((82 * 4 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 4 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 4 + t) / 8)) ((82 * 4 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 4 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 4 + t) / 8)) = (255 - (82 * 4 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_5 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 5) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 5 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 5) (LC.cst 0))) = packCanon 0 5 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 5) : ℤ) = (((packCanon 0 5).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 5) (LC.cst 0)) = packCanon 0 5 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 5 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 5 + t) / 8)) ((82 * 5 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 5 + t) / 8)) ((82 * 5 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 5 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 5 + t) / 8)) ((82 * 5 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 5 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 5 + t) / 8)) = (255 - (82 * 5 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_6 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 6) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 6 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 6) (LC.cst 0))) = packCanon 0 6 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 6) : ℤ) = (((packCanon 0 6).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 6) (LC.cst 0)) = packCanon 0 6 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 6 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 6 + t) / 8)) ((82 * 6 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 6 + t) / 8)) ((82 * 6 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 6 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 6 + t) / 8)) ((82 * 6 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 6 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 6 + t) / 8)) = (255 - (82 * 6 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_7 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 7) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 7 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 7) (LC.cst 0))) = packCanon 0 7 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 7) : ℤ) = (((packCanon 0 7).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 7) (LC.cst 0)) = packCanon 0 7 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 7 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 7 + t) / 8)) ((82 * 7 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 7 + t) / 8)) ((82 * 7 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 7 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 7 + t) / 8)) ((82 * 7 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 7 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 7 + t) / 8)) = (255 - (82 * 7 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_8 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 8) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 8 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 8) (LC.cst 0))) = packCanon 0 8 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 8) : ℤ) = (((packCanon 0 8).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 8) (LC.cst 0)) = packCanon 0 8 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 8 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 8 + t) / 8)) ((82 * 8 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 8 + t) / 8)) ((82 * 8 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 8 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 8 + t) / 8)) ((82 * 8 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 8 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 8 + t) / 8)) = (255 - (82 * 8 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_9 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 9) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 9 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 9) (LC.cst 0))) = packCanon 0 9 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 9) : ℤ) = (((packCanon 0 9).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 9) (LC.cst 0)) = packCanon 0 9 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 9 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 9 + t) / 8)) ((82 * 9 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 9 + t) / 8)) ((82 * 9 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 9 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 9 + t) / 8)) ((82 * 9 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 9 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 9 + t) / 8)) = (255 - (82 * 9 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_10 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 10) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 10 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 10) (LC.cst 0))) = packCanon 0 10 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 10) : ℤ) = (((packCanon 0 10).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 10) (LC.cst 0)) = packCanon 0 10 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 10 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 10 + t) / 8)) ((82 * 10 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 10 + t) / 8)) ((82 * 10 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 10 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 10 + t) / 8)) ((82 * 10 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 10 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 10 + t) / 8)) = (255 - (82 * 10 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_11 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 11) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 11 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 11) (LC.cst 0))) = packCanon 0 11 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 11) : ℤ) = (((packCanon 0 11).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 11) (LC.cst 0)) = packCanon 0 11 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 11 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 11 + t) / 8)) ((82 * 11 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 11 + t) / 8)) ((82 * 11 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 11 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 11 + t) / 8)) ((82 * 11 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 11 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 11 + t) / 8)) = (255 - (82 * 11 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_12 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 12) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 12 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 12) (LC.cst 0))) = packCanon 0 12 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 12) : ℤ) = (((packCanon 0 12).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 12) (LC.cst 0)) = packCanon 0 12 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 12 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 12 + t) / 8)) ((82 * 12 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 12 + t) / 8)) ((82 * 12 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 12 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 12 + t) / 8)) ((82 * 12 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 12 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 12 + t) / 8)) = (255 - (82 * 12 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_13 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 13) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 13 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 13) (LC.cst 0))) = packCanon 0 13 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 13) : ℤ) = (((packCanon 0 13).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 13) (LC.cst 0)) = packCanon 0 13 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 13 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 13 + t) / 8)) ((82 * 13 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 13 + t) / 8)) ((82 * 13 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 13 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 13 + t) / 8)) ((82 * 13 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 13 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 13 + t) / 8)) = (255 - (82 * 13 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_14 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 14) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 14 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 14) (LC.cst 0))) = packCanon 0 14 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 14) : ℤ) = (((packCanon 0 14).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 14) (LC.cst 0)) = packCanon 0 14 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 14 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 14 + t) / 8)) ((82 * 14 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 14 + t) / 8)) ((82 * 14 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 14 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 14 + t) / 8)) ((82 * 14 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 14 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 14 + t) / 8)) = (255 - (82 * 14 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_15 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 15) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 15 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 15) (LC.cst 0))) = packCanon 0 15 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 15) : ℤ) = (((packCanon 0 15).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 15) (LC.cst 0)) = packCanon 0 15 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 15 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 15 + t) / 8)) ((82 * 15 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 15 + t) / 8)) ((82 * 15 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 15 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 15 + t) / 8)) ((82 * 15 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 15 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 15 + t) / 8)) = (255 - (82 * 15 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_16 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 16) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 16 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 16) (LC.cst 0))) = packCanon 0 16 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 16) : ℤ) = (((packCanon 0 16).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 16) (LC.cst 0)) = packCanon 0 16 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 16 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 16 + t) / 8)) ((82 * 16 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 16 + t) / 8)) ((82 * 16 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 16 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 16 + t) / 8)) ((82 * 16 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 16 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 16 + t) / 8)) = (255 - (82 * 16 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_17 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 17) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 17 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 17) (LC.cst 0))) = packCanon 0 17 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 17) : ℤ) = (((packCanon 0 17).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 17) (LC.cst 0)) = packCanon 0 17 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 17 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 17 + t) / 8)) ((82 * 17 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 17 + t) / 8)) ((82 * 17 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 17 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 17 + t) / 8)) ((82 * 17 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 17 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 17 + t) / 8)) = (255 - (82 * 17 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_18 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 18) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 18 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 18) (LC.cst 0))) = packCanon 0 18 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 18) : ℤ) = (((packCanon 0 18).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 18) (LC.cst 0)) = packCanon 0 18 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 18 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 18 + t) / 8)) ((82 * 18 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 18 + t) / 8)) ((82 * 18 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 18 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 18 + t) / 8)) ((82 * 18 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 18 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 18 + t) / 8)) = (255 - (82 * 18 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_19 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 19) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 19 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 19) (LC.cst 0))) = packCanon 0 19 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 19) : ℤ) = (((packCanon 0 19).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 19) (LC.cst 0)) = packCanon 0 19 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 19 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 19 + t) / 8)) ((82 * 19 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 19 + t) / 8)) ((82 * 19 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 19 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 19 + t) / 8)) ((82 * 19 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 19 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 19 + t) / 8)) = (255 - (82 * 19 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_20 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 20) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 20 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 20) (LC.cst 0))) = packCanon 0 20 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 20) : ℤ) = (((packCanon 0 20).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 20) (LC.cst 0)) = packCanon 0 20 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 20 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 20 + t) / 8)) ((82 * 20 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 20 + t) / 8)) ((82 * 20 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 20 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 20 + t) / 8)) ((82 * 20 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 20 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 20 + t) / 8)) = (255 - (82 * 20 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_21 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 21) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 21 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 21) (LC.cst 0))) = packCanon 0 21 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 21) : ℤ) = (((packCanon 0 21).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 21) (LC.cst 0)) = packCanon 0 21 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 21 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 21 + t) / 8)) ((82 * 21 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 21 + t) / 8)) ((82 * 21 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 21 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 21 + t) / 8)) ((82 * 21 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 21 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 21 + t) / 8)) = (255 - (82 * 21 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_22 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 22) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 22 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 22) (LC.cst 0))) = packCanon 0 22 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 22) : ℤ) = (((packCanon 0 22).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 22) (LC.cst 0)) = packCanon 0 22 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 22 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 22 + t) / 8)) ((82 * 22 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 22 + t) / 8)) ((82 * 22 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 22 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 22 + t) / 8)) ((82 * 22 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 22 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 22 + t) / 8)) = (255 - (82 * 22 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_23 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 23) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 23 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 23) (LC.cst 0))) = packCanon 0 23 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 23) : ℤ) = (((packCanon 0 23).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 23) (LC.cst 0)) = packCanon 0 23 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 23 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 23 + t) / 8)) ((82 * 23 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (0 + (255 - (82 * 23 + t) / 8)) ((82 * 23 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 23 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (0 + (255 - (82 * 23 + t) / 8)) ((82 * 23 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (nBits σ) 23 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (0 + (255 - (82 * 23 + t) / 8)) = (255 - (82 * 23 + t) / 8) := by omega
  rw [hb']
  ring_nf

theorem pn_n_24 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (25 + 24) : ℤ) = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 24 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (25 + 24) (LC.cst 0))) = packCanon 0 24 := by
    decide +kernel
  have hval : (pn sq0 σ (25 + 24) : ℤ) = (((packCanon 0 24).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (25 + 24) (LC.cst 0)) = packCanon 0 24 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 24 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (0 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (if 82 * 24 + t < 2048 then (bitGLC (0 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    by_cases hj : 82 * 24 + t < 2048
    · rw [if_pos hj, if_pos hj, bitGLC_eval_eq]
      push_cast
      ring_nf
    · rw [if_neg hj, if_neg hj, mul_zero]
  rw [hsum]
  have hf : ∀ t < 82,
      ((if 82 * 24 + t < 2048 then (bitGLC (0 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0)).val ≤ 1 := by
    intro t ht
    by_cases hj : 82 * 24 + t < 2048
    · rw [if_pos hj]
      exact hb _ _ (by omega) (by omega)
    · rw [if_neg hj]
      simp
  rw [val_weighted _ hf]
  rw [limbOf_last (nBits σ) 24 80 2048 (by norm_num) (by norm_num)]
  have hL : (∑ t ∈ Finset.range 82,
        2 ^ t * ((if 82 * 24 + t < 2048 then (bitGLC (0 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0)).val)
      = ∑ t ∈ Finset.range 80,
        2 ^ t * ((if 82 * 24 + t < 2048 then (bitGLC (0 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0)).val := by
    have hsub : Finset.range 80 ⊆ Finset.range 82 := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    have hzero : ∀ t ∈ Finset.range 82, t ∉ Finset.range 80 →
        (2 ^ t * ((if 82 * 24 + t < 2048 then (bitGLC (0 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0)).val) = 0 := by
      intro t ht82 htw
      simp only [Finset.mem_range] at ht82 htw
      rw [if_neg (by omega), ZMod.val_zero, mul_zero]
    exact (Finset.sum_subset hsub hzero).symm
  rw [hL]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold nBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht80 := Finset.mem_range.mp ht
  rw [if_pos (by omega : 82 * 24 + t < 2048)]
  ring_nf

theorem pn_sig_0 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 0) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 0 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 0) (LC.cst 0))) = packCanon 256 0 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 0) : ℤ) = (((packCanon 256 0).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 0) (LC.cst 0)) = packCanon 256 0 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 0 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 0 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 0 + t) / 8)) ((82 * 0 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 0 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 0 + t) / 8)) = (256 + (255 - (82 * 0 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_1 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 1) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 1 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 1) (LC.cst 0))) = packCanon 256 1 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 1) : ℤ) = (((packCanon 256 1).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 1) (LC.cst 0)) = packCanon 256 1 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 1 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 1 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 1 + t) / 8)) ((82 * 1 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 1 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 1 + t) / 8)) = (256 + (255 - (82 * 1 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_2 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 2) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 2 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 2) (LC.cst 0))) = packCanon 256 2 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 2) : ℤ) = (((packCanon 256 2).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 2) (LC.cst 0)) = packCanon 256 2 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 2 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 2 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 2 + t) / 8)) ((82 * 2 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 2 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 2 + t) / 8)) = (256 + (255 - (82 * 2 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_3 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 3) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 3 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 3) (LC.cst 0))) = packCanon 256 3 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 3) : ℤ) = (((packCanon 256 3).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 3) (LC.cst 0)) = packCanon 256 3 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 3 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 3 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 3 + t) / 8)) ((82 * 3 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 3 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 3 + t) / 8)) = (256 + (255 - (82 * 3 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_4 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 4) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 4 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 4) (LC.cst 0))) = packCanon 256 4 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 4) : ℤ) = (((packCanon 256 4).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 4) (LC.cst 0)) = packCanon 256 4 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 4 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 4 + t) / 8)) ((82 * 4 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 4 + t) / 8)) ((82 * 4 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 4 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 4 + t) / 8)) ((82 * 4 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 4 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 4 + t) / 8)) = (256 + (255 - (82 * 4 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_5 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 5) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 5 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 5) (LC.cst 0))) = packCanon 256 5 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 5) : ℤ) = (((packCanon 256 5).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 5) (LC.cst 0)) = packCanon 256 5 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 5 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 5 + t) / 8)) ((82 * 5 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 5 + t) / 8)) ((82 * 5 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 5 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 5 + t) / 8)) ((82 * 5 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 5 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 5 + t) / 8)) = (256 + (255 - (82 * 5 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_6 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 6) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 6 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 6) (LC.cst 0))) = packCanon 256 6 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 6) : ℤ) = (((packCanon 256 6).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 6) (LC.cst 0)) = packCanon 256 6 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 6 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 6 + t) / 8)) ((82 * 6 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 6 + t) / 8)) ((82 * 6 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 6 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 6 + t) / 8)) ((82 * 6 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 6 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 6 + t) / 8)) = (256 + (255 - (82 * 6 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_7 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 7) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 7 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 7) (LC.cst 0))) = packCanon 256 7 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 7) : ℤ) = (((packCanon 256 7).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 7) (LC.cst 0)) = packCanon 256 7 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 7 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 7 + t) / 8)) ((82 * 7 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 7 + t) / 8)) ((82 * 7 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 7 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 7 + t) / 8)) ((82 * 7 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 7 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 7 + t) / 8)) = (256 + (255 - (82 * 7 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_8 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 8) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 8 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 8) (LC.cst 0))) = packCanon 256 8 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 8) : ℤ) = (((packCanon 256 8).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 8) (LC.cst 0)) = packCanon 256 8 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 8 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 8 + t) / 8)) ((82 * 8 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 8 + t) / 8)) ((82 * 8 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 8 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 8 + t) / 8)) ((82 * 8 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 8 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 8 + t) / 8)) = (256 + (255 - (82 * 8 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_9 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 9) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 9 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 9) (LC.cst 0))) = packCanon 256 9 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 9) : ℤ) = (((packCanon 256 9).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 9) (LC.cst 0)) = packCanon 256 9 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 9 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 9 + t) / 8)) ((82 * 9 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 9 + t) / 8)) ((82 * 9 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 9 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 9 + t) / 8)) ((82 * 9 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 9 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 9 + t) / 8)) = (256 + (255 - (82 * 9 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_10 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 10) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 10 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 10) (LC.cst 0))) = packCanon 256 10 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 10) : ℤ) = (((packCanon 256 10).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 10) (LC.cst 0)) = packCanon 256 10 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 10 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 10 + t) / 8)) ((82 * 10 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 10 + t) / 8)) ((82 * 10 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 10 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 10 + t) / 8)) ((82 * 10 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 10 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 10 + t) / 8)) = (256 + (255 - (82 * 10 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_11 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 11) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 11 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 11) (LC.cst 0))) = packCanon 256 11 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 11) : ℤ) = (((packCanon 256 11).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 11) (LC.cst 0)) = packCanon 256 11 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 11 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 11 + t) / 8)) ((82 * 11 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 11 + t) / 8)) ((82 * 11 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 11 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 11 + t) / 8)) ((82 * 11 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 11 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 11 + t) / 8)) = (256 + (255 - (82 * 11 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_12 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 12) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 12 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 12) (LC.cst 0))) = packCanon 256 12 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 12) : ℤ) = (((packCanon 256 12).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 12) (LC.cst 0)) = packCanon 256 12 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 12 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 12 + t) / 8)) ((82 * 12 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 12 + t) / 8)) ((82 * 12 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 12 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 12 + t) / 8)) ((82 * 12 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 12 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 12 + t) / 8)) = (256 + (255 - (82 * 12 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_13 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 13) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 13 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 13) (LC.cst 0))) = packCanon 256 13 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 13) : ℤ) = (((packCanon 256 13).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 13) (LC.cst 0)) = packCanon 256 13 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 13 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 13 + t) / 8)) ((82 * 13 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 13 + t) / 8)) ((82 * 13 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 13 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 13 + t) / 8)) ((82 * 13 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 13 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 13 + t) / 8)) = (256 + (255 - (82 * 13 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_14 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 14) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 14 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 14) (LC.cst 0))) = packCanon 256 14 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 14) : ℤ) = (((packCanon 256 14).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 14) (LC.cst 0)) = packCanon 256 14 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 14 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 14 + t) / 8)) ((82 * 14 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 14 + t) / 8)) ((82 * 14 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 14 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 14 + t) / 8)) ((82 * 14 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 14 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 14 + t) / 8)) = (256 + (255 - (82 * 14 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_15 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 15) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 15 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 15) (LC.cst 0))) = packCanon 256 15 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 15) : ℤ) = (((packCanon 256 15).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 15) (LC.cst 0)) = packCanon 256 15 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 15 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 15 + t) / 8)) ((82 * 15 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 15 + t) / 8)) ((82 * 15 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 15 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 15 + t) / 8)) ((82 * 15 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 15 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 15 + t) / 8)) = (256 + (255 - (82 * 15 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_16 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 16) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 16 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 16) (LC.cst 0))) = packCanon 256 16 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 16) : ℤ) = (((packCanon 256 16).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 16) (LC.cst 0)) = packCanon 256 16 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 16 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 16 + t) / 8)) ((82 * 16 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 16 + t) / 8)) ((82 * 16 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 16 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 16 + t) / 8)) ((82 * 16 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 16 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 16 + t) / 8)) = (256 + (255 - (82 * 16 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_17 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 17) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 17 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 17) (LC.cst 0))) = packCanon 256 17 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 17) : ℤ) = (((packCanon 256 17).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 17) (LC.cst 0)) = packCanon 256 17 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 17 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 17 + t) / 8)) ((82 * 17 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 17 + t) / 8)) ((82 * 17 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 17 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 17 + t) / 8)) ((82 * 17 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 17 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 17 + t) / 8)) = (256 + (255 - (82 * 17 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_18 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 18) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 18 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 18) (LC.cst 0))) = packCanon 256 18 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 18) : ℤ) = (((packCanon 256 18).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 18) (LC.cst 0)) = packCanon 256 18 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 18 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 18 + t) / 8)) ((82 * 18 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 18 + t) / 8)) ((82 * 18 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 18 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 18 + t) / 8)) ((82 * 18 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 18 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 18 + t) / 8)) = (256 + (255 - (82 * 18 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_19 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 19) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 19 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 19) (LC.cst 0))) = packCanon 256 19 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 19) : ℤ) = (((packCanon 256 19).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 19) (LC.cst 0)) = packCanon 256 19 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 19 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 19 + t) / 8)) ((82 * 19 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 19 + t) / 8)) ((82 * 19 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 19 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 19 + t) / 8)) ((82 * 19 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 19 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 19 + t) / 8)) = (256 + (255 - (82 * 19 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_20 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 20) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 20 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 20) (LC.cst 0))) = packCanon 256 20 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 20) : ℤ) = (((packCanon 256 20).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 20) (LC.cst 0)) = packCanon 256 20 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 20 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 20 + t) / 8)) ((82 * 20 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 20 + t) / 8)) ((82 * 20 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 20 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 20 + t) / 8)) ((82 * 20 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 20 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 20 + t) / 8)) = (256 + (255 - (82 * 20 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_21 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 21) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 21 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 21) (LC.cst 0))) = packCanon 256 21 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 21) : ℤ) = (((packCanon 256 21).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 21) (LC.cst 0)) = packCanon 256 21 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 21 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 21 + t) / 8)) ((82 * 21 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 21 + t) / 8)) ((82 * 21 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 21 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 21 + t) / 8)) ((82 * 21 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 21 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 21 + t) / 8)) = (256 + (255 - (82 * 21 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_22 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 22) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 22 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 22) (LC.cst 0))) = packCanon 256 22 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 22) : ℤ) = (((packCanon 256 22).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 22) (LC.cst 0)) = packCanon 256 22 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 22 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 22 + t) / 8)) ((82 * 22 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 22 + t) / 8)) ((82 * 22 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 22 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 22 + t) / 8)) ((82 * 22 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 22 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 22 + t) / 8)) = (256 + (255 - (82 * 22 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_23 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 23) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 23 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 23) (LC.cst 0))) = packCanon 256 23 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 23) : ℤ) = (((packCanon 256 23).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 23) (LC.cst 0)) = packCanon 256 23 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 23 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 23 + t) / 8)) ((82 * 23 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (bitGLC (256 + (255 - (82 * 23 + t) / 8)) ((82 * 23 + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega : 82 * 23 + t < 2048)]
    rw [bitGLC_eval_eq]
    push_cast
    ring_nf
  rw [hsum]
  have hf : ∀ t < 82,
      ((bitGLC (256 + (255 - (82 * 23 + t) / 8)) ((82 * 23 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    exact hb _ _ (by omega) (by omega)
  rw [val_weighted _ hf]
  rw [limbOf_full (sigBits σ) 23 2048 (by norm_num)]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have hb' : (256 + (255 - (82 * 23 + t) / 8)) = (256 + (255 - (82 * 23 + t) / 8)) := by omega
  rw [hb']
  ring_nf

theorem pn_sig_24 (σ : ℕ → F) (h : Sat circuit σ) :
    (pn sq0 σ (0 + 24) : ℤ) = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 24 := by
  have hb := hbit σ h
  have hplug : (ZLC.toF ((callAt 548).plugs.getD (0 + 24) (LC.cst 0))) = packCanon 256 24 := by
    decide +kernel
  have hval : (pn sq0 σ (0 + 24) : ℤ) = (((packCanon 256 24).eval σ).val : ℤ) := by
    simp only [pn, Call.lift, Call.env, sq0]
    rw [show ZLC.toF ((callAt 548).plugs.getD (0 + 24) (LC.cst 0)) = packCanon 256 24 from hplug]
  rw [hval, packCanon_eval, eval_packTerms]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 24 + t < 2048 then
          (↑(2 ^ t) : F) * ((bitTerms (256 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).map
              fun term => term.1 * σ term.2).sum
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (if 82 * 24 + t < 2048 then (bitGLC (256 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    by_cases hj : 82 * 24 + t < 2048
    · rw [if_pos hj, if_pos hj, bitGLC_eval_eq]
      push_cast
      ring_nf
    · rw [if_neg hj, if_neg hj, mul_zero]
  rw [hsum]
  have hf : ∀ t < 82,
      ((if 82 * 24 + t < 2048 then (bitGLC (256 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0)).val ≤ 1 := by
    intro t ht
    by_cases hj : 82 * 24 + t < 2048
    · rw [if_pos hj]
      exact hb _ _ (by omega) (by omega)
    · rw [if_neg hj]
      simp
  rw [val_weighted _ hf]
  rw [limbOf_last (sigBits σ) 24 80 2048 (by norm_num) (by norm_num)]
  have hL : (∑ t ∈ Finset.range 82,
        2 ^ t * ((if 82 * 24 + t < 2048 then (bitGLC (256 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0)).val)
      = ∑ t ∈ Finset.range 80,
        2 ^ t * ((if 82 * 24 + t < 2048 then (bitGLC (256 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0)).val := by
    have hsub : Finset.range 80 ⊆ Finset.range 82 := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    have hzero : ∀ t ∈ Finset.range 82, t ∉ Finset.range 80 →
        (2 ^ t * ((if 82 * 24 + t < 2048 then (bitGLC (256 + (255 - (82 * 24 + t) / 8)) ((82 * 24 + t) % 8)).eval σ else 0)).val) = 0 := by
      intro t ht82 htw
      simp only [Finset.mem_range] at ht82 htw
      rw [if_neg (by omega), ZMod.val_zero, mul_zero]
    exact (Finset.sum_subset hsub hzero).symm
  rw [hL]
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold sigBits
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht80 := Finset.mem_range.mp ht
  rw [if_pos (by omega : 82 * 24 + t < 2048)]
  ring_nf

theorem chainN_limb (σ : ℕ → F) (h : Sat circuit σ) :
    chainN σ = ∑ q ∈ Finset.range 25, Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 q * W ^ q := by
  rw [chainN]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq25 := Finset.mem_range.mp hq
  interval_cases q
  · change pv sq0 σ (25 + 0) * W ^ 0 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 0 * W ^ 0
    rw [pv_eq_pn, pn_n_0 σ h]
  · change pv sq0 σ (25 + 1) * W ^ 1 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 1 * W ^ 1
    rw [pv_eq_pn, pn_n_1 σ h]
  · change pv sq0 σ (25 + 2) * W ^ 2 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 2 * W ^ 2
    rw [pv_eq_pn, pn_n_2 σ h]
  · change pv sq0 σ (25 + 3) * W ^ 3 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 3 * W ^ 3
    rw [pv_eq_pn, pn_n_3 σ h]
  · change pv sq0 σ (25 + 4) * W ^ 4 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 4 * W ^ 4
    rw [pv_eq_pn, pn_n_4 σ h]
  · change pv sq0 σ (25 + 5) * W ^ 5 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 5 * W ^ 5
    rw [pv_eq_pn, pn_n_5 σ h]
  · change pv sq0 σ (25 + 6) * W ^ 6 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 6 * W ^ 6
    rw [pv_eq_pn, pn_n_6 σ h]
  · change pv sq0 σ (25 + 7) * W ^ 7 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 7 * W ^ 7
    rw [pv_eq_pn, pn_n_7 σ h]
  · change pv sq0 σ (25 + 8) * W ^ 8 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 8 * W ^ 8
    rw [pv_eq_pn, pn_n_8 σ h]
  · change pv sq0 σ (25 + 9) * W ^ 9 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 9 * W ^ 9
    rw [pv_eq_pn, pn_n_9 σ h]
  · change pv sq0 σ (25 + 10) * W ^ 10 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 10 * W ^ 10
    rw [pv_eq_pn, pn_n_10 σ h]
  · change pv sq0 σ (25 + 11) * W ^ 11 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 11 * W ^ 11
    rw [pv_eq_pn, pn_n_11 σ h]
  · change pv sq0 σ (25 + 12) * W ^ 12 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 12 * W ^ 12
    rw [pv_eq_pn, pn_n_12 σ h]
  · change pv sq0 σ (25 + 13) * W ^ 13 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 13 * W ^ 13
    rw [pv_eq_pn, pn_n_13 σ h]
  · change pv sq0 σ (25 + 14) * W ^ 14 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 14 * W ^ 14
    rw [pv_eq_pn, pn_n_14 σ h]
  · change pv sq0 σ (25 + 15) * W ^ 15 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 15 * W ^ 15
    rw [pv_eq_pn, pn_n_15 σ h]
  · change pv sq0 σ (25 + 16) * W ^ 16 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 16 * W ^ 16
    rw [pv_eq_pn, pn_n_16 σ h]
  · change pv sq0 σ (25 + 17) * W ^ 17 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 17 * W ^ 17
    rw [pv_eq_pn, pn_n_17 σ h]
  · change pv sq0 σ (25 + 18) * W ^ 18 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 18 * W ^ 18
    rw [pv_eq_pn, pn_n_18 σ h]
  · change pv sq0 σ (25 + 19) * W ^ 19 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 19 * W ^ 19
    rw [pv_eq_pn, pn_n_19 σ h]
  · change pv sq0 σ (25 + 20) * W ^ 20 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 20 * W ^ 20
    rw [pv_eq_pn, pn_n_20 σ h]
  · change pv sq0 σ (25 + 21) * W ^ 21 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 21 * W ^ 21
    rw [pv_eq_pn, pn_n_21 σ h]
  · change pv sq0 σ (25 + 22) * W ^ 22 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 22 * W ^ 22
    rw [pv_eq_pn, pn_n_22 σ h]
  · change pv sq0 σ (25 + 23) * W ^ 23 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 23 * W ^ 23
    rw [pv_eq_pn, pn_n_23 σ h]
  · change pv sq0 σ (25 + 24) * W ^ 24 = Xark.Rsa.Bytes.limbOf (nBits σ) 82 2048 24 * W ^ 24
    rw [pv_eq_pn, pn_n_24 σ h]

theorem chainSig_limb (σ : ℕ → F) (h : Sat circuit σ) :
    val (limb sq0 σ 0) = ∑ q ∈ Finset.range 25, Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 q * W ^ q := by
  rw [val]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq25 := Finset.mem_range.mp hq
  interval_cases q
  · change pv sq0 σ (0 + 0) * W ^ 0 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 0 * W ^ 0
    rw [pv_eq_pn, pn_sig_0 σ h]
  · change pv sq0 σ (0 + 1) * W ^ 1 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 1 * W ^ 1
    rw [pv_eq_pn, pn_sig_1 σ h]
  · change pv sq0 σ (0 + 2) * W ^ 2 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 2 * W ^ 2
    rw [pv_eq_pn, pn_sig_2 σ h]
  · change pv sq0 σ (0 + 3) * W ^ 3 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 3 * W ^ 3
    rw [pv_eq_pn, pn_sig_3 σ h]
  · change pv sq0 σ (0 + 4) * W ^ 4 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 4 * W ^ 4
    rw [pv_eq_pn, pn_sig_4 σ h]
  · change pv sq0 σ (0 + 5) * W ^ 5 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 5 * W ^ 5
    rw [pv_eq_pn, pn_sig_5 σ h]
  · change pv sq0 σ (0 + 6) * W ^ 6 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 6 * W ^ 6
    rw [pv_eq_pn, pn_sig_6 σ h]
  · change pv sq0 σ (0 + 7) * W ^ 7 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 7 * W ^ 7
    rw [pv_eq_pn, pn_sig_7 σ h]
  · change pv sq0 σ (0 + 8) * W ^ 8 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 8 * W ^ 8
    rw [pv_eq_pn, pn_sig_8 σ h]
  · change pv sq0 σ (0 + 9) * W ^ 9 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 9 * W ^ 9
    rw [pv_eq_pn, pn_sig_9 σ h]
  · change pv sq0 σ (0 + 10) * W ^ 10 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 10 * W ^ 10
    rw [pv_eq_pn, pn_sig_10 σ h]
  · change pv sq0 σ (0 + 11) * W ^ 11 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 11 * W ^ 11
    rw [pv_eq_pn, pn_sig_11 σ h]
  · change pv sq0 σ (0 + 12) * W ^ 12 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 12 * W ^ 12
    rw [pv_eq_pn, pn_sig_12 σ h]
  · change pv sq0 σ (0 + 13) * W ^ 13 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 13 * W ^ 13
    rw [pv_eq_pn, pn_sig_13 σ h]
  · change pv sq0 σ (0 + 14) * W ^ 14 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 14 * W ^ 14
    rw [pv_eq_pn, pn_sig_14 σ h]
  · change pv sq0 σ (0 + 15) * W ^ 15 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 15 * W ^ 15
    rw [pv_eq_pn, pn_sig_15 σ h]
  · change pv sq0 σ (0 + 16) * W ^ 16 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 16 * W ^ 16
    rw [pv_eq_pn, pn_sig_16 σ h]
  · change pv sq0 σ (0 + 17) * W ^ 17 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 17 * W ^ 17
    rw [pv_eq_pn, pn_sig_17 σ h]
  · change pv sq0 σ (0 + 18) * W ^ 18 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 18 * W ^ 18
    rw [pv_eq_pn, pn_sig_18 σ h]
  · change pv sq0 σ (0 + 19) * W ^ 19 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 19 * W ^ 19
    rw [pv_eq_pn, pn_sig_19 σ h]
  · change pv sq0 σ (0 + 20) * W ^ 20 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 20 * W ^ 20
    rw [pv_eq_pn, pn_sig_20 σ h]
  · change pv sq0 σ (0 + 21) * W ^ 21 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 21 * W ^ 21
    rw [pv_eq_pn, pn_sig_21 σ h]
  · change pv sq0 σ (0 + 22) * W ^ 22 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 22 * W ^ 22
    rw [pv_eq_pn, pn_sig_22 σ h]
  · change pv sq0 σ (0 + 23) * W ^ 23 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 23 * W ^ 23
    rw [pv_eq_pn, pn_sig_23 σ h]
  · change pv sq0 σ (0 + 24) * W ^ 24 = Xark.Rsa.Bytes.limbOf (sigBits σ) 82 2048 24 * W ^ 24
    rw [pv_eq_pn, pn_sig_24 σ h]

end Xark.Circuits.Rsa2048
