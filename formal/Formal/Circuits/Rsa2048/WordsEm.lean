/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.WordsCong
import Formal.ToBits

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The words EM bound: the digest bits are bits

The terminal `grouped_columns` call's `r` array is the `sha256_em_bits_82` output, a
weighted sum of the 256 digest bits. Those bits are the outputs of the 32 `to_bits`
calls at s2..s33; each output is `bitOf` of a byte, hence `0`/`1`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Templates.Add32 (IsBit)

/-- The 8 outputs of a `to_bits`-style call are bits. -/
theorem tobits_out_isBit (σ' : TVar → F) (h : Xark.Templates.ToBits.template.Sat σ')
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs σ').getD t 0) := by
  have hs := Xark.Templates.ToBits.soundness σ' h
  rw [Xark.Templates.ToBits.Spec] at hs
  obtain ⟨hlt, houts⟩ := hs
  have hval : (Xark.Templates.ToBits.template.outs σ').getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins σ').getD 0 0) t := by
    rw [houts]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
    rfl
  rw [hval, Xark.Template.bitOf]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem w_tobits_out_isBit_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 2).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 2 (wcallAt 2) rfl (by decide)
  rw [show (wcallAt 2).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 2).lift σ) hsat ht

theorem w_tobits_out_isBit_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 3).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 3 (wcallAt 3) rfl (by decide)
  rw [show (wcallAt 3).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 3).lift σ) hsat ht

theorem w_tobits_out_isBit_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 4).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 4 (wcallAt 4) rfl (by decide)
  rw [show (wcallAt 4).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 4).lift σ) hsat ht

theorem w_tobits_out_isBit_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 5).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 5 (wcallAt 5) rfl (by decide)
  rw [show (wcallAt 5).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 5).lift σ) hsat ht

theorem w_tobits_out_isBit_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 6).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 6 (wcallAt 6) rfl (by decide)
  rw [show (wcallAt 6).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 6).lift σ) hsat ht

theorem w_tobits_out_isBit_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 7).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 7 (wcallAt 7) rfl (by decide)
  rw [show (wcallAt 7).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 7).lift σ) hsat ht

theorem w_tobits_out_isBit_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 8).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 8 (wcallAt 8) rfl (by decide)
  rw [show (wcallAt 8).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 8).lift σ) hsat ht

theorem w_tobits_out_isBit_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 9).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 9 (wcallAt 9) rfl (by decide)
  rw [show (wcallAt 9).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 9).lift σ) hsat ht

theorem w_tobits_out_isBit_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 10).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 10 (wcallAt 10) rfl (by decide)
  rw [show (wcallAt 10).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 10).lift σ) hsat ht

theorem w_tobits_out_isBit_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 11).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 11 (wcallAt 11) rfl (by decide)
  rw [show (wcallAt 11).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 11).lift σ) hsat ht

theorem w_tobits_out_isBit_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 12).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 12 (wcallAt 12) rfl (by decide)
  rw [show (wcallAt 12).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 12).lift σ) hsat ht

theorem w_tobits_out_isBit_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 13).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 13 (wcallAt 13) rfl (by decide)
  rw [show (wcallAt 13).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 13).lift σ) hsat ht

theorem w_tobits_out_isBit_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 14).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 14 (wcallAt 14) rfl (by decide)
  rw [show (wcallAt 14).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 14).lift σ) hsat ht

theorem w_tobits_out_isBit_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 15).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 15 (wcallAt 15) rfl (by decide)
  rw [show (wcallAt 15).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 15).lift σ) hsat ht

theorem w_tobits_out_isBit_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 16).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 16 (wcallAt 16) rfl (by decide)
  rw [show (wcallAt 16).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 16).lift σ) hsat ht

theorem w_tobits_out_isBit_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 17).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 17 (wcallAt 17) rfl (by decide)
  rw [show (wcallAt 17).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 17).lift σ) hsat ht

theorem w_tobits_out_isBit_16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 18).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 18 (wcallAt 18) rfl (by decide)
  rw [show (wcallAt 18).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 18).lift σ) hsat ht

theorem w_tobits_out_isBit_17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 19).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 19 (wcallAt 19) rfl (by decide)
  rw [show (wcallAt 19).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 19).lift σ) hsat ht

theorem w_tobits_out_isBit_18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 20).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 20 (wcallAt 20) rfl (by decide)
  rw [show (wcallAt 20).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 20).lift σ) hsat ht

theorem w_tobits_out_isBit_19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 21).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 21 (wcallAt 21) rfl (by decide)
  rw [show (wcallAt 21).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 21).lift σ) hsat ht

theorem w_tobits_out_isBit_20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 22).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 22 (wcallAt 22) rfl (by decide)
  rw [show (wcallAt 22).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 22).lift σ) hsat ht

theorem w_tobits_out_isBit_21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 23).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 23 (wcallAt 23) rfl (by decide)
  rw [show (wcallAt 23).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 23).lift σ) hsat ht

theorem w_tobits_out_isBit_22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 24).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 24 (wcallAt 24) rfl (by decide)
  rw [show (wcallAt 24).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 24).lift σ) hsat ht

theorem w_tobits_out_isBit_23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 25).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 25 (wcallAt 25) rfl (by decide)
  rw [show (wcallAt 25).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 25).lift σ) hsat ht

theorem w_tobits_out_isBit_24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 26).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 26 (wcallAt 26) rfl (by decide)
  rw [show (wcallAt 26).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 26).lift σ) hsat ht

theorem w_tobits_out_isBit_25 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 27).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 27 (wcallAt 27) rfl (by decide)
  rw [show (wcallAt 27).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 27).lift σ) hsat ht

theorem w_tobits_out_isBit_26 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 28).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 28 (wcallAt 28) rfl (by decide)
  rw [show (wcallAt 28).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 28).lift σ) hsat ht

theorem w_tobits_out_isBit_27 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 29).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 29 (wcallAt 29) rfl (by decide)
  rw [show (wcallAt 29).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 29).lift σ) hsat ht

theorem w_tobits_out_isBit_28 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 30).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 30 (wcallAt 30) rfl (by decide)
  rw [show (wcallAt 30).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 30).lift σ) hsat ht

theorem w_tobits_out_isBit_29 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 31).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 31 (wcallAt 31) rfl (by decide)
  rw [show (wcallAt 31).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 31).lift σ) hsat ht

theorem w_tobits_out_isBit_30 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 32).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 32 (wcallAt 32) rfl (by decide)
  rw [show (wcallAt 32).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 32).lift σ) hsat ht

theorem w_tobits_out_isBit_31 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    {t : ℕ} (ht : t < 8) :
    IsBit ((Xark.Templates.ToBits.template.outs ((wcallAt 33).lift σ)).getD t 0) := by
  have hsat := wcall_sat_of h 33 (wcallAt 33) rfl (by decide)
  rw [show (wcallAt 33).t = Xark.Templates.ToBits.template from by decide] at hsat
  exact tobits_out_isBit ((wcallAt 33).lift σ) hsat ht

end Xark.Circuits.Rsa2048
