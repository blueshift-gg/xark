/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.WordsCong
import Formal.Circuits.Rsa2048.PackBoundW
import Formal.ToBits

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The words EM bound

The terminal `grouped_columns` call's `r` array is the `sha256_em_bits_82` output, a
weighted sum of the 256 digest bits. Those bits are the outputs of the 32 `to_bits`
calls at s2..s33; each output is `bitOf` of a byte, hence `0`/`1`. The gadget emits no
rows, so the words circuit carries its 25 output limbs inline (plugs 100..124):
`EM82_CONST`'s limb plus the digest's bits at weights `2^t`.

`wbitTerms`/`wemTerms` name those combinations, `wem_plug` matches the exported plugs
against them (`decide +kernel` on the normalized terms), `wbit_le_one` turns
`ToBits.soundness` into "each bit is 0 or 1", and `weighted_ltW`/`val_weightedW` bound
the weighted sum: every limb is below `2^82` (`w_hEm`). That is the words path's
analogue of the byte path's `EmBits`/`PackBound`, and it leaves `w_verify_wide`
unconditional.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
open Xark.Templates.Add32 (IsBit)

/-! ## The `to_bits` calls' outputs are bits -/

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

/-! ## The digest bytes' bits -/

/-- The `to_bits` call for digest byte `b` starts its witnesses at `8294 + 7b`. -/
def wbitBase (b : ℕ) : ℕ := 8294 + 7 * b

/-- Digest byte `b`'s bit `tb`: bit 0 is the affine output (`byte − Σ 2^{s+1}·w_s`), bits 1..7 the witnesses. -/
def wbitTerms (b tb : ℕ) : List (F × ℕ) :=
  if tb = 0 then
    (1, 8262 + b) :: (List.range 7).map (fun s => (-(↑(2 ^ (s + 1)) : F), wbitBase b + s))
  else [(1, wbitBase b + (tb - 1))]

/-- The same bit as a zero-constant combination. -/
def wbitGLC (b tb : ℕ) : GLC := ⟨0, wbitTerms b tb⟩

/-! ## The encoded message's limbs -/


/-- The encoded message's limb `q`: `EM82_CONST`'s limb plus the digest's bits at `2^t`. -/
def wemTerms (q : ℕ) : List (F × ℕ) :=
  (List.range 82).flatMap fun t =>
    let j := 82 * q + t
    if j < 256 then
      let b := 31 - j / 8
      let tb := j % 8
      (wbitTerms b tb).map fun term => ((((2 ^ t : ℕ) : F)) * term.1, term.2)
    else []

/-- The limb in canonical form, so the exported plug is compared by `decide` rather than
by normalizing the huge plug term inside a rewrite. -/
def wemCanon (q : ℕ) : GLC :=
  ⟨((Xark.Rsa.Em.em82 q : ℤ) : F), Xark.R1cs.normTerms leNat (wemTerms q)⟩

/-- **The exported plug is the model.** -/
theorem wem_plug (q : ℕ) (hq : q < 25) :
    (ZLC.toF ((wcallAt 88).plugs.getD (100 + q) (LC.cst 0))) = wemCanon q := by
  interval_cases q <;> decide +kernel

/-- The canonical limb's value: the constant frame plus the terms. -/
theorem wemCanon_eval (q : ℕ) (σ : ℕ → F) :
    (wemCanon q).eval σ
      = ((Xark.Rsa.Em.em82 q : ℤ) : F) + ((⟨0, wemTerms q⟩ : GLC).eval σ) := by
  simp only [wemCanon, LC.eval, zero_add]
  congr 1
  exact Xark.R1cs.eval_normTerms leNat (wemTerms q) σ

/-- The terms' value: a `2^t`-weighted sum of the digest bits. -/
theorem eval_wemTerms (q : ℕ) (σ : ℕ → F) :
    ((⟨0, wemTerms q⟩ : GLC).eval σ)
      = ∑ t ∈ Finset.range 82,
          if 82 * q + t < 256 then
            ((2 ^ t : ℕ) : F) * (wbitGLC (31 - (82 * q + t) / 8) ((82 * q + t) % 8)).eval σ
          else 0 := by
  simp only [wemTerms, LC.eval, zero_add]
  rw [sum_flatMapF, sum_rangeF]
  refine Finset.sum_congr rfl fun t ht => ?_
  by_cases hj : 82 * q + t < 256
  · simp only [hj, if_pos]
    rw [List.map_map]
    simp only [wbitGLC, zero_add]
    exact sum_map_scale _ _ σ
  · simp only [hj, if_false, List.map_nil, List.sum_nil]

/-- **The limb as a weighted sum of the digest bits.** -/
theorem wem_eval (q : ℕ) (σ : ℕ → F) :
    (wemCanon q).eval σ
      = ((Xark.Rsa.Em.em82 q : ℤ) : F) + ∑ t ∈ Finset.range 82,
          if 82 * q + t < 256 then
            ((2 ^ t : ℕ) : F) * (wbitGLC (31 - (82 * q + t) / 8) ((82 * q + t) % 8)).eval σ
          else 0 := by
  rw [wemCanon_eval, eval_wemTerms]


/-! ## The bits are bits, so a limb is below `2^82` -/


/-- A `to_bits` call's output `tb` as a combination over the circuit's variables. -/
def wbitOut (c : Call) (tb : ℕ) : GLC :=
  ((c.t.outputs.getD tb (LC.cst 0)).bind c.env)

/-- The output combination's value is the template's output. -/
theorem wbitOut_eval (c : Call) (tb : ℕ) (σ : ℕ → F) :
    (wbitOut c tb).eval σ = (c.t.outs (c.lift σ)).getD tb 0 := by
  simp only [wbitOut, Call.outs, LC.eval_bind]
  rw [getD_map_eq _ (fun l => LC.eval l (fun v => LC.eval (c.env v) σ)) tb (LC.cst 0) 0
    (by simp [LC.cst, LC.eval])]

/-- With the plug and witness base read off the call, the bit is that output. -/
theorem wbitGLC_eq_wbitOut (c : Call) (b tb : ℕ)
    (hb0 : c.t = Xark.Templates.ToBits.template)
    (hplugs : c.plugs = [(Xark.R1cs.LC.var (8262 + b) : Xark.Circuit.ZLC)])
    (hbase : c.base = wbitBase b) (htb : tb < 8) :
    wbitGLC b tb = wbitOut c tb := by
  interval_cases tb <;>
    simp [wbitGLC, wbitTerms, wbitBase, wbitOut, Call.env, hplugs, hbase, hb0,
      Xark.Templates.ToBits.template, ZLC.toF, LC.bind, LC.var, LC.cst] <;>
    try rfl

/-- **A `to_bits` output is 0 or 1**: the contract's bits are `bitOf`, hence bits. -/
theorem wbit_le_one_at (σ : ℕ → F) (c : Call) (b tb : ℕ)
    (hsat : c.t.Sat (c.lift σ))
    (hb0 : c.t = Xark.Templates.ToBits.template)
    (hplugs : c.plugs = [(Xark.R1cs.LC.var (8262 + b) : Xark.Circuit.ZLC)])
    (hbase : c.base = wbitBase b) (htb : tb < 8) :
    ((wbitGLC b tb).eval σ).val ≤ 1 := by
  have glc : (wbitGLC b tb).eval σ
      = (Xark.Templates.ToBits.template.outs (c.lift σ)).getD tb 0 := by
    rw [wbitGLC_eq_wbitOut c b tb hb0 hplugs hbase htb, wbitOut_eval, hb0]
  rw [hb0] at hsat
  have hspec := Xark.Templates.ToBits.soundness (c.lift σ) hsat
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs (c.lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins (c.lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

/-- Every digest bit the words circuit reads is 0 or 1 (one wrapper per byte). -/
theorem wbit_le_one (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) (b tb : ℕ)
    (hb : b < 32) (htb : tb < 8) :
    ((wbitGLC b tb).eval σ).val ≤ 1 := by
  interval_cases b
  · exact wbit_le_one_at σ (wcallAt 2) 0 tb (wcall_sat_of h 2 (wcallAt 2) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 3) 1 tb (wcall_sat_of h 3 (wcallAt 3) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 4) 2 tb (wcall_sat_of h 4 (wcallAt 4) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 5) 3 tb (wcall_sat_of h 5 (wcallAt 5) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 6) 4 tb (wcall_sat_of h 6 (wcallAt 6) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 7) 5 tb (wcall_sat_of h 7 (wcallAt 7) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 8) 6 tb (wcall_sat_of h 8 (wcallAt 8) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 9) 7 tb (wcall_sat_of h 9 (wcallAt 9) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 10) 8 tb (wcall_sat_of h 10 (wcallAt 10) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 11) 9 tb (wcall_sat_of h 11 (wcallAt 11) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 12) 10 tb (wcall_sat_of h 12 (wcallAt 12) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 13) 11 tb (wcall_sat_of h 13 (wcallAt 13) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 14) 12 tb (wcall_sat_of h 14 (wcallAt 14) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 15) 13 tb (wcall_sat_of h 15 (wcallAt 15) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 16) 14 tb (wcall_sat_of h 16 (wcallAt 16) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 17) 15 tb (wcall_sat_of h 17 (wcallAt 17) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 18) 16 tb (wcall_sat_of h 18 (wcallAt 18) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 19) 17 tb (wcall_sat_of h 19 (wcallAt 19) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 20) 18 tb (wcall_sat_of h 20 (wcallAt 20) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 21) 19 tb (wcall_sat_of h 21 (wcallAt 21) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 22) 20 tb (wcall_sat_of h 22 (wcallAt 22) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 23) 21 tb (wcall_sat_of h 23 (wcallAt 23) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 24) 22 tb (wcall_sat_of h 24 (wcallAt 24) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 25) 23 tb (wcall_sat_of h 25 (wcallAt 25) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 26) 24 tb (wcall_sat_of h 26 (wcallAt 26) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 27) 25 tb (wcall_sat_of h 27 (wcallAt 27) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 28) 26 tb (wcall_sat_of h 28 (wcallAt 28) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 29) 27 tb (wcall_sat_of h 29 (wcallAt 29) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 30) 28 tb (wcall_sat_of h 30 (wcallAt 30) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 31) 29 tb (wcall_sat_of h 31 (wcallAt 31) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 32) 30 tb (wcall_sat_of h 32 (wcallAt 32) rfl (by decide)) rfl rfl rfl htb
  · exact wbit_le_one_at σ (wcallAt 33) 31 tb (wcall_sat_of h 33 (wcallAt 33) rfl (by decide)) rfl rfl rfl htb


/-- A weighted sum of `w` bits plus a constant `k` below `2^82` is below `2^82`. -/
theorem wem_bound_of (w k : ℕ) (f : ℕ → F) (q : ℕ) (σ : ℕ → F)
    (hw : w ≤ 82) (hf : ∀ t < w, (f t).val ≤ 1)
    (heval : (wemCanon q).eval σ
      = ((Xark.Rsa.Em.em82 q : ℤ) : F) + ∑ t ∈ Finset.range w, ((2 ^ t : ℕ) : F) * f t)
    (hcval : ((Xark.Rsa.Em.em82 q : ℤ) : F).val = k) (hk : k + 2 ^ w ≤ 2 ^ 82) :
    ((wemCanon q).eval σ).val < 2 ^ 82 := by
  rw [heval]
  have hSval := val_weightedW w hw f hf
  have hSlt := weighted_ltW w f hf
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ 82 := Nat.pow_le_pow_right (by norm_num) hw
  have hr : (2 : ℕ) ^ 82 < r := Xark.Templates.ToBits.two_pow_lt_r' (by norm_num)
  have hlt : k + (∑ t ∈ Finset.range w, 2 ^ t * (f t).val) < r := by omega
  rw [ZMod.val_add, hcval, hSval, Nat.mod_eq_of_lt hlt]
  omega

/-- A `range 82` sum whose guard holds exactly below `w` collapses to `range w`. -/
theorem sum_guard_shrink (f : ℕ → F) (q w : ℕ) (hw : w ≤ 82)
    (hg1 : ∀ x, x < w → 82 * q + x < 256)
    (hg2 : ∀ x, ¬ x < w → ¬ 82 * q + x < 256) :
    (∑ t ∈ Finset.range 82, if 82 * q + t < 256 then f t else 0) = ∑ t ∈ Finset.range w, f t := by
  have h2 : (∑ t ∈ Finset.range w, (if 82 * q + t < 256 then f t else 0))
      = ∑ t ∈ Finset.range 82, if 82 * q + t < 256 then f t else 0 := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr hw) fun x _ hxw => ?_
    rw [if_neg (hg2 x (by simpa using hxw))]
  rw [← h2]
  exact Finset.sum_congr rfl fun t ht => by
    rw [if_pos (hg1 t (Finset.mem_range.mp ht))]

/-- Limbs 0..2: no constant frame, 82 bits. -/
theorem wem_bound_small (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) (q : ℕ) (hq : q < 3) :
    ((wemCanon q).eval σ).val < 2 ^ 82 := by
  have hf : ∀ t < 82, ((wbitGLC (31 - (82 * q + t) / 8) ((82 * q + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    refine wbit_le_one σ h _ _ (Nat.lt_of_le_of_lt (Nat.sub_le 31 _) (by norm_num))
      (Nat.mod_lt _ (by norm_num))
  have hper : ∀ q' < 3, ((Xark.Rsa.Em.em82 q' : ℤ) : F).val = 0 := by
    intro q' hq'
    interval_cases q' <;> decide
  refine wem_bound_of 82 0
    (fun t => (wbitGLC (31 - (82 * q + t) / 8) ((82 * q + t) % 8)).eval σ) q σ le_rfl hf ?_
    (hper q hq) (by decide)
  rw [wem_eval]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * q + t < 256 then
          ((2 ^ t : ℕ) : F) * (wbitGLC (31 - (82 * q + t) / 8) ((82 * q + t) % 8)).eval σ
        else 0)
      = ∑ t ∈ Finset.range 82,
          ((2 ^ t : ℕ) : F) * (wbitGLC (31 - (82 * q + t) / 8) ((82 * q + t) % 8)).eval σ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht82 := Finset.mem_range.mp ht
    rw [if_pos (by omega)]
  rw [hsum]

/-- Limb 3: the frame's `1908058575186009548423168` plus the digest's top ten bits. -/
theorem wem_bound3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((wemCanon 3).eval σ).val < 2 ^ 82 := by
  have hf : ∀ t < 10, ((wbitGLC (31 - (82 * 3 + t) / 8) ((82 * 3 + t) % 8)).eval σ).val ≤ 1 := by
    intro t ht
    refine wbit_le_one σ h _ _ (Nat.lt_of_le_of_lt (Nat.sub_le 31 _) (by norm_num))
      (Nat.mod_lt _ (by norm_num))
  refine wem_bound_of 10 1908058575186009548423168
    (fun t => (wbitGLC (31 - (82 * 3 + t) / 8) ((82 * 3 + t) % 8)).eval σ) 3 σ (by norm_num) hf ?_
    (by decide) (by decide)
  rw [wem_eval]
  have hsum : (∑ t ∈ Finset.range 82,
        if 82 * 3 + t < 256 then
          ((2 ^ t : ℕ) : F) * (wbitGLC (31 - (82 * 3 + t) / 8) ((82 * 3 + t) % 8)).eval σ
        else 0)
      = ∑ t ∈ Finset.range 10,
          ((2 ^ t : ℕ) : F) * (wbitGLC (31 - (82 * 3 + t) / 8) ((82 * 3 + t) % 8)).eval σ := by
    rw [sum_guard_shrink
      (fun t => ((2 ^ t : ℕ) : F) * (wbitGLC (31 - (82 * 3 + t) / 8) ((82 * 3 + t) % 8)).eval σ)
      3 10 (by norm_num) (fun x hx => by omega) (fun x hx => by omega)]
  rw [hsum]

/-- Limbs 4..24: the digest is below them, so only the frame's constant remains. -/
theorem wem_bound_const (σ : ℕ → F) (q : ℕ) (hq : 4 ≤ q) (hq' : q < 25) :
    ((wemCanon q).eval σ).val < 2 ^ 82 := by
  rw [wem_eval]
  have hz : (∑ t ∈ Finset.range 82,
      if 82 * q + t < 256 then
        ((2 ^ t : ℕ) : F) * (wbitGLC (31 - (82 * q + t) / 8) ((82 * q + t) % 8)).eval σ
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [if_neg (by omega)]
  rw [hz, add_zero]
  interval_cases q <;> decide

/-- **The terminal `grouped_columns` call's `r` array is below `2^82`.** -/
theorem w_hEm (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ i < 25, pn (wcallAt 88) σ (100 + i) < 2 ^ 82 := by
  intro i hi
  have hpn : pn (wcallAt 88) σ (100 + i) = ((wemCanon i).eval σ).val := by
    simp only [pn, Call.lift, Call.env]
    rw [wem_plug i hi]
  rw [hpn]
  by_cases h3 : i < 3
  · exact wem_bound_small σ h i h3
  · rcases lt_or_ge i 4 with h4 | h4
    · have : i = 3 := by omega
      subst this
      exact wem_bound3 σ h
    · exact wem_bound_const σ i h4 hi

/-- **The 17×121 circuit's verification statement.** `n` is 2048 bits, `sig < n`, and the
encoded message `wChainEm` the circuit carries is `sig^65537 mod n`. -/
theorem w_verify_wide (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    2 ^ 2047 ≤ wChainN σ ∧ wChainN σ < 2 ^ 2048 ∧
      val (limb (wcallAt 40) σ 0) < wChainN σ ∧
      wChainEm σ ≡ (val (limb (wcallAt 40) σ 0)) ^ (2 ^ 16 + 1) [ZMOD wChainN σ] :=
  w_verify_wide_of_em σ h (w_hEm σ h)

end Xark.Circuits.Rsa2048
