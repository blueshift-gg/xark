/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.MinusOneVal

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The words circuit's chain contracts

The same gadget contracts as `Verify.lean`, applied to `Rsa2048Words.circuit` through
`wseg`/`wcall_sat_of`. The template-level `val_inLimb_*` and `*_ins_getD` lemmas are
circuit-independent and reused.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

theorem wq_call_bound (σ : ℕ → F) (n : ℕ) (c : Call)
    (h : Sat Rsa2048Words.circuit σ) (hseg : wseg n = .call c)
    (hn : n < Rsa2048Words.circuit.length)
    (ht : c.t = Xark.Templates.RangeCheckQ.template) {j : ℕ} (hj : j < 25) :
    pn c σ j < 2 ^ 82 := by
  have hsat := wcall_sat_of h n c hseg hn
  rw [ht] at hsat
  have hs := Xark.Templates.RangeCheckQ.soundness (c.lift σ) hsat
  rw [Xark.Templates.RangeCheckQ.Spec, Xark.Templates.RangeDerived.SpecAt] at hs
  rcases hs with ⟨h1, h2⟩
  by_cases hj24 : j < 24
  · have := h1 j hj24
    rwa [q_ins_getD (c.lift σ) hj] at this
  · have hj24' : j = 24 := by omega
    subst hj24'
    have := h2
    rw [q_ins_getD (c.lift σ) (by norm_num : 24 < 25)] at this
    exact lt_trans this (by norm_num)

theorem wr_call_bound (σ : ℕ → F) (n : ℕ) (c : Call)
    (h : Sat Rsa2048Words.circuit σ) (hseg : wseg n = .call c)
    (hn : n < Rsa2048Words.circuit.length)
    (ht : c.t = Xark.Templates.RangeCheckR.template) {j : ℕ} (hj : j < 25) :
    pn c σ j < 2 ^ 82 := by
  have hsat := wcall_sat_of h n c hseg hn
  rw [ht] at hsat
  have hs := Xark.Templates.RangeCheckR.soundness (c.lift σ) hsat
  rw [Xark.Templates.RangeCheckR.Spec, Xark.Templates.RangeDerived.SpecAt] at hs
  rcases hs with ⟨h1, h2⟩
  by_cases hj24 : j < 24
  · have := h1 j hj24
    rwa [r_ins_getD (c.lift σ) hj] at this
  · have hj24' : j = 24 := by omega
    subst hj24'
    have := h2
    rw [r_ins_getD (c.lift σ) (by norm_num : 24 < 25)] at this
    exact lt_trans this (by norm_num)

/-- The square call's integer identity, from the four quarter bounds. -/
theorem w_square_contract (σ : ℕ → F) {n : ℕ} {c : Call}
    (h : Sat Rsa2048Words.circuit σ) (hseg : wseg n = .call c)
    (hn : n < Rsa2048Words.circuit.length)
    (ht : c.t = Xark.Templates.GroupedColumnsSquare.template)
    (ha : ∀ i < 25, pn c σ i < 2 ^ 82)
    (hm : ∀ i < 25, pn c σ (25 + i) < 2 ^ 82)
    (hq : ∀ i < 25, pn c σ (50 + i) < 2 ^ 82)
    (hr : ∀ i < 25, pn c σ (75 + i) < 2 ^ 82) :
    val (limb c σ 0) * val (limb c σ 0)
      = val (limb c σ 50) * val (limb c σ 25) + val (limb c σ 75) := by
  have hsat := wcall_sat_of h n c hseg hn
  rw [ht] at hsat
  have hspec := Xark.Templates.GroupedColumnsSquare.soundness (c.lift σ) hsat
  have hass : Xark.Templates.GroupedColumnsSquare.Assumptions
      (Xark.Templates.GroupedColumnsSquare.template.ins (c.lift σ)) := by
    intro i hi
    rw [Xark.Templates.GroupedColumnsSquare.ins_getD _ hi]
    by_cases h1 : i < 25
    · exact ha i h1
    · by_cases h2 : i < 50
      · have hi' : i = 25 + (i - 25) := by omega
        rw [hi']; exact hm (i - 25) (by omega)
      · by_cases h3 : i < 75
        · have hi' : i = 50 + (i - 50) := by omega
          rw [hi']; exact hq (i - 50) (by omega)
        · have hi' : i = 75 + (i - 75) := by omega
          rw [hi']; exact hr (i - 75) (by omega)
  have hid := hspec hass
  rw [val_inLimb_sq0 c σ, val_inLimb_sq c σ 50 (by norm_num),
    val_inLimb_sq c σ 25 (by norm_num), val_inLimb_sq c σ 75 (by norm_num)] at hid
  exact hid

/-- The terminal call's integer identity. -/
theorem w_general_contract (σ : ℕ → F) {n : ℕ} {c : Call}
    (h : Sat Rsa2048Words.circuit σ) (hseg : wseg n = .call c)
    (hn : n < Rsa2048Words.circuit.length)
    (ht : c.t = Xark.Templates.GroupedColumns.template)
    (ha : ∀ i < 25, pn c σ i < 2 ^ 82)
    (hb : ∀ i < 25, pn c σ (25 + i) < 2 ^ 82)
    (hm : ∀ i < 25, pn c σ (50 + i) < 2 ^ 82)
    (hq : ∀ i < 25, pn c σ (75 + i) < 2 ^ 82)
    (hr : ∀ i < 25, pn c σ (100 + i) < 2 ^ 82) :
    val (limb c σ 0) * val (limb c σ 25)
      = val (limb c σ 75) * val (limb c σ 50) + val (limb c σ 100) := by
  have hsat := wcall_sat_of h n c hseg hn
  rw [ht] at hsat
  have hspec := Xark.Templates.GroupedColumns.soundness (c.lift σ) hsat
  have hass : Xark.Templates.GroupedColumns.Assumptions
      (Xark.Templates.GroupedColumns.template.ins (c.lift σ)) := by
    intro i hi
    rw [Xark.Templates.GroupedColumns.ins_getD _ hi]
    by_cases h1 : i < 25
    · exact ha i h1
    · by_cases h2 : i < 50
      · have hi' : i = 25 + (i - 25) := by omega
        rw [hi']; exact hb (i - 25) (by omega)
      · by_cases h3 : i < 75
        · have hi' : i = 50 + (i - 50) := by omega
          rw [hi']; exact hm (i - 50) (by omega)
        · by_cases h4 : i < 100
          · have hi' : i = 75 + (i - 75) := by omega
            rw [hi']; exact hq (i - 75) (by omega)
          · have hi' : i = 100 + (i - 100) := by omega
            rw [hi']; exact hr (i - 100) (by omega)
  have hid := hspec hass
  rw [val_inLimb_gen0 c σ, val_inLimb_gen c σ 25 (by norm_num),
    val_inLimb_gen c σ 50 (by norm_num), val_inLimb_gen c σ 75 (by norm_num),
    val_inLimb_gen c σ 100 (by norm_num)] at hid
  exact hid

end Xark.Circuits.Rsa2048
