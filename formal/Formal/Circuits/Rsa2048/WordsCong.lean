/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.WordsFinal
import Formal.RsaChain

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The words chain's congruence
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
theorem whaFin (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 88) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 88).plugs.drop 0).take 25 = ((wcallAt 85).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 88) σ j = pn (wcallAt 85) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_15 σ h j hj

theorem whbFin (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 88) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 88).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 88) σ (25 + j) = pn (wcallAt 40) σ (0 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  simpa using wa_0 σ h j hj

theorem whmFin (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 88) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 88).plugs.drop 50).take 25 = ((wcallAt 40).plugs.drop 25).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 88) σ (50 + j) = pn (wcallAt 40) σ (25 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wm_0 σ h j hj

theorem whqFin (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 88) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 88).plugs.drop 75).take 25 = ((wcallAt 86).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 88) σ (75 + j) = pn (wcallAt 86) σ (0 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  simpa using wq_call_bound σ 86 (wcallAt 86) h rfl (by decide) rfl hj

theorem wn_0 (σ : ℕ → F) :
    val (limb (wcallAt 40) σ 25) = wChainN σ := rfl

theorem wn_1 (σ : ℕ → F) :
    val (limb (wcallAt 43) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 43).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_2 (σ : ℕ → F) :
    val (limb (wcallAt 46) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 46).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_3 (σ : ℕ → F) :
    val (limb (wcallAt 49) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 49).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_4 (σ : ℕ → F) :
    val (limb (wcallAt 52) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 52).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_5 (σ : ℕ → F) :
    val (limb (wcallAt 55) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 55).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_6 (σ : ℕ → F) :
    val (limb (wcallAt 58) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 58).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_7 (σ : ℕ → F) :
    val (limb (wcallAt 61) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 61).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_8 (σ : ℕ → F) :
    val (limb (wcallAt 64) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 64).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_9 (σ : ℕ → F) :
    val (limb (wcallAt 67) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 67).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_10 (σ : ℕ → F) :
    val (limb (wcallAt 70) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 70).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_11 (σ : ℕ → F) :
    val (limb (wcallAt 73) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 73).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_12 (σ : ℕ → F) :
    val (limb (wcallAt 76) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 76).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_13 (σ : ℕ → F) :
    val (limb (wcallAt 79) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 79).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_14 (σ : ℕ → F) :
    val (limb (wcallAt 82) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 82).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem wn_15 (σ : ℕ → F) :
    val (limb (wcallAt 85) σ 25) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((wcallAt 85).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

theorem w_step (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 16, wChainA σ (j + 1) ≡ wChainA σ j * wChainA σ j [ZMOD wChainN σ] := by
  intro j hj
  interval_cases j
  · have h1 : wChainA σ 1 = val (limb (wcallAt 40) σ 75) := by
      rw [show wChainA σ 1 = val (limb (wcallAt 43) σ 0) from rfl, wA_0 σ]
    have h0 : wChainA σ 0 = val (limb (wcallAt 40) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 40) σ 50), by rw [wsq_0 σ h, wn_0 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 2 = val (limb (wcallAt 43) σ 75) := by
      rw [show wChainA σ 2 = val (limb (wcallAt 46) σ 0) from rfl, wA_1 σ]
    have h0 : wChainA σ 1 = val (limb (wcallAt 43) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 43) σ 50), by rw [wsq_1 σ h, wn_1 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 3 = val (limb (wcallAt 46) σ 75) := by
      rw [show wChainA σ 3 = val (limb (wcallAt 49) σ 0) from rfl, wA_2 σ]
    have h0 : wChainA σ 2 = val (limb (wcallAt 46) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 46) σ 50), by rw [wsq_2 σ h, wn_2 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 4 = val (limb (wcallAt 49) σ 75) := by
      rw [show wChainA σ 4 = val (limb (wcallAt 52) σ 0) from rfl, wA_3 σ]
    have h0 : wChainA σ 3 = val (limb (wcallAt 49) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 49) σ 50), by rw [wsq_3 σ h, wn_3 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 5 = val (limb (wcallAt 52) σ 75) := by
      rw [show wChainA σ 5 = val (limb (wcallAt 55) σ 0) from rfl, wA_4 σ]
    have h0 : wChainA σ 4 = val (limb (wcallAt 52) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 52) σ 50), by rw [wsq_4 σ h, wn_4 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 6 = val (limb (wcallAt 55) σ 75) := by
      rw [show wChainA σ 6 = val (limb (wcallAt 58) σ 0) from rfl, wA_5 σ]
    have h0 : wChainA σ 5 = val (limb (wcallAt 55) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 55) σ 50), by rw [wsq_5 σ h, wn_5 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 7 = val (limb (wcallAt 58) σ 75) := by
      rw [show wChainA σ 7 = val (limb (wcallAt 61) σ 0) from rfl, wA_6 σ]
    have h0 : wChainA σ 6 = val (limb (wcallAt 58) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 58) σ 50), by rw [wsq_6 σ h, wn_6 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 8 = val (limb (wcallAt 61) σ 75) := by
      rw [show wChainA σ 8 = val (limb (wcallAt 64) σ 0) from rfl, wA_7 σ]
    have h0 : wChainA σ 7 = val (limb (wcallAt 61) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 61) σ 50), by rw [wsq_7 σ h, wn_7 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 9 = val (limb (wcallAt 64) σ 75) := by
      rw [show wChainA σ 9 = val (limb (wcallAt 67) σ 0) from rfl, wA_8 σ]
    have h0 : wChainA σ 8 = val (limb (wcallAt 64) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 64) σ 50), by rw [wsq_8 σ h, wn_8 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 10 = val (limb (wcallAt 67) σ 75) := by
      rw [show wChainA σ 10 = val (limb (wcallAt 70) σ 0) from rfl, wA_9 σ]
    have h0 : wChainA σ 9 = val (limb (wcallAt 67) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 67) σ 50), by rw [wsq_9 σ h, wn_9 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 11 = val (limb (wcallAt 70) σ 75) := by
      rw [show wChainA σ 11 = val (limb (wcallAt 73) σ 0) from rfl, wA_10 σ]
    have h0 : wChainA σ 10 = val (limb (wcallAt 70) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 70) σ 50), by rw [wsq_10 σ h, wn_10 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 12 = val (limb (wcallAt 73) σ 75) := by
      rw [show wChainA σ 12 = val (limb (wcallAt 76) σ 0) from rfl, wA_11 σ]
    have h0 : wChainA σ 11 = val (limb (wcallAt 73) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 73) σ 50), by rw [wsq_11 σ h, wn_11 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 13 = val (limb (wcallAt 76) σ 75) := by
      rw [show wChainA σ 13 = val (limb (wcallAt 79) σ 0) from rfl, wA_12 σ]
    have h0 : wChainA σ 12 = val (limb (wcallAt 76) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 76) σ 50), by rw [wsq_12 σ h, wn_12 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 14 = val (limb (wcallAt 79) σ 75) := by
      rw [show wChainA σ 14 = val (limb (wcallAt 82) σ 0) from rfl, wA_13 σ]
    have h0 : wChainA σ 13 = val (limb (wcallAt 79) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 79) σ 50), by rw [wsq_13 σ h, wn_13 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 15 = val (limb (wcallAt 82) σ 75) := by
      rw [show wChainA σ 15 = val (limb (wcallAt 85) σ 0) from rfl, wA_14 σ]
    have h0 : wChainA σ 14 = val (limb (wcallAt 82) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 82) σ 50), by rw [wsq_14 σ h, wn_14 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩
  · have h1 : wChainA σ 16 = val (limb (wcallAt 85) σ 75) := by
      rw [show wChainA σ 16 = val (limb (wcallAt 88) σ 0) from rfl, wA_15 σ]
    have h0 : wChainA σ 15 = val (limb (wcallAt 85) σ 0) := rfl
    rw [h1, h0, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]
    rw [Int.modEq_iff_dvd]
    exact ⟨val (limb (wcallAt 85) σ 50), by rw [wsq_15 σ h, wn_15 σ, show wChainN σ = val (limb (wcallAt 40) σ 25) from rfl]; ring⟩

theorem w_final (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    (hEm : ∀ j < 25, pn (wcallAt 88) σ (100 + j) < 2 ^ 82) :
    wChainA σ 16 * wChainA σ 0 = val (limb (wcallAt 88) σ 75) * wChainN σ + wChainEm σ := by
  have hf := w_general_contract (n := 88) (c := wcallAt 88) σ h rfl (by decide) rfl
    (whaFin σ h) (whbFin σ h) (whmFin σ h) (whqFin σ h) hEm
  rw [show wChainA σ 16 = val (limb (wcallAt 88) σ 0) from rfl,
      show wChainA σ 0 = val (limb (wcallAt 40) σ 0) from rfl,
      show wChainEm σ = val (limb (wcallAt 88) σ 100) from rfl,
      ← wFinB σ, ← wFinM σ]
  exact hf

/-- The words chain: `EM ≡ sig^65537 (mod n)`. -/
theorem w_chain_congruence (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    (hEm : ∀ j < 25, pn (wcallAt 88) σ (100 + j) < 2 ^ 82) :
    wChainEm σ ≡ (wChainA σ 0) ^ (2 ^ 16 + 1) [ZMOD wChainN σ] :=
  Xark.Rsa.Chain.chain_seq_range (wChainN σ) (wChainEm σ) (val (limb (wcallAt 88) σ 75))
    (wChainA σ) 16 (w_step σ h) (w_final σ h hEm)

end Xark.Circuits.Rsa2048
