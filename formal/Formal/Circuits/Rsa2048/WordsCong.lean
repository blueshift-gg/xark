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
    ∀ j < 25, pn (wcallAt 88) σ (0 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 88).plugs.drop 0).take 25 = ((wcallAt 85).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 88) σ (0 + j) = pn (wcallAt 85) σ (75 + j) := by
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

end Xark.Circuits.Rsa2048
