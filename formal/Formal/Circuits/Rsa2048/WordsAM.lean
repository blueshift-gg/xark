/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.WordsQR

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The words chain: a and m bounds for the 16 squarings

The `m` array of every square is the converted modulus (`nLimb`); the `a` array is the
signature (`sLimb`, square 0) or the previous square's `r` (its plugs 75..99).
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

def nLimbMapLC : List ZLC := nLimb.map (fun v => (⟨0, [((1 : ℤ), v)]⟩ : ZLC))
def sLimbMapLC : List ZLC := sLimb.map (fun v => (⟨0, [((1 : ℤ), v)]⟩ : ZLC))

theorem nLimbMapLC_getD (j : ℕ) (hj : j < 25) :
    nLimbMapLC.getD j (LC.cst 0) = ⟨0, [((1 : ℤ), nLimb.getD j 0)]⟩ := by
  interval_cases j <;> rfl

theorem sLimbMapLC_getD (j : ℕ) (hj : j < 25) :
    sLimbMapLC.getD j (LC.cst 0) = ⟨0, [((1 : ℤ), sLimb.getD j 0)]⟩ := by
  interval_cases j <;> rfl
theorem wa_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 40) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 40).plugs.drop 0).take 25 = (sLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := sLimbMapLC_getD j hj
  have hpn : pn (wcallAt 40) σ j = (σ (sLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact s_limb_lt82 σ h j hj

theorem wm_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 40) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 40).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 40) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 43) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 43).plugs.drop 0).take 25 = ((wcallAt 40).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 43) σ j = pn (wcallAt 40) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_0 σ h j hj

theorem wm_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 43) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 43).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 43) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 46) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 46).plugs.drop 0).take 25 = ((wcallAt 43).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 46) σ j = pn (wcallAt 43) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_1 σ h j hj

theorem wm_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 46) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 46).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 46) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 49) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 49).plugs.drop 0).take 25 = ((wcallAt 46).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 49) σ j = pn (wcallAt 46) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_2 σ h j hj

theorem wm_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 49) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 49).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 49) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 52) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 52).plugs.drop 0).take 25 = ((wcallAt 49).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 52) σ j = pn (wcallAt 49) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_3 σ h j hj

theorem wm_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 52) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 52).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 52) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 55) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 55).plugs.drop 0).take 25 = ((wcallAt 52).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 55) σ j = pn (wcallAt 52) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_4 σ h j hj

theorem wm_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 55) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 55).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 55) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 58) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 58).plugs.drop 0).take 25 = ((wcallAt 55).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 58) σ j = pn (wcallAt 55) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_5 σ h j hj

theorem wm_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 58) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 58).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 58) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 61) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 61).plugs.drop 0).take 25 = ((wcallAt 58).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 61) σ j = pn (wcallAt 58) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_6 σ h j hj

theorem wm_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 61) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 61).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 61) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 64) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 64).plugs.drop 0).take 25 = ((wcallAt 61).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 64) σ j = pn (wcallAt 61) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_7 σ h j hj

theorem wm_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 64) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 64).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 64) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 67) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 67).plugs.drop 0).take 25 = ((wcallAt 64).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 67) σ j = pn (wcallAt 64) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_8 σ h j hj

theorem wm_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 67) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 67).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 67) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 70) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 70).plugs.drop 0).take 25 = ((wcallAt 67).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 70) σ j = pn (wcallAt 67) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_9 σ h j hj

theorem wm_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 70) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 70).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 70) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 73) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 73).plugs.drop 0).take 25 = ((wcallAt 70).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 73) σ j = pn (wcallAt 70) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_10 σ h j hj

theorem wm_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 73) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 73).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 73) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 76) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 76).plugs.drop 0).take 25 = ((wcallAt 73).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 76) σ j = pn (wcallAt 73) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_11 σ h j hj

theorem wm_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 76) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 76).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 76) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 79) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 79).plugs.drop 0).take 25 = ((wcallAt 76).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 79) σ j = pn (wcallAt 76) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_12 σ h j hj

theorem wm_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 79) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 79).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 79) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 82) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 82).plugs.drop 0).take 25 = ((wcallAt 79).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 82) σ j = pn (wcallAt 79) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_13 σ h j hj

theorem wm_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 82) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 82).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 82) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

theorem wa_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 85) σ j < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 85).plugs.drop 0).take 25 = ((wcallAt 82).plugs.drop 75).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hpn : pn (wcallAt 85) σ j = pn (wcallAt 82) σ (75 + j) := by
    simp only [pn, Call.lift, Call.env, hp]
  rw [hpn]
  exact wr_14 σ h j hj

theorem wm_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 85) σ (25 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 85).plugs.drop 25).take 25 = (nLimbMapLC.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  rw [Nat.zero_add] at hp
  have hgd := nLimbMapLC_getD j hj
  have hpn : pn (wcallAt 85) σ (25 + j) = (σ (nLimb.getD j 0)).val := by
    simp only [pn, Call.lift, Call.env, hp, hgd]
    simp [ZLC.toF, Xark.R1cs.LC.eval]
  rw [hpn]
  exact n_limb_lt82 σ h j hj

end Xark.Circuits.Rsa2048
