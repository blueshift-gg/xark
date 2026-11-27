/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.WordsChain

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The words chain: q/r bounds for the 16 squarings

Square `i` is at segment `40 + 3i`; its `q` array (plugs 50..74) is the range-check
call at `38 + 3i`'s plugs, and its `r` array (75..99) the check at `39 + 3i`'s.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
theorem wq_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 40) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 40).plugs.drop 50).take 25 = ((wcallAt 38).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 40) σ (50 + j) = pn (wcallAt 38) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 38 (wcallAt 38) h rfl (by decide) rfl hj

theorem wr_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 40) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 40).plugs.drop 75).take 25 = ((wcallAt 39).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 40) σ (75 + j) = pn (wcallAt 39) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 39 (wcallAt 39) h rfl (by decide) rfl hj

theorem wq_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 43) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 43).plugs.drop 50).take 25 = ((wcallAt 41).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 43) σ (50 + j) = pn (wcallAt 41) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 41 (wcallAt 41) h rfl (by decide) rfl hj

theorem wr_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 43) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 43).plugs.drop 75).take 25 = ((wcallAt 42).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 43) σ (75 + j) = pn (wcallAt 42) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 42 (wcallAt 42) h rfl (by decide) rfl hj

theorem wq_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 46) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 46).plugs.drop 50).take 25 = ((wcallAt 44).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 46) σ (50 + j) = pn (wcallAt 44) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 44 (wcallAt 44) h rfl (by decide) rfl hj

theorem wr_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 46) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 46).plugs.drop 75).take 25 = ((wcallAt 45).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 46) σ (75 + j) = pn (wcallAt 45) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 45 (wcallAt 45) h rfl (by decide) rfl hj

theorem wq_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 49) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 49).plugs.drop 50).take 25 = ((wcallAt 47).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 49) σ (50 + j) = pn (wcallAt 47) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 47 (wcallAt 47) h rfl (by decide) rfl hj

theorem wr_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 49) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 49).plugs.drop 75).take 25 = ((wcallAt 48).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 49) σ (75 + j) = pn (wcallAt 48) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 48 (wcallAt 48) h rfl (by decide) rfl hj

theorem wq_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 52) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 52).plugs.drop 50).take 25 = ((wcallAt 50).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 52) σ (50 + j) = pn (wcallAt 50) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 50 (wcallAt 50) h rfl (by decide) rfl hj

theorem wr_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 52) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 52).plugs.drop 75).take 25 = ((wcallAt 51).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 52) σ (75 + j) = pn (wcallAt 51) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 51 (wcallAt 51) h rfl (by decide) rfl hj

theorem wq_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 55) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 55).plugs.drop 50).take 25 = ((wcallAt 53).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 55) σ (50 + j) = pn (wcallAt 53) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 53 (wcallAt 53) h rfl (by decide) rfl hj

theorem wr_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 55) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 55).plugs.drop 75).take 25 = ((wcallAt 54).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 55) σ (75 + j) = pn (wcallAt 54) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 54 (wcallAt 54) h rfl (by decide) rfl hj

theorem wq_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 58) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 58).plugs.drop 50).take 25 = ((wcallAt 56).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 58) σ (50 + j) = pn (wcallAt 56) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 56 (wcallAt 56) h rfl (by decide) rfl hj

theorem wr_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 58) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 58).plugs.drop 75).take 25 = ((wcallAt 57).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 58) σ (75 + j) = pn (wcallAt 57) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 57 (wcallAt 57) h rfl (by decide) rfl hj

theorem wq_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 61) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 61).plugs.drop 50).take 25 = ((wcallAt 59).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 61) σ (50 + j) = pn (wcallAt 59) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 59 (wcallAt 59) h rfl (by decide) rfl hj

theorem wr_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 61) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 61).plugs.drop 75).take 25 = ((wcallAt 60).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 61) σ (75 + j) = pn (wcallAt 60) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 60 (wcallAt 60) h rfl (by decide) rfl hj

theorem wq_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 64) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 64).plugs.drop 50).take 25 = ((wcallAt 62).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 64) σ (50 + j) = pn (wcallAt 62) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 62 (wcallAt 62) h rfl (by decide) rfl hj

theorem wr_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 64) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 64).plugs.drop 75).take 25 = ((wcallAt 63).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 64) σ (75 + j) = pn (wcallAt 63) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 63 (wcallAt 63) h rfl (by decide) rfl hj

theorem wq_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 67) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 67).plugs.drop 50).take 25 = ((wcallAt 65).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 67) σ (50 + j) = pn (wcallAt 65) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 65 (wcallAt 65) h rfl (by decide) rfl hj

theorem wr_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 67) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 67).plugs.drop 75).take 25 = ((wcallAt 66).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 67) σ (75 + j) = pn (wcallAt 66) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 66 (wcallAt 66) h rfl (by decide) rfl hj

theorem wq_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 70) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 70).plugs.drop 50).take 25 = ((wcallAt 68).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 70) σ (50 + j) = pn (wcallAt 68) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 68 (wcallAt 68) h rfl (by decide) rfl hj

theorem wr_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 70) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 70).plugs.drop 75).take 25 = ((wcallAt 69).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 70) σ (75 + j) = pn (wcallAt 69) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 69 (wcallAt 69) h rfl (by decide) rfl hj

theorem wq_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 73) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 73).plugs.drop 50).take 25 = ((wcallAt 71).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 73) σ (50 + j) = pn (wcallAt 71) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 71 (wcallAt 71) h rfl (by decide) rfl hj

theorem wr_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 73) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 73).plugs.drop 75).take 25 = ((wcallAt 72).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 73) σ (75 + j) = pn (wcallAt 72) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 72 (wcallAt 72) h rfl (by decide) rfl hj

theorem wq_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 76) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 76).plugs.drop 50).take 25 = ((wcallAt 74).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 76) σ (50 + j) = pn (wcallAt 74) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 74 (wcallAt 74) h rfl (by decide) rfl hj

theorem wr_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 76) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 76).plugs.drop 75).take 25 = ((wcallAt 75).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 76) σ (75 + j) = pn (wcallAt 75) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 75 (wcallAt 75) h rfl (by decide) rfl hj

theorem wq_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 79) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 79).plugs.drop 50).take 25 = ((wcallAt 77).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 79) σ (50 + j) = pn (wcallAt 77) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 77 (wcallAt 77) h rfl (by decide) rfl hj

theorem wr_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 79) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 79).plugs.drop 75).take 25 = ((wcallAt 78).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 79) σ (75 + j) = pn (wcallAt 78) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 78 (wcallAt 78) h rfl (by decide) rfl hj

theorem wq_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 82) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 82).plugs.drop 50).take 25 = ((wcallAt 80).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 82) σ (50 + j) = pn (wcallAt 80) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 80 (wcallAt 80) h rfl (by decide) rfl hj

theorem wr_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 82) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 82).plugs.drop 75).take 25 = ((wcallAt 81).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 82) σ (75 + j) = pn (wcallAt 81) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 81 (wcallAt 81) h rfl (by decide) rfl hj

theorem wq_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 85) σ (50 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 85).plugs.drop 50).take 25 = ((wcallAt 83).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 85) σ (50 + j) = pn (wcallAt 83) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wq_call_bound σ 83 (wcallAt 83) h rfl (by decide) rfl hj

theorem wr_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, pn (wcallAt 85) σ (75 + j) < 2 ^ 82 := by
  intro j hj
  have hw : ((wcallAt 85).plugs.drop 75).take 25 = ((wcallAt 84).plugs.drop 0).take 25 := by
    decide +kernel
  have hp := getD_of_window hj hw (LC.cst 0)
  have hpn : pn (wcallAt 85) σ (75 + j) = pn (wcallAt 84) σ j := by
    simp only [pn, Call.lift, Call.env, hp, Nat.zero_add]
  rw [hpn]
  exact wr_call_bound σ 84 (wcallAt 84) h rfl (by decide) rfl hj

end Xark.Circuits.Rsa2048
