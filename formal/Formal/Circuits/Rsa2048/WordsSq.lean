/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.WordsAM

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The words chain: the 16 square identities

Square `i` at segment `40 + 3i`: `a·a = q·m + r` over the integers, with the four
array bounds from `WordsQR`/`WordsAM`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
theorem wsq_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 40) σ 0) * val (limb (wcallAt 40) σ 0)
      = val (limb (wcallAt 40) σ 50) * val (limb (wcallAt 40) σ 25)
        + val (limb (wcallAt 40) σ 75) :=
  w_square_contract (n := 40) (c := wcallAt 40) σ h rfl (by decide) rfl (wa_0 σ h) (wm_0 σ h) (wq_0 σ h) (wr_0 σ h)

theorem wsq_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 43) σ 0) * val (limb (wcallAt 43) σ 0)
      = val (limb (wcallAt 43) σ 50) * val (limb (wcallAt 43) σ 25)
        + val (limb (wcallAt 43) σ 75) :=
  w_square_contract (n := 43) (c := wcallAt 43) σ h rfl (by decide) rfl (wa_1 σ h) (wm_1 σ h) (wq_1 σ h) (wr_1 σ h)

theorem wsq_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 46) σ 0) * val (limb (wcallAt 46) σ 0)
      = val (limb (wcallAt 46) σ 50) * val (limb (wcallAt 46) σ 25)
        + val (limb (wcallAt 46) σ 75) :=
  w_square_contract (n := 46) (c := wcallAt 46) σ h rfl (by decide) rfl (wa_2 σ h) (wm_2 σ h) (wq_2 σ h) (wr_2 σ h)

theorem wsq_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 49) σ 0) * val (limb (wcallAt 49) σ 0)
      = val (limb (wcallAt 49) σ 50) * val (limb (wcallAt 49) σ 25)
        + val (limb (wcallAt 49) σ 75) :=
  w_square_contract (n := 49) (c := wcallAt 49) σ h rfl (by decide) rfl (wa_3 σ h) (wm_3 σ h) (wq_3 σ h) (wr_3 σ h)

theorem wsq_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 52) σ 0) * val (limb (wcallAt 52) σ 0)
      = val (limb (wcallAt 52) σ 50) * val (limb (wcallAt 52) σ 25)
        + val (limb (wcallAt 52) σ 75) :=
  w_square_contract (n := 52) (c := wcallAt 52) σ h rfl (by decide) rfl (wa_4 σ h) (wm_4 σ h) (wq_4 σ h) (wr_4 σ h)

theorem wsq_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 55) σ 0) * val (limb (wcallAt 55) σ 0)
      = val (limb (wcallAt 55) σ 50) * val (limb (wcallAt 55) σ 25)
        + val (limb (wcallAt 55) σ 75) :=
  w_square_contract (n := 55) (c := wcallAt 55) σ h rfl (by decide) rfl (wa_5 σ h) (wm_5 σ h) (wq_5 σ h) (wr_5 σ h)

theorem wsq_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 58) σ 0) * val (limb (wcallAt 58) σ 0)
      = val (limb (wcallAt 58) σ 50) * val (limb (wcallAt 58) σ 25)
        + val (limb (wcallAt 58) σ 75) :=
  w_square_contract (n := 58) (c := wcallAt 58) σ h rfl (by decide) rfl (wa_6 σ h) (wm_6 σ h) (wq_6 σ h) (wr_6 σ h)

theorem wsq_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 61) σ 0) * val (limb (wcallAt 61) σ 0)
      = val (limb (wcallAt 61) σ 50) * val (limb (wcallAt 61) σ 25)
        + val (limb (wcallAt 61) σ 75) :=
  w_square_contract (n := 61) (c := wcallAt 61) σ h rfl (by decide) rfl (wa_7 σ h) (wm_7 σ h) (wq_7 σ h) (wr_7 σ h)

theorem wsq_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 64) σ 0) * val (limb (wcallAt 64) σ 0)
      = val (limb (wcallAt 64) σ 50) * val (limb (wcallAt 64) σ 25)
        + val (limb (wcallAt 64) σ 75) :=
  w_square_contract (n := 64) (c := wcallAt 64) σ h rfl (by decide) rfl (wa_8 σ h) (wm_8 σ h) (wq_8 σ h) (wr_8 σ h)

theorem wsq_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 67) σ 0) * val (limb (wcallAt 67) σ 0)
      = val (limb (wcallAt 67) σ 50) * val (limb (wcallAt 67) σ 25)
        + val (limb (wcallAt 67) σ 75) :=
  w_square_contract (n := 67) (c := wcallAt 67) σ h rfl (by decide) rfl (wa_9 σ h) (wm_9 σ h) (wq_9 σ h) (wr_9 σ h)

theorem wsq_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 70) σ 0) * val (limb (wcallAt 70) σ 0)
      = val (limb (wcallAt 70) σ 50) * val (limb (wcallAt 70) σ 25)
        + val (limb (wcallAt 70) σ 75) :=
  w_square_contract (n := 70) (c := wcallAt 70) σ h rfl (by decide) rfl (wa_10 σ h) (wm_10 σ h) (wq_10 σ h) (wr_10 σ h)

theorem wsq_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 73) σ 0) * val (limb (wcallAt 73) σ 0)
      = val (limb (wcallAt 73) σ 50) * val (limb (wcallAt 73) σ 25)
        + val (limb (wcallAt 73) σ 75) :=
  w_square_contract (n := 73) (c := wcallAt 73) σ h rfl (by decide) rfl (wa_11 σ h) (wm_11 σ h) (wq_11 σ h) (wr_11 σ h)

theorem wsq_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 76) σ 0) * val (limb (wcallAt 76) σ 0)
      = val (limb (wcallAt 76) σ 50) * val (limb (wcallAt 76) σ 25)
        + val (limb (wcallAt 76) σ 75) :=
  w_square_contract (n := 76) (c := wcallAt 76) σ h rfl (by decide) rfl (wa_12 σ h) (wm_12 σ h) (wq_12 σ h) (wr_12 σ h)

theorem wsq_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 79) σ 0) * val (limb (wcallAt 79) σ 0)
      = val (limb (wcallAt 79) σ 50) * val (limb (wcallAt 79) σ 25)
        + val (limb (wcallAt 79) σ 75) :=
  w_square_contract (n := 79) (c := wcallAt 79) σ h rfl (by decide) rfl (wa_13 σ h) (wm_13 σ h) (wq_13 σ h) (wr_13 σ h)

theorem wsq_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 82) σ 0) * val (limb (wcallAt 82) σ 0)
      = val (limb (wcallAt 82) σ 50) * val (limb (wcallAt 82) σ 25)
        + val (limb (wcallAt 82) σ 75) :=
  w_square_contract (n := 82) (c := wcallAt 82) σ h rfl (by decide) rfl (wa_14 σ h) (wm_14 σ h) (wq_14 σ h) (wr_14 σ h)

theorem wsq_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    val (limb (wcallAt 85) σ 0) * val (limb (wcallAt 85) σ 0)
      = val (limb (wcallAt 85) σ 50) * val (limb (wcallAt 85) σ 25)
        + val (limb (wcallAt 85) σ 75) :=
  w_square_contract (n := 85) (c := wcallAt 85) σ h rfl (by decide) rfl (wa_15 σ h) (wm_15 σ h) (wq_15 σ h) (wr_15 σ h)

end Xark.Circuits.Rsa2048
