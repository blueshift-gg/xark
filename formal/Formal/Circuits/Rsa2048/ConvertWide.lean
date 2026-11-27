/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.ConvertCols
import Formal.Circuits.Rsa2048.ConvertColsSig
import Formal.RsaConvert

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# `convert_wide` telescopes: the converted limbs denote the 17×121 numbers

`RsaConvert.telescoping` needs the per-column hypothesis and the final carry zero.
The column theorems are in `ConvertCols.lean`/`ConvertColsSig.lean`; this file puts
them in `cols`/`cN`/`yN` form and gets `Σ y_j·W^j = Σ x_i·2^(121i)` for both operands.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- The modulus's 17 input limb variables (the reader's plugs). -/
def nIn : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
/-- The modulus's 25 converted limb variables. -/
def nLimb : List ℕ := [16747, 17147, 17547, 17947, 18347, 18747, 19147, 19547, 19947, 20347, 20747, 21147, 21547, 21947, 22347, 22747, 23147, 23547, 23947, 24347, 24747, 25147, 25547, 25947, 26347]
/-- The modulus's 25 carry variables. -/
def nCarry : List ℕ := [16746, 17146, 17546, 17946, 18346, 18746, 19146, 19546, 19946, 20346, 20746, 21146, 21546, 21946, 22346, 22746, 23146, 23546, 23946, 24346, 24746, 25146, 25546, 25946, 26346]
/-- The signature's 17 input limb variables. -/
def sIn : List ℕ := [4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147]
/-- The signature's 25 converted limb variables. -/
def sLimb : List ℕ := [26508, 26908, 27308, 27708, 28108, 28508, 28908, 29308, 29708, 30108, 30508, 30908, 31308, 31708, 32108, 32508, 32908, 33308, 33708, 34108, 34508, 34908, 35308, 35708, 36108]
/-- The signature's 25 carry variables. -/
def sCarry : List ℕ := [26507, 26907, 27307, 27707, 28107, 28507, 28907, 29307, 29707, 30107, 30507, 30907, 31307, 31707, 32107, 32507, 32907, 33307, 33707, 34107, 34507, 34907, 35307, 35707, 36107]

def xN (σ : ℕ → F) (i : ℕ) : ℤ := ((σ (nIn.getD i 0)).val : ℤ)
def yN (σ : ℕ → F) (j : ℕ) : ℤ := ((σ (nLimb.getD j 0)).val : ℤ)
def cN (σ : ℕ → F) (j : ℕ) : ℤ := ((σ (nCarry.getD j 0)).val : ℤ)
def xS (σ : ℕ → F) (i : ℕ) : ℤ := ((σ (sIn.getD i 0)).val : ℤ)
def yS (σ : ℕ → F) (j : ℕ) : ℤ := ((σ (sLimb.getD j 0)).val : ℤ)
def cS (σ : ℕ → F) (j : ℕ) : ℤ := ((σ (sCarry.getD j 0)).val : ℤ)

/-- `cols` at a column with one input limb. -/
theorem cols_single {x : ℕ → ℤ} {j i0 : ℕ} (hi0 : 121 * i0 / 82 = j) (hi0lt : i0 < 17)
    (huniq : ∀ i : Fin 17, (i : ℕ) ≠ i0 → 121 * (i : ℕ) / 82 ≠ j) :
    Xark.Rsa.Convert.cols x j = x i0 * 2 ^ (121 * i0 % 82) := by
  rw [Xark.Rsa.Convert.cols, Finset.sum_eq_single i0]
  · rw [if_pos hi0]
  · intro i hi hne
    rw [if_neg]
    exact huniq ⟨i, Finset.mem_range.mp hi⟩ hne
  · intro hnot
    exact absurd (Finset.mem_range.mpr hi0lt) hnot

/-- `cols` at a column with no input limb. -/
theorem cols_none {x : ℕ → ℤ} {j : ℕ} (h : ∀ i : Fin 17, 121 * (i : ℕ) / 82 ≠ j) :
    Xark.Rsa.Convert.cols x j = 0 := by
  rw [Xark.Rsa.Convert.cols]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [if_neg]
  exact h ⟨i, Finset.mem_range.mp hi⟩

theorem n_c24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) : (cN σ) 24 = 0 := by
  have hz := n_col24_row σ h
  simp [cN, nCarry, hz]

theorem n_row0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 0 + 0 = W * (cN σ) 0 + (yN σ) 0 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 0 = ((σ 0).val : ℤ) := by
    rw [cols_single (j := 0) (i0 := 0) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col0 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_one] using hcol

theorem n_hrow1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 1 + (cN σ) 0 =
      W * (cN σ) 1 + (yN σ) 1 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 1 =
      (2 ^ 39 : ℤ) * ((σ 1).val : ℤ) := by
    rw [cols_single (j := 1) (i0 := 1) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col1 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 2 + (cN σ) 1 =
      W * (cN σ) 2 + (yN σ) 2 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 2 =
      (2 ^ 78 : ℤ) * ((σ 2).val : ℤ) := by
    rw [cols_single (j := 2) (i0 := 2) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col2 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 3 + (cN σ) 2 =
      W * (cN σ) 3 + (yN σ) 3 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 3 = 0 := by
    rw [cols_none (j := 3) (by decide)]
  have hcol := n_col3 σ h
  rw [hc, zero_add]
  simpa [cN, yN, nLimb, nCarry] using hcol

theorem n_hrow4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 4 + (cN σ) 3 =
      W * (cN σ) 4 + (yN σ) 4 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 4 =
      (2 ^ 35 : ℤ) * ((σ 3).val : ℤ) := by
    rw [cols_single (j := 4) (i0 := 3) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col4 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 5 + (cN σ) 4 =
      W * (cN σ) 5 + (yN σ) 5 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 5 =
      (2 ^ 74 : ℤ) * ((σ 4).val : ℤ) := by
    rw [cols_single (j := 5) (i0 := 4) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col5 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 6 + (cN σ) 5 =
      W * (cN σ) 6 + (yN σ) 6 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 6 = 0 := by
    rw [cols_none (j := 6) (by decide)]
  have hcol := n_col6 σ h
  rw [hc, zero_add]
  simpa [cN, yN, nLimb, nCarry] using hcol

theorem n_hrow7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 7 + (cN σ) 6 =
      W * (cN σ) 7 + (yN σ) 7 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 7 =
      (2 ^ 31 : ℤ) * ((σ 5).val : ℤ) := by
    rw [cols_single (j := 7) (i0 := 5) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col7 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 8 + (cN σ) 7 =
      W * (cN σ) 8 + (yN σ) 8 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 8 =
      (2 ^ 70 : ℤ) * ((σ 6).val : ℤ) := by
    rw [cols_single (j := 8) (i0 := 6) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col8 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 9 + (cN σ) 8 =
      W * (cN σ) 9 + (yN σ) 9 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 9 = 0 := by
    rw [cols_none (j := 9) (by decide)]
  have hcol := n_col9 σ h
  rw [hc, zero_add]
  simpa [cN, yN, nLimb, nCarry] using hcol

theorem n_hrow10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 10 + (cN σ) 9 =
      W * (cN σ) 10 + (yN σ) 10 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 10 =
      (2 ^ 27 : ℤ) * ((σ 7).val : ℤ) := by
    rw [cols_single (j := 10) (i0 := 7) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col10 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 11 + (cN σ) 10 =
      W * (cN σ) 11 + (yN σ) 11 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 11 =
      (2 ^ 66 : ℤ) * ((σ 8).val : ℤ) := by
    rw [cols_single (j := 11) (i0 := 8) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col11 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 12 + (cN σ) 11 =
      W * (cN σ) 12 + (yN σ) 12 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 12 = 0 := by
    rw [cols_none (j := 12) (by decide)]
  have hcol := n_col12 σ h
  rw [hc, zero_add]
  simpa [cN, yN, nLimb, nCarry] using hcol

theorem n_hrow13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 13 + (cN σ) 12 =
      W * (cN σ) 13 + (yN σ) 13 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 13 =
      (2 ^ 23 : ℤ) * ((σ 9).val : ℤ) := by
    rw [cols_single (j := 13) (i0 := 9) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col13 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 14 + (cN σ) 13 =
      W * (cN σ) 14 + (yN σ) 14 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 14 =
      (2 ^ 62 : ℤ) * ((σ 10).val : ℤ) := by
    rw [cols_single (j := 14) (i0 := 10) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col14 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 15 + (cN σ) 14 =
      W * (cN σ) 15 + (yN σ) 15 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 15 = 0 := by
    rw [cols_none (j := 15) (by decide)]
  have hcol := n_col15 σ h
  rw [hc, zero_add]
  simpa [cN, yN, nLimb, nCarry] using hcol

theorem n_hrow16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 16 + (cN σ) 15 =
      W * (cN σ) 16 + (yN σ) 16 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 16 =
      (2 ^ 19 : ℤ) * ((σ 11).val : ℤ) := by
    rw [cols_single (j := 16) (i0 := 11) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col16 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 17 + (cN σ) 16 =
      W * (cN σ) 17 + (yN σ) 17 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 17 =
      (2 ^ 58 : ℤ) * ((σ 12).val : ℤ) := by
    rw [cols_single (j := 17) (i0 := 12) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col17 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 18 + (cN σ) 17 =
      W * (cN σ) 18 + (yN σ) 18 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 18 = 0 := by
    rw [cols_none (j := 18) (by decide)]
  have hcol := n_col18 σ h
  rw [hc, zero_add]
  simpa [cN, yN, nLimb, nCarry] using hcol

theorem n_hrow19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 19 + (cN σ) 18 =
      W * (cN σ) 19 + (yN σ) 19 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 19 =
      (2 ^ 15 : ℤ) * ((σ 13).val : ℤ) := by
    rw [cols_single (j := 19) (i0 := 13) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col19 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 20 + (cN σ) 19 =
      W * (cN σ) 20 + (yN σ) 20 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 20 =
      (2 ^ 54 : ℤ) * ((σ 14).val : ℤ) := by
    rw [cols_single (j := 20) (i0 := 14) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col20 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 21 + (cN σ) 20 =
      W * (cN σ) 21 + (yN σ) 21 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 21 = 0 := by
    rw [cols_none (j := 21) (by decide)]
  have hcol := n_col21 σ h
  rw [hc, zero_add]
  simpa [cN, yN, nLimb, nCarry] using hcol

theorem n_hrow22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 22 + (cN σ) 21 =
      W * (cN σ) 22 + (yN σ) 22 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 22 =
      (2 ^ 11 : ℤ) * ((σ 15).val : ℤ) := by
    rw [cols_single (j := 22) (i0 := 15) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col22 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 23 + (cN σ) 22 =
      W * (cN σ) 23 + (yN σ) 23 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 23 =
      (2 ^ 50 : ℤ) * ((σ 16).val : ℤ) := by
    rw [cols_single (j := 23) (i0 := 16) (by norm_num) (by norm_num) (by decide)]
    simp [xN, nIn] <;> ring
  have hcol := n_col23 σ h
  rw [hc]
  simpa [cN, yN, nLimb, nCarry, mul_comm] using hcol

theorem n_hrow24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xN σ) 24 + (cN σ) 23 = W * (cN σ) 24 + (yN σ) 24 := by
  have hc : Xark.Rsa.Convert.cols (xN σ) 24 = 0 := by
    rw [cols_none (j := 24) (by decide)]
  have hz := n_c24 σ h
  have hcol := n_col24 σ h
  rw [hc, zero_add, hz]
  simpa [cN, yN, nLimb, nCarry] using hcol

theorem n_hrow (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, Xark.Rsa.Convert.cols (xN σ) j +
      (if j = 0 then 0 else (cN σ) (j - 1)) = W * (cN σ) j + (yN σ) j := by
  intro j hj
  interval_cases j
  · simpa using n_row0 σ h
  · simpa using n_hrow1 σ h
  · simpa using n_hrow2 σ h
  · simpa using n_hrow3 σ h
  · simpa using n_hrow4 σ h
  · simpa using n_hrow5 σ h
  · simpa using n_hrow6 σ h
  · simpa using n_hrow7 σ h
  · simpa using n_hrow8 σ h
  · simpa using n_hrow9 σ h
  · simpa using n_hrow10 σ h
  · simpa using n_hrow11 σ h
  · simpa using n_hrow12 σ h
  · simpa using n_hrow13 σ h
  · simpa using n_hrow14 σ h
  · simpa using n_hrow15 σ h
  · simpa using n_hrow16 σ h
  · simpa using n_hrow17 σ h
  · simpa using n_hrow18 σ h
  · simpa using n_hrow19 σ h
  · simpa using n_hrow20 σ h
  · simpa using n_hrow21 σ h
  · simpa using n_hrow22 σ h
  · simpa using n_hrow23 σ h
  · simpa using n_hrow24 σ h

theorem n_convert_eq (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (∑ j ∈ Finset.range 25, (yN σ) j * (W : ℤ) ^ j)
      = ∑ i ∈ Finset.range 17, (xN σ) i * 2 ^ (121 * i) := by
  have := Xark.Rsa.Convert.telescoping (xN σ) (yN σ) (cN σ) (n_hrow σ h) (n_c24 σ h)
  simpa [Xark.Rsa.Convert.W, W] using this

theorem s_c24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) : (cS σ) 24 = 0 := by
  have hz := s_col24_row σ h
  simp [cS, sCarry, hz]

theorem s_row0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 0 + 0 = W * (cS σ) 0 + (yS σ) 0 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 0 = ((σ 4131).val : ℤ) := by
    rw [cols_single (j := 0) (i0 := 0) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col0 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_one] using hcol

theorem s_hrow1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 1 + (cS σ) 0 =
      W * (cS σ) 1 + (yS σ) 1 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 1 =
      (2 ^ 39 : ℤ) * ((σ 4132).val : ℤ) := by
    rw [cols_single (j := 1) (i0 := 1) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col1 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 2 + (cS σ) 1 =
      W * (cS σ) 2 + (yS σ) 2 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 2 =
      (2 ^ 78 : ℤ) * ((σ 4133).val : ℤ) := by
    rw [cols_single (j := 2) (i0 := 2) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col2 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 3 + (cS σ) 2 =
      W * (cS σ) 3 + (yS σ) 3 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 3 = 0 := by
    rw [cols_none (j := 3) (by decide)]
  have hcol := s_col3 σ h
  rw [hc, zero_add]
  simpa [cS, yS, sLimb, sCarry] using hcol

theorem s_hrow4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 4 + (cS σ) 3 =
      W * (cS σ) 4 + (yS σ) 4 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 4 =
      (2 ^ 35 : ℤ) * ((σ 4134).val : ℤ) := by
    rw [cols_single (j := 4) (i0 := 3) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col4 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 5 + (cS σ) 4 =
      W * (cS σ) 5 + (yS σ) 5 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 5 =
      (2 ^ 74 : ℤ) * ((σ 4135).val : ℤ) := by
    rw [cols_single (j := 5) (i0 := 4) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col5 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 6 + (cS σ) 5 =
      W * (cS σ) 6 + (yS σ) 6 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 6 = 0 := by
    rw [cols_none (j := 6) (by decide)]
  have hcol := s_col6 σ h
  rw [hc, zero_add]
  simpa [cS, yS, sLimb, sCarry] using hcol

theorem s_hrow7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 7 + (cS σ) 6 =
      W * (cS σ) 7 + (yS σ) 7 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 7 =
      (2 ^ 31 : ℤ) * ((σ 4136).val : ℤ) := by
    rw [cols_single (j := 7) (i0 := 5) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col7 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 8 + (cS σ) 7 =
      W * (cS σ) 8 + (yS σ) 8 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 8 =
      (2 ^ 70 : ℤ) * ((σ 4137).val : ℤ) := by
    rw [cols_single (j := 8) (i0 := 6) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col8 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 9 + (cS σ) 8 =
      W * (cS σ) 9 + (yS σ) 9 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 9 = 0 := by
    rw [cols_none (j := 9) (by decide)]
  have hcol := s_col9 σ h
  rw [hc, zero_add]
  simpa [cS, yS, sLimb, sCarry] using hcol

theorem s_hrow10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 10 + (cS σ) 9 =
      W * (cS σ) 10 + (yS σ) 10 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 10 =
      (2 ^ 27 : ℤ) * ((σ 4138).val : ℤ) := by
    rw [cols_single (j := 10) (i0 := 7) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col10 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 11 + (cS σ) 10 =
      W * (cS σ) 11 + (yS σ) 11 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 11 =
      (2 ^ 66 : ℤ) * ((σ 4139).val : ℤ) := by
    rw [cols_single (j := 11) (i0 := 8) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col11 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 12 + (cS σ) 11 =
      W * (cS σ) 12 + (yS σ) 12 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 12 = 0 := by
    rw [cols_none (j := 12) (by decide)]
  have hcol := s_col12 σ h
  rw [hc, zero_add]
  simpa [cS, yS, sLimb, sCarry] using hcol

theorem s_hrow13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 13 + (cS σ) 12 =
      W * (cS σ) 13 + (yS σ) 13 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 13 =
      (2 ^ 23 : ℤ) * ((σ 4140).val : ℤ) := by
    rw [cols_single (j := 13) (i0 := 9) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col13 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 14 + (cS σ) 13 =
      W * (cS σ) 14 + (yS σ) 14 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 14 =
      (2 ^ 62 : ℤ) * ((σ 4141).val : ℤ) := by
    rw [cols_single (j := 14) (i0 := 10) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col14 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 15 + (cS σ) 14 =
      W * (cS σ) 15 + (yS σ) 15 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 15 = 0 := by
    rw [cols_none (j := 15) (by decide)]
  have hcol := s_col15 σ h
  rw [hc, zero_add]
  simpa [cS, yS, sLimb, sCarry] using hcol

theorem s_hrow16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 16 + (cS σ) 15 =
      W * (cS σ) 16 + (yS σ) 16 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 16 =
      (2 ^ 19 : ℤ) * ((σ 4142).val : ℤ) := by
    rw [cols_single (j := 16) (i0 := 11) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col16 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 17 + (cS σ) 16 =
      W * (cS σ) 17 + (yS σ) 17 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 17 =
      (2 ^ 58 : ℤ) * ((σ 4143).val : ℤ) := by
    rw [cols_single (j := 17) (i0 := 12) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col17 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 18 + (cS σ) 17 =
      W * (cS σ) 18 + (yS σ) 18 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 18 = 0 := by
    rw [cols_none (j := 18) (by decide)]
  have hcol := s_col18 σ h
  rw [hc, zero_add]
  simpa [cS, yS, sLimb, sCarry] using hcol

theorem s_hrow19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 19 + (cS σ) 18 =
      W * (cS σ) 19 + (yS σ) 19 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 19 =
      (2 ^ 15 : ℤ) * ((σ 4144).val : ℤ) := by
    rw [cols_single (j := 19) (i0 := 13) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col19 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 20 + (cS σ) 19 =
      W * (cS σ) 20 + (yS σ) 20 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 20 =
      (2 ^ 54 : ℤ) * ((σ 4145).val : ℤ) := by
    rw [cols_single (j := 20) (i0 := 14) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col20 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 21 + (cS σ) 20 =
      W * (cS σ) 21 + (yS σ) 21 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 21 = 0 := by
    rw [cols_none (j := 21) (by decide)]
  have hcol := s_col21 σ h
  rw [hc, zero_add]
  simpa [cS, yS, sLimb, sCarry] using hcol

theorem s_hrow22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 22 + (cS σ) 21 =
      W * (cS σ) 22 + (yS σ) 22 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 22 =
      (2 ^ 11 : ℤ) * ((σ 4146).val : ℤ) := by
    rw [cols_single (j := 22) (i0 := 15) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col22 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 23 + (cS σ) 22 =
      W * (cS σ) 23 + (yS σ) 23 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 23 =
      (2 ^ 50 : ℤ) * ((σ 4147).val : ℤ) := by
    rw [cols_single (j := 23) (i0 := 16) (by norm_num) (by norm_num) (by decide)]
    simp [xS, sIn] <;> ring
  have hcol := s_col23 σ h
  rw [hc]
  simpa [cS, yS, sLimb, sCarry, mul_comm] using hcol

theorem s_hrow24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    Xark.Rsa.Convert.cols (xS σ) 24 + (cS σ) 23 = W * (cS σ) 24 + (yS σ) 24 := by
  have hc : Xark.Rsa.Convert.cols (xS σ) 24 = 0 := by
    rw [cols_none (j := 24) (by decide)]
  have hz := s_c24 σ h
  have hcol := s_col24 σ h
  rw [hc, zero_add, hz]
  simpa [cS, yS, sLimb, sCarry] using hcol

theorem s_hrow (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, Xark.Rsa.Convert.cols (xS σ) j +
      (if j = 0 then 0 else (cS σ) (j - 1)) = W * (cS σ) j + (yS σ) j := by
  intro j hj
  interval_cases j
  · simpa using s_row0 σ h
  · simpa using s_hrow1 σ h
  · simpa using s_hrow2 σ h
  · simpa using s_hrow3 σ h
  · simpa using s_hrow4 σ h
  · simpa using s_hrow5 σ h
  · simpa using s_hrow6 σ h
  · simpa using s_hrow7 σ h
  · simpa using s_hrow8 σ h
  · simpa using s_hrow9 σ h
  · simpa using s_hrow10 σ h
  · simpa using s_hrow11 σ h
  · simpa using s_hrow12 σ h
  · simpa using s_hrow13 σ h
  · simpa using s_hrow14 σ h
  · simpa using s_hrow15 σ h
  · simpa using s_hrow16 σ h
  · simpa using s_hrow17 σ h
  · simpa using s_hrow18 σ h
  · simpa using s_hrow19 σ h
  · simpa using s_hrow20 σ h
  · simpa using s_hrow21 σ h
  · simpa using s_hrow22 σ h
  · simpa using s_hrow23 σ h
  · simpa using s_hrow24 σ h

theorem s_convert_eq (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (∑ j ∈ Finset.range 25, (yS σ) j * (W : ℤ) ^ j)
      = ∑ i ∈ Finset.range 17, (xS σ) i * 2 ^ (121 * i) := by
  have := Xark.Rsa.Convert.telescoping (xS σ) (yS σ) (cS σ) (s_hrow σ h) (s_c24 σ h)
  simpa [Xark.Rsa.Convert.W, W] using this

end Xark.Circuits.Rsa2048
