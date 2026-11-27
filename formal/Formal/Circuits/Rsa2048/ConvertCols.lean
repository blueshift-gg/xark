/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.ConvertGlue

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# `convert_wide(n)`'s 25 carry rows

Generated from the s36 glue: one theorem per column of the modulus's conversion
(`convert_col_x` / `convert_col_prev` / `convert_col_x0`), so together they are
`RsaConvert.partial_sum`'s per-column hypothesis. The modulus's input limbs are the
input reader's plugs 0..16 (`n_plug0`/`pn_n0` are in `ConvertGlue`).
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

theorem n_plug1 : (wcallAt 0).env (.plug 1) = (LC.var 1 : GLC) := rfl

theorem pn_n1 (σ : ℕ → F) : pn (wcallAt 0) σ 1 = (σ 1).val := by
  simp [pn, Call.lift, n_plug1, LC.var, LC.eval]

theorem n_plug2 : (wcallAt 0).env (.plug 2) = (LC.var 2 : GLC) := rfl

theorem pn_n2 (σ : ℕ → F) : pn (wcallAt 0) σ 2 = (σ 2).val := by
  simp [pn, Call.lift, n_plug2, LC.var, LC.eval]

theorem n_plug3 : (wcallAt 0).env (.plug 3) = (LC.var 3 : GLC) := rfl

theorem pn_n3 (σ : ℕ → F) : pn (wcallAt 0) σ 3 = (σ 3).val := by
  simp [pn, Call.lift, n_plug3, LC.var, LC.eval]

theorem n_plug4 : (wcallAt 0).env (.plug 4) = (LC.var 4 : GLC) := rfl

theorem pn_n4 (σ : ℕ → F) : pn (wcallAt 0) σ 4 = (σ 4).val := by
  simp [pn, Call.lift, n_plug4, LC.var, LC.eval]

theorem n_plug5 : (wcallAt 0).env (.plug 5) = (LC.var 5 : GLC) := rfl

theorem pn_n5 (σ : ℕ → F) : pn (wcallAt 0) σ 5 = (σ 5).val := by
  simp [pn, Call.lift, n_plug5, LC.var, LC.eval]

theorem n_plug6 : (wcallAt 0).env (.plug 6) = (LC.var 6 : GLC) := rfl

theorem pn_n6 (σ : ℕ → F) : pn (wcallAt 0) σ 6 = (σ 6).val := by
  simp [pn, Call.lift, n_plug6, LC.var, LC.eval]

theorem n_plug7 : (wcallAt 0).env (.plug 7) = (LC.var 7 : GLC) := rfl

theorem pn_n7 (σ : ℕ → F) : pn (wcallAt 0) σ 7 = (σ 7).val := by
  simp [pn, Call.lift, n_plug7, LC.var, LC.eval]

theorem n_plug8 : (wcallAt 0).env (.plug 8) = (LC.var 8 : GLC) := rfl

theorem pn_n8 (σ : ℕ → F) : pn (wcallAt 0) σ 8 = (σ 8).val := by
  simp [pn, Call.lift, n_plug8, LC.var, LC.eval]

theorem n_plug9 : (wcallAt 0).env (.plug 9) = (LC.var 9 : GLC) := rfl

theorem pn_n9 (σ : ℕ → F) : pn (wcallAt 0) σ 9 = (σ 9).val := by
  simp [pn, Call.lift, n_plug9, LC.var, LC.eval]

theorem n_plug10 : (wcallAt 0).env (.plug 10) = (LC.var 10 : GLC) := rfl

theorem pn_n10 (σ : ℕ → F) : pn (wcallAt 0) σ 10 = (σ 10).val := by
  simp [pn, Call.lift, n_plug10, LC.var, LC.eval]

theorem n_plug11 : (wcallAt 0).env (.plug 11) = (LC.var 11 : GLC) := rfl

theorem pn_n11 (σ : ℕ → F) : pn (wcallAt 0) σ 11 = (σ 11).val := by
  simp [pn, Call.lift, n_plug11, LC.var, LC.eval]

theorem n_plug12 : (wcallAt 0).env (.plug 12) = (LC.var 12 : GLC) := rfl

theorem pn_n12 (σ : ℕ → F) : pn (wcallAt 0) σ 12 = (σ 12).val := by
  simp [pn, Call.lift, n_plug12, LC.var, LC.eval]

theorem n_plug13 : (wcallAt 0).env (.plug 13) = (LC.var 13 : GLC) := rfl

theorem pn_n13 (σ : ℕ → F) : pn (wcallAt 0) σ 13 = (σ 13).val := by
  simp [pn, Call.lift, n_plug13, LC.var, LC.eval]

theorem n_plug14 : (wcallAt 0).env (.plug 14) = (LC.var 14 : GLC) := rfl

theorem pn_n14 (σ : ℕ → F) : pn (wcallAt 0) σ 14 = (σ 14).val := by
  simp [pn, Call.lift, n_plug14, LC.var, LC.eval]

theorem n_plug15 : (wcallAt 0).env (.plug 15) = (LC.var 15 : GLC) := rfl

theorem pn_n15 (σ : ℕ → F) : pn (wcallAt 0) σ 15 = (σ 15).val := by
  simp [pn, Call.lift, n_plug15, LC.var, LC.eval]

theorem n_plug16 : (wcallAt 0).env (.plug 16) = (LC.var 16 : GLC) := rfl

theorem pn_n16 (σ : ℕ → F) : pn (wcallAt 0) σ 16 = (σ 16).val := by
  simp [pn, Call.lift, n_plug16, LC.var, LC.eval]

/-- Column 0: `x_0 = W·carry + limb`. -/
theorem n_col0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 0).val : ℤ) = (W : ℤ) * ((σ 16746).val : ℤ) + ((σ 16747).val : ℤ) := by
  refine convert_col_x0 σ h 0 (by decide) 0 16746 16747 ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 0) (by norm_num)
    rw [pn_n0] at hx
    exact hx
  · exact gblock_sound 16746 16911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 83) (by decide +kernel))
  · exact gblock_sound 16747 16748 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1) (by decide +kernel))

/-- Column 1: `2^39·x_1 + prev = W·carry + limb`. -/
theorem n_col1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 39 : ℤ) * ((σ 1).val : ℤ) + ((σ 16746).val : ℤ) =
      (W : ℤ) * ((σ 17146).val : ℤ) + ((σ 17147).val : ℤ) := by
  refine convert_col_x σ h 201 (by decide) 39 (by norm_num) 1 16746 17146 17147 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 1) (by norm_num)
    rw [pn_n1] at hx
    exact hx
  · exact gblock_sound 16746 16911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 83) (by decide +kernel))
  · exact gblock_sound 17146 17311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 284) (by decide +kernel))
  · exact gblock_sound 17147 17148 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 202) (by decide +kernel))

/-- Column 2: `2^78·x_2 + prev = W·carry + limb`. -/
theorem n_col2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 78 : ℤ) * ((σ 2).val : ℤ) + ((σ 17146).val : ℤ) =
      (W : ℤ) * ((σ 17546).val : ℤ) + ((σ 17547).val : ℤ) := by
  refine convert_col_x σ h 402 (by decide) 78 (by norm_num) 2 17146 17546 17547 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 2) (by norm_num)
    rw [pn_n2] at hx
    exact hx
  · exact gblock_sound 17146 17311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 284) (by decide +kernel))
  · exact gblock_sound 17546 17711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 485) (by decide +kernel))
  · exact gblock_sound 17547 17548 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 403) (by decide +kernel))

/-- Column 3: `prev = W·carry + limb`. -/
theorem n_col3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 17546).val : ℤ) = (W : ℤ) * ((σ 17946).val : ℤ) + ((σ 17947).val : ℤ) := by
  refine convert_col_prev σ h 603 (by decide) 17546 17946 17947 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 17546 17711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 485) (by decide +kernel))
  · exact gblock_sound 17946 18111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 686) (by decide +kernel))
  · exact gblock_sound 17947 17948 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 604) (by decide +kernel))

/-- Column 4: `2^35·x_3 + prev = W·carry + limb`. -/
theorem n_col4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 35 : ℤ) * ((σ 3).val : ℤ) + ((σ 17946).val : ℤ) =
      (W : ℤ) * ((σ 18346).val : ℤ) + ((σ 18347).val : ℤ) := by
  refine convert_col_x σ h 804 (by decide) 35 (by norm_num) 3 17946 18346 18347 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 3) (by norm_num)
    rw [pn_n3] at hx
    exact hx
  · exact gblock_sound 17946 18111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 686) (by decide +kernel))
  · exact gblock_sound 18346 18511 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 887) (by decide +kernel))
  · exact gblock_sound 18347 18348 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 805) (by decide +kernel))

/-- Column 5: `2^74·x_4 + prev = W·carry + limb`. -/
theorem n_col5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 74 : ℤ) * ((σ 4).val : ℤ) + ((σ 18346).val : ℤ) =
      (W : ℤ) * ((σ 18746).val : ℤ) + ((σ 18747).val : ℤ) := by
  refine convert_col_x σ h 1005 (by decide) 74 (by norm_num) 4 18346 18746 18747 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 4) (by norm_num)
    rw [pn_n4] at hx
    exact hx
  · exact gblock_sound 18346 18511 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 887) (by decide +kernel))
  · exact gblock_sound 18746 18911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1088) (by decide +kernel))
  · exact gblock_sound 18747 18748 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1006) (by decide +kernel))

/-- Column 6: `prev = W·carry + limb`. -/
theorem n_col6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 18746).val : ℤ) = (W : ℤ) * ((σ 19146).val : ℤ) + ((σ 19147).val : ℤ) := by
  refine convert_col_prev σ h 1206 (by decide) 18746 19146 19147 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 18746 18911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1088) (by decide +kernel))
  · exact gblock_sound 19146 19311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1289) (by decide +kernel))
  · exact gblock_sound 19147 19148 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1207) (by decide +kernel))

/-- Column 7: `2^31·x_5 + prev = W·carry + limb`. -/
theorem n_col7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 31 : ℤ) * ((σ 5).val : ℤ) + ((σ 19146).val : ℤ) =
      (W : ℤ) * ((σ 19546).val : ℤ) + ((σ 19547).val : ℤ) := by
  refine convert_col_x σ h 1407 (by decide) 31 (by norm_num) 5 19146 19546 19547 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 5) (by norm_num)
    rw [pn_n5] at hx
    exact hx
  · exact gblock_sound 19146 19311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1289) (by decide +kernel))
  · exact gblock_sound 19546 19711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1490) (by decide +kernel))
  · exact gblock_sound 19547 19548 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1408) (by decide +kernel))

/-- Column 8: `2^70·x_6 + prev = W·carry + limb`. -/
theorem n_col8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 70 : ℤ) * ((σ 6).val : ℤ) + ((σ 19546).val : ℤ) =
      (W : ℤ) * ((σ 19946).val : ℤ) + ((σ 19947).val : ℤ) := by
  refine convert_col_x σ h 1608 (by decide) 70 (by norm_num) 6 19546 19946 19947 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 6) (by norm_num)
    rw [pn_n6] at hx
    exact hx
  · exact gblock_sound 19546 19711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1490) (by decide +kernel))
  · exact gblock_sound 19946 20111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1691) (by decide +kernel))
  · exact gblock_sound 19947 19948 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1609) (by decide +kernel))

/-- Column 9: `prev = W·carry + limb`. -/
theorem n_col9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 19946).val : ℤ) = (W : ℤ) * ((σ 20346).val : ℤ) + ((σ 20347).val : ℤ) := by
  refine convert_col_prev σ h 1809 (by decide) 19946 20346 20347 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 19946 20111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1691) (by decide +kernel))
  · exact gblock_sound 20346 20511 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1892) (by decide +kernel))
  · exact gblock_sound 20347 20348 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1810) (by decide +kernel))

/-- Column 10: `2^27·x_7 + prev = W·carry + limb`. -/
theorem n_col10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 27 : ℤ) * ((σ 7).val : ℤ) + ((σ 20346).val : ℤ) =
      (W : ℤ) * ((σ 20746).val : ℤ) + ((σ 20747).val : ℤ) := by
  refine convert_col_x σ h 2010 (by decide) 27 (by norm_num) 7 20346 20746 20747 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 7) (by norm_num)
    rw [pn_n7] at hx
    exact hx
  · exact gblock_sound 20346 20511 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 1892) (by decide +kernel))
  · exact gblock_sound 20746 20911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2093) (by decide +kernel))
  · exact gblock_sound 20747 20748 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2011) (by decide +kernel))

/-- Column 11: `2^66·x_8 + prev = W·carry + limb`. -/
theorem n_col11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 66 : ℤ) * ((σ 8).val : ℤ) + ((σ 20746).val : ℤ) =
      (W : ℤ) * ((σ 21146).val : ℤ) + ((σ 21147).val : ℤ) := by
  refine convert_col_x σ h 2211 (by decide) 66 (by norm_num) 8 20746 21146 21147 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 8) (by norm_num)
    rw [pn_n8] at hx
    exact hx
  · exact gblock_sound 20746 20911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2093) (by decide +kernel))
  · exact gblock_sound 21146 21311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2294) (by decide +kernel))
  · exact gblock_sound 21147 21148 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2212) (by decide +kernel))

/-- Column 12: `prev = W·carry + limb`. -/
theorem n_col12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 21146).val : ℤ) = (W : ℤ) * ((σ 21546).val : ℤ) + ((σ 21547).val : ℤ) := by
  refine convert_col_prev σ h 2412 (by decide) 21146 21546 21547 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 21146 21311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2294) (by decide +kernel))
  · exact gblock_sound 21546 21711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2495) (by decide +kernel))
  · exact gblock_sound 21547 21548 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2413) (by decide +kernel))

/-- Column 13: `2^23·x_9 + prev = W·carry + limb`. -/
theorem n_col13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 23 : ℤ) * ((σ 9).val : ℤ) + ((σ 21546).val : ℤ) =
      (W : ℤ) * ((σ 21946).val : ℤ) + ((σ 21947).val : ℤ) := by
  refine convert_col_x σ h 2613 (by decide) 23 (by norm_num) 9 21546 21946 21947 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 9) (by norm_num)
    rw [pn_n9] at hx
    exact hx
  · exact gblock_sound 21546 21711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2495) (by decide +kernel))
  · exact gblock_sound 21946 22111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2696) (by decide +kernel))
  · exact gblock_sound 21947 21948 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2614) (by decide +kernel))

/-- Column 14: `2^62·x_10 + prev = W·carry + limb`. -/
theorem n_col14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 62 : ℤ) * ((σ 10).val : ℤ) + ((σ 21946).val : ℤ) =
      (W : ℤ) * ((σ 22346).val : ℤ) + ((σ 22347).val : ℤ) := by
  refine convert_col_x σ h 2814 (by decide) 62 (by norm_num) 10 21946 22346 22347 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 10) (by norm_num)
    rw [pn_n10] at hx
    exact hx
  · exact gblock_sound 21946 22111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2696) (by decide +kernel))
  · exact gblock_sound 22346 22511 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2897) (by decide +kernel))
  · exact gblock_sound 22347 22348 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2815) (by decide +kernel))

/-- Column 15: `prev = W·carry + limb`. -/
theorem n_col15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 22346).val : ℤ) = (W : ℤ) * ((σ 22746).val : ℤ) + ((σ 22747).val : ℤ) := by
  refine convert_col_prev σ h 3015 (by decide) 22346 22746 22747 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 22346 22511 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 2897) (by decide +kernel))
  · exact gblock_sound 22746 22911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3098) (by decide +kernel))
  · exact gblock_sound 22747 22748 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3016) (by decide +kernel))

/-- Column 16: `2^19·x_11 + prev = W·carry + limb`. -/
theorem n_col16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 19 : ℤ) * ((σ 11).val : ℤ) + ((σ 22746).val : ℤ) =
      (W : ℤ) * ((σ 23146).val : ℤ) + ((σ 23147).val : ℤ) := by
  refine convert_col_x σ h 3216 (by decide) 19 (by norm_num) 11 22746 23146 23147 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 11) (by norm_num)
    rw [pn_n11] at hx
    exact hx
  · exact gblock_sound 22746 22911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3098) (by decide +kernel))
  · exact gblock_sound 23146 23311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3299) (by decide +kernel))
  · exact gblock_sound 23147 23148 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3217) (by decide +kernel))

/-- Column 17: `2^58·x_12 + prev = W·carry + limb`. -/
theorem n_col17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 58 : ℤ) * ((σ 12).val : ℤ) + ((σ 23146).val : ℤ) =
      (W : ℤ) * ((σ 23546).val : ℤ) + ((σ 23547).val : ℤ) := by
  refine convert_col_x σ h 3417 (by decide) 58 (by norm_num) 12 23146 23546 23547 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 12) (by norm_num)
    rw [pn_n12] at hx
    exact hx
  · exact gblock_sound 23146 23311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3299) (by decide +kernel))
  · exact gblock_sound 23546 23711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3500) (by decide +kernel))
  · exact gblock_sound 23547 23548 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3418) (by decide +kernel))

/-- Column 18: `prev = W·carry + limb`. -/
theorem n_col18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 23546).val : ℤ) = (W : ℤ) * ((σ 23946).val : ℤ) + ((σ 23947).val : ℤ) := by
  refine convert_col_prev σ h 3618 (by decide) 23546 23946 23947 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 23546 23711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3500) (by decide +kernel))
  · exact gblock_sound 23946 24111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3701) (by decide +kernel))
  · exact gblock_sound 23947 23948 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3619) (by decide +kernel))

/-- Column 19: `2^15·x_13 + prev = W·carry + limb`. -/
theorem n_col19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 15 : ℤ) * ((σ 13).val : ℤ) + ((σ 23946).val : ℤ) =
      (W : ℤ) * ((σ 24346).val : ℤ) + ((σ 24347).val : ℤ) := by
  refine convert_col_x σ h 3819 (by decide) 15 (by norm_num) 13 23946 24346 24347 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 13) (by norm_num)
    rw [pn_n13] at hx
    exact hx
  · exact gblock_sound 23946 24111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3701) (by decide +kernel))
  · exact gblock_sound 24346 24511 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3902) (by decide +kernel))
  · exact gblock_sound 24347 24348 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3820) (by decide +kernel))

/-- Column 20: `2^54·x_14 + prev = W·carry + limb`. -/
theorem n_col20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 54 : ℤ) * ((σ 14).val : ℤ) + ((σ 24346).val : ℤ) =
      (W : ℤ) * ((σ 24746).val : ℤ) + ((σ 24747).val : ℤ) := by
  refine convert_col_x σ h 4020 (by decide) 54 (by norm_num) 14 24346 24746 24747 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 14) (by norm_num)
    rw [pn_n14] at hx
    exact hx
  · exact gblock_sound 24346 24511 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 3902) (by decide +kernel))
  · exact gblock_sound 24746 24911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4103) (by decide +kernel))
  · exact gblock_sound 24747 24748 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4021) (by decide +kernel))

/-- Column 21: `prev = W·carry + limb`. -/
theorem n_col21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 24746).val : ℤ) = (W : ℤ) * ((σ 25146).val : ℤ) + ((σ 25147).val : ℤ) := by
  refine convert_col_prev σ h 4221 (by decide) 24746 25146 25147 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 24746 24911 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4103) (by decide +kernel))
  · exact gblock_sound 25146 25311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4304) (by decide +kernel))
  · exact gblock_sound 25147 25148 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4222) (by decide +kernel))

/-- Column 22: `2^11·x_15 + prev = W·carry + limb`. -/
theorem n_col22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 11 : ℤ) * ((σ 15).val : ℤ) + ((σ 25146).val : ℤ) =
      (W : ℤ) * ((σ 25546).val : ℤ) + ((σ 25547).val : ℤ) := by
  refine convert_col_x σ h 4422 (by decide) 11 (by norm_num) 15 25146 25546 25547 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 15) (by norm_num)
    rw [pn_n15] at hx
    exact hx
  · exact gblock_sound 25146 25311 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4304) (by decide +kernel))
  · exact gblock_sound 25546 25711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4505) (by decide +kernel))
  · exact gblock_sound 25547 25548 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4423) (by decide +kernel))

/-- Column 23: `2^50·x_16 + prev = W·carry + limb`. -/
theorem n_col23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 50 : ℤ) * ((σ 16).val : ℤ) + ((σ 25546).val : ℤ) =
      (W : ℤ) * ((σ 25946).val : ℤ) + ((σ 25947).val : ℤ) := by
  refine convert_col_x σ h 4623 (by decide) 50 (by norm_num) 16 25546 25946 25947 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := n_limb_bound σ h (j := 16) (by norm_num)
    rw [pn_n16] at hx
    exact hx
  · exact gblock_sound 25546 25711 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4505) (by decide +kernel))
  · exact gblock_sound 25946 26111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4706) (by decide +kernel))
  · exact gblock_sound 25947 25948 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4624) (by decide +kernel))

/-- Column 24: the final carry is required 0. -/
theorem n_col24_row (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 26346) = 0 := by
  have hr := growAt_sat (s36_sat h) 4825 (by decide)
  have hrow : growAt 4825 = ⟨⟨0, [((1 : F), 26346)]⟩, ⟨1, []⟩, ⟨0, []⟩⟩ := by decide +kernel
  rw [hrow] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

/-- Column 24: the final carry telescopes out. -/
theorem n_col24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 25946).val : ℤ) = (W : ℤ) * 0 + ((σ 26347).val : ℤ) := by
  have hz := n_col24_row σ h
  have hc : (σ 26346).val < 2 ^ 118 := by rw [hz, ZMod.val_zero]; norm_num
  have hp : (σ 25946).val < 2 ^ 118 := gblock_sound 25946 26111 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4706) (by decide +kernel))
  have hl80 : (σ 26347).val < 2 ^ 80 := gblock_sound 26347 26348 80 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4826) (by decide +kernel))
  have hl : (σ 26347).val < 2 ^ 82 := Nat.lt_of_lt_of_le hl80 (by norm_num)
  have hcol := convert_col_prev σ h 4824 (by decide) 25946 26346 26347 (by decide +kernel) hp hc hl
  rw [hz, ZMod.val_zero, Nat.cast_zero, mul_zero, zero_add] at hcol
  simpa using hcol

end Xark.Circuits.Rsa2048
