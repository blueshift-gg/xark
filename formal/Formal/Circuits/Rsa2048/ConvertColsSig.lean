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
# `convert_wide(sig)`'s 25 carry rows

The signature operand's counterpart of `ConvertCols.lean`: same generator, base row
4906, input reader call 1, input limbs at variables 4131..4147.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

theorem s_plug0 : (wcallAt 1).env (.plug 0) = (LC.var 4131 : GLC) := rfl

theorem pn_s0 (σ : ℕ → F) : pn (wcallAt 1) σ 0 = (σ 4131).val := by
  simp [pn, Call.lift, s_plug0, LC.var, LC.eval]

theorem s_plug1 : (wcallAt 1).env (.plug 1) = (LC.var 4132 : GLC) := rfl

theorem pn_s1 (σ : ℕ → F) : pn (wcallAt 1) σ 1 = (σ 4132).val := by
  simp [pn, Call.lift, s_plug1, LC.var, LC.eval]

theorem s_plug2 : (wcallAt 1).env (.plug 2) = (LC.var 4133 : GLC) := rfl

theorem pn_s2 (σ : ℕ → F) : pn (wcallAt 1) σ 2 = (σ 4133).val := by
  simp [pn, Call.lift, s_plug2, LC.var, LC.eval]

theorem s_plug3 : (wcallAt 1).env (.plug 3) = (LC.var 4134 : GLC) := rfl

theorem pn_s3 (σ : ℕ → F) : pn (wcallAt 1) σ 3 = (σ 4134).val := by
  simp [pn, Call.lift, s_plug3, LC.var, LC.eval]

theorem s_plug4 : (wcallAt 1).env (.plug 4) = (LC.var 4135 : GLC) := rfl

theorem pn_s4 (σ : ℕ → F) : pn (wcallAt 1) σ 4 = (σ 4135).val := by
  simp [pn, Call.lift, s_plug4, LC.var, LC.eval]

theorem s_plug5 : (wcallAt 1).env (.plug 5) = (LC.var 4136 : GLC) := rfl

theorem pn_s5 (σ : ℕ → F) : pn (wcallAt 1) σ 5 = (σ 4136).val := by
  simp [pn, Call.lift, s_plug5, LC.var, LC.eval]

theorem s_plug6 : (wcallAt 1).env (.plug 6) = (LC.var 4137 : GLC) := rfl

theorem pn_s6 (σ : ℕ → F) : pn (wcallAt 1) σ 6 = (σ 4137).val := by
  simp [pn, Call.lift, s_plug6, LC.var, LC.eval]

theorem s_plug7 : (wcallAt 1).env (.plug 7) = (LC.var 4138 : GLC) := rfl

theorem pn_s7 (σ : ℕ → F) : pn (wcallAt 1) σ 7 = (σ 4138).val := by
  simp [pn, Call.lift, s_plug7, LC.var, LC.eval]

theorem s_plug8 : (wcallAt 1).env (.plug 8) = (LC.var 4139 : GLC) := rfl

theorem pn_s8 (σ : ℕ → F) : pn (wcallAt 1) σ 8 = (σ 4139).val := by
  simp [pn, Call.lift, s_plug8, LC.var, LC.eval]

theorem s_plug9 : (wcallAt 1).env (.plug 9) = (LC.var 4140 : GLC) := rfl

theorem pn_s9 (σ : ℕ → F) : pn (wcallAt 1) σ 9 = (σ 4140).val := by
  simp [pn, Call.lift, s_plug9, LC.var, LC.eval]

theorem s_plug10 : (wcallAt 1).env (.plug 10) = (LC.var 4141 : GLC) := rfl

theorem pn_s10 (σ : ℕ → F) : pn (wcallAt 1) σ 10 = (σ 4141).val := by
  simp [pn, Call.lift, s_plug10, LC.var, LC.eval]

theorem s_plug11 : (wcallAt 1).env (.plug 11) = (LC.var 4142 : GLC) := rfl

theorem pn_s11 (σ : ℕ → F) : pn (wcallAt 1) σ 11 = (σ 4142).val := by
  simp [pn, Call.lift, s_plug11, LC.var, LC.eval]

theorem s_plug12 : (wcallAt 1).env (.plug 12) = (LC.var 4143 : GLC) := rfl

theorem pn_s12 (σ : ℕ → F) : pn (wcallAt 1) σ 12 = (σ 4143).val := by
  simp [pn, Call.lift, s_plug12, LC.var, LC.eval]

theorem s_plug13 : (wcallAt 1).env (.plug 13) = (LC.var 4144 : GLC) := rfl

theorem pn_s13 (σ : ℕ → F) : pn (wcallAt 1) σ 13 = (σ 4144).val := by
  simp [pn, Call.lift, s_plug13, LC.var, LC.eval]

theorem s_plug14 : (wcallAt 1).env (.plug 14) = (LC.var 4145 : GLC) := rfl

theorem pn_s14 (σ : ℕ → F) : pn (wcallAt 1) σ 14 = (σ 4145).val := by
  simp [pn, Call.lift, s_plug14, LC.var, LC.eval]

theorem s_plug15 : (wcallAt 1).env (.plug 15) = (LC.var 4146 : GLC) := rfl

theorem pn_s15 (σ : ℕ → F) : pn (wcallAt 1) σ 15 = (σ 4146).val := by
  simp [pn, Call.lift, s_plug15, LC.var, LC.eval]

theorem s_plug16 : (wcallAt 1).env (.plug 16) = (LC.var 4147 : GLC) := rfl

theorem pn_s16 (σ : ℕ → F) : pn (wcallAt 1) σ 16 = (σ 4147).val := by
  simp [pn, Call.lift, s_plug16, LC.var, LC.eval]

theorem s_col0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 4131).val : ℤ) = (W : ℤ) * ((σ 26507).val : ℤ) + ((σ 26508).val : ℤ) := by
  refine convert_col_x0 σ h 4906 (by decide) 4131 26507 26508 ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 0) (by norm_num)
    rw [pn_s0] at hx
    exact hx
  · exact gblock_sound 26507 26672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4989) (by decide +kernel))
  · exact gblock_sound 26508 26509 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4907) (by decide +kernel))

theorem s_col1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 39 : ℤ) * ((σ 4132).val : ℤ) + ((σ 26507).val : ℤ) =
      (W : ℤ) * ((σ 26907).val : ℤ) + ((σ 26908).val : ℤ) := by
  refine convert_col_x σ h 5107 (by decide) 39 (by norm_num) 4132 26507 26907 26908 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 1) (by norm_num)
    rw [pn_s1] at hx
    exact hx
  · exact gblock_sound 26507 26672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 4989) (by decide +kernel))
  · exact gblock_sound 26907 27072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5190) (by decide +kernel))
  · exact gblock_sound 26908 26909 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5108) (by decide +kernel))

theorem s_col2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 78 : ℤ) * ((σ 4133).val : ℤ) + ((σ 26907).val : ℤ) =
      (W : ℤ) * ((σ 27307).val : ℤ) + ((σ 27308).val : ℤ) := by
  refine convert_col_x σ h 5308 (by decide) 78 (by norm_num) 4133 26907 27307 27308 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 2) (by norm_num)
    rw [pn_s2] at hx
    exact hx
  · exact gblock_sound 26907 27072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5190) (by decide +kernel))
  · exact gblock_sound 27307 27472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5391) (by decide +kernel))
  · exact gblock_sound 27308 27309 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5309) (by decide +kernel))

theorem s_col3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 27307).val : ℤ) = (W : ℤ) * ((σ 27707).val : ℤ) + ((σ 27708).val : ℤ) := by
  refine convert_col_prev σ h 5509 (by decide) 27307 27707 27708 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 27307 27472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5391) (by decide +kernel))
  · exact gblock_sound 27707 27872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5592) (by decide +kernel))
  · exact gblock_sound 27708 27709 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5510) (by decide +kernel))

theorem s_col4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 35 : ℤ) * ((σ 4134).val : ℤ) + ((σ 27707).val : ℤ) =
      (W : ℤ) * ((σ 28107).val : ℤ) + ((σ 28108).val : ℤ) := by
  refine convert_col_x σ h 5710 (by decide) 35 (by norm_num) 4134 27707 28107 28108 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 3) (by norm_num)
    rw [pn_s3] at hx
    exact hx
  · exact gblock_sound 27707 27872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5592) (by decide +kernel))
  · exact gblock_sound 28107 28272 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5793) (by decide +kernel))
  · exact gblock_sound 28108 28109 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5711) (by decide +kernel))

theorem s_col5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 74 : ℤ) * ((σ 4135).val : ℤ) + ((σ 28107).val : ℤ) =
      (W : ℤ) * ((σ 28507).val : ℤ) + ((σ 28508).val : ℤ) := by
  refine convert_col_x σ h 5911 (by decide) 74 (by norm_num) 4135 28107 28507 28508 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 4) (by norm_num)
    rw [pn_s4] at hx
    exact hx
  · exact gblock_sound 28107 28272 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5793) (by decide +kernel))
  · exact gblock_sound 28507 28672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5994) (by decide +kernel))
  · exact gblock_sound 28508 28509 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5912) (by decide +kernel))

theorem s_col6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 28507).val : ℤ) = (W : ℤ) * ((σ 28907).val : ℤ) + ((σ 28908).val : ℤ) := by
  refine convert_col_prev σ h 6112 (by decide) 28507 28907 28908 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 28507 28672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 5994) (by decide +kernel))
  · exact gblock_sound 28907 29072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6195) (by decide +kernel))
  · exact gblock_sound 28908 28909 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6113) (by decide +kernel))

theorem s_col7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 31 : ℤ) * ((σ 4136).val : ℤ) + ((σ 28907).val : ℤ) =
      (W : ℤ) * ((σ 29307).val : ℤ) + ((σ 29308).val : ℤ) := by
  refine convert_col_x σ h 6313 (by decide) 31 (by norm_num) 4136 28907 29307 29308 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 5) (by norm_num)
    rw [pn_s5] at hx
    exact hx
  · exact gblock_sound 28907 29072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6195) (by decide +kernel))
  · exact gblock_sound 29307 29472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6396) (by decide +kernel))
  · exact gblock_sound 29308 29309 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6314) (by decide +kernel))

theorem s_col8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 70 : ℤ) * ((σ 4137).val : ℤ) + ((σ 29307).val : ℤ) =
      (W : ℤ) * ((σ 29707).val : ℤ) + ((σ 29708).val : ℤ) := by
  refine convert_col_x σ h 6514 (by decide) 70 (by norm_num) 4137 29307 29707 29708 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 6) (by norm_num)
    rw [pn_s6] at hx
    exact hx
  · exact gblock_sound 29307 29472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6396) (by decide +kernel))
  · exact gblock_sound 29707 29872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6597) (by decide +kernel))
  · exact gblock_sound 29708 29709 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6515) (by decide +kernel))

theorem s_col9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 29707).val : ℤ) = (W : ℤ) * ((σ 30107).val : ℤ) + ((σ 30108).val : ℤ) := by
  refine convert_col_prev σ h 6715 (by decide) 29707 30107 30108 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 29707 29872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6597) (by decide +kernel))
  · exact gblock_sound 30107 30272 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6798) (by decide +kernel))
  · exact gblock_sound 30108 30109 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6716) (by decide +kernel))

theorem s_col10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 27 : ℤ) * ((σ 4138).val : ℤ) + ((σ 30107).val : ℤ) =
      (W : ℤ) * ((σ 30507).val : ℤ) + ((σ 30508).val : ℤ) := by
  refine convert_col_x σ h 6916 (by decide) 27 (by norm_num) 4138 30107 30507 30508 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 7) (by norm_num)
    rw [pn_s7] at hx
    exact hx
  · exact gblock_sound 30107 30272 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6798) (by decide +kernel))
  · exact gblock_sound 30507 30672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6999) (by decide +kernel))
  · exact gblock_sound 30508 30509 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6917) (by decide +kernel))

theorem s_col11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 66 : ℤ) * ((σ 4139).val : ℤ) + ((σ 30507).val : ℤ) =
      (W : ℤ) * ((σ 30907).val : ℤ) + ((σ 30908).val : ℤ) := by
  refine convert_col_x σ h 7117 (by decide) 66 (by norm_num) 4139 30507 30907 30908 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 8) (by norm_num)
    rw [pn_s8] at hx
    exact hx
  · exact gblock_sound 30507 30672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 6999) (by decide +kernel))
  · exact gblock_sound 30907 31072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7200) (by decide +kernel))
  · exact gblock_sound 30908 30909 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7118) (by decide +kernel))

theorem s_col12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 30907).val : ℤ) = (W : ℤ) * ((σ 31307).val : ℤ) + ((σ 31308).val : ℤ) := by
  refine convert_col_prev σ h 7318 (by decide) 30907 31307 31308 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 30907 31072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7200) (by decide +kernel))
  · exact gblock_sound 31307 31472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7401) (by decide +kernel))
  · exact gblock_sound 31308 31309 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7319) (by decide +kernel))

theorem s_col13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 23 : ℤ) * ((σ 4140).val : ℤ) + ((σ 31307).val : ℤ) =
      (W : ℤ) * ((σ 31707).val : ℤ) + ((σ 31708).val : ℤ) := by
  refine convert_col_x σ h 7519 (by decide) 23 (by norm_num) 4140 31307 31707 31708 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 9) (by norm_num)
    rw [pn_s9] at hx
    exact hx
  · exact gblock_sound 31307 31472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7401) (by decide +kernel))
  · exact gblock_sound 31707 31872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7602) (by decide +kernel))
  · exact gblock_sound 31708 31709 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7520) (by decide +kernel))

theorem s_col14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 62 : ℤ) * ((σ 4141).val : ℤ) + ((σ 31707).val : ℤ) =
      (W : ℤ) * ((σ 32107).val : ℤ) + ((σ 32108).val : ℤ) := by
  refine convert_col_x σ h 7720 (by decide) 62 (by norm_num) 4141 31707 32107 32108 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 10) (by norm_num)
    rw [pn_s10] at hx
    exact hx
  · exact gblock_sound 31707 31872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7602) (by decide +kernel))
  · exact gblock_sound 32107 32272 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7803) (by decide +kernel))
  · exact gblock_sound 32108 32109 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7721) (by decide +kernel))

theorem s_col15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 32107).val : ℤ) = (W : ℤ) * ((σ 32507).val : ℤ) + ((σ 32508).val : ℤ) := by
  refine convert_col_prev σ h 7921 (by decide) 32107 32507 32508 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 32107 32272 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7803) (by decide +kernel))
  · exact gblock_sound 32507 32672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8004) (by decide +kernel))
  · exact gblock_sound 32508 32509 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 7922) (by decide +kernel))

theorem s_col16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 19 : ℤ) * ((σ 4142).val : ℤ) + ((σ 32507).val : ℤ) =
      (W : ℤ) * ((σ 32907).val : ℤ) + ((σ 32908).val : ℤ) := by
  refine convert_col_x σ h 8122 (by decide) 19 (by norm_num) 4142 32507 32907 32908 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 11) (by norm_num)
    rw [pn_s11] at hx
    exact hx
  · exact gblock_sound 32507 32672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8004) (by decide +kernel))
  · exact gblock_sound 32907 33072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8205) (by decide +kernel))
  · exact gblock_sound 32908 32909 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8123) (by decide +kernel))

theorem s_col17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 58 : ℤ) * ((σ 4143).val : ℤ) + ((σ 32907).val : ℤ) =
      (W : ℤ) * ((σ 33307).val : ℤ) + ((σ 33308).val : ℤ) := by
  refine convert_col_x σ h 8323 (by decide) 58 (by norm_num) 4143 32907 33307 33308 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 12) (by norm_num)
    rw [pn_s12] at hx
    exact hx
  · exact gblock_sound 32907 33072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8205) (by decide +kernel))
  · exact gblock_sound 33307 33472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8406) (by decide +kernel))
  · exact gblock_sound 33308 33309 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8324) (by decide +kernel))

theorem s_col18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 33307).val : ℤ) = (W : ℤ) * ((σ 33707).val : ℤ) + ((σ 33708).val : ℤ) := by
  refine convert_col_prev σ h 8524 (by decide) 33307 33707 33708 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 33307 33472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8406) (by decide +kernel))
  · exact gblock_sound 33707 33872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8607) (by decide +kernel))
  · exact gblock_sound 33708 33709 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8525) (by decide +kernel))

theorem s_col19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 15 : ℤ) * ((σ 4144).val : ℤ) + ((σ 33707).val : ℤ) =
      (W : ℤ) * ((σ 34107).val : ℤ) + ((σ 34108).val : ℤ) := by
  refine convert_col_x σ h 8725 (by decide) 15 (by norm_num) 4144 33707 34107 34108 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 13) (by norm_num)
    rw [pn_s13] at hx
    exact hx
  · exact gblock_sound 33707 33872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8607) (by decide +kernel))
  · exact gblock_sound 34107 34272 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8808) (by decide +kernel))
  · exact gblock_sound 34108 34109 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8726) (by decide +kernel))

theorem s_col20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 54 : ℤ) * ((σ 4145).val : ℤ) + ((σ 34107).val : ℤ) =
      (W : ℤ) * ((σ 34507).val : ℤ) + ((σ 34508).val : ℤ) := by
  refine convert_col_x σ h 8926 (by decide) 54 (by norm_num) 4145 34107 34507 34508 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 14) (by norm_num)
    rw [pn_s14] at hx
    exact hx
  · exact gblock_sound 34107 34272 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8808) (by decide +kernel))
  · exact gblock_sound 34507 34672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9009) (by decide +kernel))
  · exact gblock_sound 34508 34509 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 8927) (by decide +kernel))

theorem s_col21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 34507).val : ℤ) = (W : ℤ) * ((σ 34907).val : ℤ) + ((σ 34908).val : ℤ) := by
  refine convert_col_prev σ h 9127 (by decide) 34507 34907 34908 ?_ ?_ ?_ ?_
  · decide +kernel
  · exact gblock_sound 34507 34672 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9009) (by decide +kernel))
  · exact gblock_sound 34907 35072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9210) (by decide +kernel))
  · exact gblock_sound 34908 34909 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9128) (by decide +kernel))

theorem s_col22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 11 : ℤ) * ((σ 4146).val : ℤ) + ((σ 34907).val : ℤ) =
      (W : ℤ) * ((σ 35307).val : ℤ) + ((σ 35308).val : ℤ) := by
  refine convert_col_x σ h 9328 (by decide) 11 (by norm_num) 4146 34907 35307 35308 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 15) (by norm_num)
    rw [pn_s15] at hx
    exact hx
  · exact gblock_sound 34907 35072 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9210) (by decide +kernel))
  · exact gblock_sound 35307 35472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9411) (by decide +kernel))
  · exact gblock_sound 35308 35309 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9329) (by decide +kernel))

theorem s_col23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (2 ^ 50 : ℤ) * ((σ 4147).val : ℤ) + ((σ 35307).val : ℤ) =
      (W : ℤ) * ((σ 35707).val : ℤ) + ((σ 35708).val : ℤ) := by
  refine convert_col_x σ h 9529 (by decide) 50 (by norm_num) 4147 35307 35707 35708 ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · have hx := sig_limb_bound σ h (j := 16) (by norm_num)
    rw [pn_s16] at hx
    exact hx
  · exact gblock_sound 35307 35472 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9411) (by decide +kernel))
  · exact gblock_sound 35707 35872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9612) (by decide +kernel))
  · exact gblock_sound 35708 35709 82 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9530) (by decide +kernel))

theorem s_col24_row (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 36107) = 0 := by
  have hr := growAt_sat (s36_sat h) 9731 (by decide)
  have hrow : growAt 9731 = ⟨⟨0, [((1 : F), 36107)]⟩, ⟨1, []⟩, ⟨0, []⟩⟩ := by decide +kernel
  rw [hrow] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem s_col24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 35707).val : ℤ) = (W : ℤ) * 0 + ((σ 36108).val : ℤ) := by
  have hz := s_col24_row σ h
  have hc : (σ 36107).val < 2 ^ 118 := by rw [hz, ZMod.val_zero]; norm_num
  have hp : (σ 35707).val < 2 ^ 118 := gblock_sound 35707 35872 118 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9612) (by decide +kernel))
  have hl80 : (σ 36108).val < 2 ^ 80 := gblock_sound 36108 36109 80 (by norm_num) (by norm_num) σ (gblock_sat (s36_sat h) (k := 9732) (by decide +kernel))
  have hl : (σ 36108).val < 2 ^ 82 := Nat.lt_of_lt_of_le hl80 (by norm_num)
  have hcol := convert_col_prev σ h 9730 (by decide) 35707 36107 36108 (by decide +kernel) hp hc hl
  rw [hz, ZMod.val_zero, Nat.cast_zero, mul_zero, zero_add] at hcol
  simpa using hcol

end Xark.Circuits.Rsa2048
