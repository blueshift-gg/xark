/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.ConvertTop
import Formal.Circuits.Rsa2048.SigLt

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# The words `minus_one(n)` tail (s36 indices 9813..9912)

The same lowering as the byte path's `s544`: per limb `i` an `is_zero` gadget
(`m_i·w_i = z_i`, `m_i·(1−z_i) = 0`, `w_i·(1−z_i) = 0`) and a borrow product
(`borrow_{i+1}·(1−z_{i+1}) = borrow_{i+2}`), ending `borrow_25 = 0`, with
`out_i = n_i − borrow_i + W·borrow_{i+1}`. This file holds the model and the row
shapes; the `SigLt`-style algebra follows.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- The `is_zero` variable for limb `j`. -/
def mzvar (j : ℕ) : ℕ := if j = 0 then 36269 else 36273 + 5 * (j - 1)

/-- The `is_zero` inverse variable for limb `j`. -/
def mwvar (j : ℕ) : ℕ := mzvar j - 1

/-- `borrow_{i+2}`'s variable (the product row's `c`). -/
def mnxt (i : ℕ) : ℕ := 36276 + 5 * i

/-- `1 − z_j`, the `is_zero` bit of limb `j`. -/
def mbLC (j : ℕ) : ZLC := ⟨1, [(-1, mzvar j)]⟩

/-- The borrow vector: `borrow_0 = 1`, `borrow_1 = b_0`, then the product hints. -/
def mborrow : ℕ → ZLC
  | 0 => ⟨1, []⟩
  | 1 => mbLC 0
  | (i + 2) => ⟨0, [(1, mnxt i)]⟩

theorem mE1_0 : growAt 9813 =
    ⟨⟨0, [((1 : F), 16747)]⟩, ⟨0, [((1 : F), 36268)]⟩, ⟨0, [((1 : F), 36269)]⟩⟩ := by
  decide +kernel

theorem mE2_0 : growAt 9814 =
    ⟨⟨0, [((1 : F), 16747)]⟩, ⟨1, [((-1 : F), 36269)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_0 : growAt 9815 =
    ⟨⟨0, [((1 : F), 36268)]⟩, ⟨1, [((-1 : F), 36269)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_1 : growAt 9816 =
    ⟨⟨0, [((1 : F), 17147)]⟩, ⟨0, [((1 : F), 36272)]⟩, ⟨0, [((1 : F), 36273)]⟩⟩ := by
  decide +kernel

theorem mE2_1 : growAt 9817 =
    ⟨⟨0, [((1 : F), 17147)]⟩, ⟨1, [((-1 : F), 36273)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_1 : growAt 9818 =
    ⟨⟨0, [((1 : F), 36272)]⟩, ⟨1, [((-1 : F), 36273)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_2 : growAt 9820 =
    ⟨⟨0, [((1 : F), 17547)]⟩, ⟨0, [((1 : F), 36277)]⟩, ⟨0, [((1 : F), 36278)]⟩⟩ := by
  decide +kernel

theorem mE2_2 : growAt 9821 =
    ⟨⟨0, [((1 : F), 17547)]⟩, ⟨1, [((-1 : F), 36278)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_2 : growAt 9822 =
    ⟨⟨0, [((1 : F), 36277)]⟩, ⟨1, [((-1 : F), 36278)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_3 : growAt 9824 =
    ⟨⟨0, [((1 : F), 17947)]⟩, ⟨0, [((1 : F), 36282)]⟩, ⟨0, [((1 : F), 36283)]⟩⟩ := by
  decide +kernel

theorem mE2_3 : growAt 9825 =
    ⟨⟨0, [((1 : F), 17947)]⟩, ⟨1, [((-1 : F), 36283)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_3 : growAt 9826 =
    ⟨⟨0, [((1 : F), 36282)]⟩, ⟨1, [((-1 : F), 36283)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_4 : growAt 9828 =
    ⟨⟨0, [((1 : F), 18347)]⟩, ⟨0, [((1 : F), 36287)]⟩, ⟨0, [((1 : F), 36288)]⟩⟩ := by
  decide +kernel

theorem mE2_4 : growAt 9829 =
    ⟨⟨0, [((1 : F), 18347)]⟩, ⟨1, [((-1 : F), 36288)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_4 : growAt 9830 =
    ⟨⟨0, [((1 : F), 36287)]⟩, ⟨1, [((-1 : F), 36288)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_5 : growAt 9832 =
    ⟨⟨0, [((1 : F), 18747)]⟩, ⟨0, [((1 : F), 36292)]⟩, ⟨0, [((1 : F), 36293)]⟩⟩ := by
  decide +kernel

theorem mE2_5 : growAt 9833 =
    ⟨⟨0, [((1 : F), 18747)]⟩, ⟨1, [((-1 : F), 36293)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_5 : growAt 9834 =
    ⟨⟨0, [((1 : F), 36292)]⟩, ⟨1, [((-1 : F), 36293)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_6 : growAt 9836 =
    ⟨⟨0, [((1 : F), 19147)]⟩, ⟨0, [((1 : F), 36297)]⟩, ⟨0, [((1 : F), 36298)]⟩⟩ := by
  decide +kernel

theorem mE2_6 : growAt 9837 =
    ⟨⟨0, [((1 : F), 19147)]⟩, ⟨1, [((-1 : F), 36298)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_6 : growAt 9838 =
    ⟨⟨0, [((1 : F), 36297)]⟩, ⟨1, [((-1 : F), 36298)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_7 : growAt 9840 =
    ⟨⟨0, [((1 : F), 19547)]⟩, ⟨0, [((1 : F), 36302)]⟩, ⟨0, [((1 : F), 36303)]⟩⟩ := by
  decide +kernel

theorem mE2_7 : growAt 9841 =
    ⟨⟨0, [((1 : F), 19547)]⟩, ⟨1, [((-1 : F), 36303)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_7 : growAt 9842 =
    ⟨⟨0, [((1 : F), 36302)]⟩, ⟨1, [((-1 : F), 36303)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_8 : growAt 9844 =
    ⟨⟨0, [((1 : F), 19947)]⟩, ⟨0, [((1 : F), 36307)]⟩, ⟨0, [((1 : F), 36308)]⟩⟩ := by
  decide +kernel

theorem mE2_8 : growAt 9845 =
    ⟨⟨0, [((1 : F), 19947)]⟩, ⟨1, [((-1 : F), 36308)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_8 : growAt 9846 =
    ⟨⟨0, [((1 : F), 36307)]⟩, ⟨1, [((-1 : F), 36308)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_9 : growAt 9848 =
    ⟨⟨0, [((1 : F), 20347)]⟩, ⟨0, [((1 : F), 36312)]⟩, ⟨0, [((1 : F), 36313)]⟩⟩ := by
  decide +kernel

theorem mE2_9 : growAt 9849 =
    ⟨⟨0, [((1 : F), 20347)]⟩, ⟨1, [((-1 : F), 36313)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_9 : growAt 9850 =
    ⟨⟨0, [((1 : F), 36312)]⟩, ⟨1, [((-1 : F), 36313)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_10 : growAt 9852 =
    ⟨⟨0, [((1 : F), 20747)]⟩, ⟨0, [((1 : F), 36317)]⟩, ⟨0, [((1 : F), 36318)]⟩⟩ := by
  decide +kernel

theorem mE2_10 : growAt 9853 =
    ⟨⟨0, [((1 : F), 20747)]⟩, ⟨1, [((-1 : F), 36318)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_10 : growAt 9854 =
    ⟨⟨0, [((1 : F), 36317)]⟩, ⟨1, [((-1 : F), 36318)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_11 : growAt 9856 =
    ⟨⟨0, [((1 : F), 21147)]⟩, ⟨0, [((1 : F), 36322)]⟩, ⟨0, [((1 : F), 36323)]⟩⟩ := by
  decide +kernel

theorem mE2_11 : growAt 9857 =
    ⟨⟨0, [((1 : F), 21147)]⟩, ⟨1, [((-1 : F), 36323)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_11 : growAt 9858 =
    ⟨⟨0, [((1 : F), 36322)]⟩, ⟨1, [((-1 : F), 36323)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_12 : growAt 9860 =
    ⟨⟨0, [((1 : F), 21547)]⟩, ⟨0, [((1 : F), 36327)]⟩, ⟨0, [((1 : F), 36328)]⟩⟩ := by
  decide +kernel

theorem mE2_12 : growAt 9861 =
    ⟨⟨0, [((1 : F), 21547)]⟩, ⟨1, [((-1 : F), 36328)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_12 : growAt 9862 =
    ⟨⟨0, [((1 : F), 36327)]⟩, ⟨1, [((-1 : F), 36328)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_13 : growAt 9864 =
    ⟨⟨0, [((1 : F), 21947)]⟩, ⟨0, [((1 : F), 36332)]⟩, ⟨0, [((1 : F), 36333)]⟩⟩ := by
  decide +kernel

theorem mE2_13 : growAt 9865 =
    ⟨⟨0, [((1 : F), 21947)]⟩, ⟨1, [((-1 : F), 36333)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_13 : growAt 9866 =
    ⟨⟨0, [((1 : F), 36332)]⟩, ⟨1, [((-1 : F), 36333)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_14 : growAt 9868 =
    ⟨⟨0, [((1 : F), 22347)]⟩, ⟨0, [((1 : F), 36337)]⟩, ⟨0, [((1 : F), 36338)]⟩⟩ := by
  decide +kernel

theorem mE2_14 : growAt 9869 =
    ⟨⟨0, [((1 : F), 22347)]⟩, ⟨1, [((-1 : F), 36338)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_14 : growAt 9870 =
    ⟨⟨0, [((1 : F), 36337)]⟩, ⟨1, [((-1 : F), 36338)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_15 : growAt 9872 =
    ⟨⟨0, [((1 : F), 22747)]⟩, ⟨0, [((1 : F), 36342)]⟩, ⟨0, [((1 : F), 36343)]⟩⟩ := by
  decide +kernel

theorem mE2_15 : growAt 9873 =
    ⟨⟨0, [((1 : F), 22747)]⟩, ⟨1, [((-1 : F), 36343)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_15 : growAt 9874 =
    ⟨⟨0, [((1 : F), 36342)]⟩, ⟨1, [((-1 : F), 36343)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_16 : growAt 9876 =
    ⟨⟨0, [((1 : F), 23147)]⟩, ⟨0, [((1 : F), 36347)]⟩, ⟨0, [((1 : F), 36348)]⟩⟩ := by
  decide +kernel

theorem mE2_16 : growAt 9877 =
    ⟨⟨0, [((1 : F), 23147)]⟩, ⟨1, [((-1 : F), 36348)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_16 : growAt 9878 =
    ⟨⟨0, [((1 : F), 36347)]⟩, ⟨1, [((-1 : F), 36348)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_17 : growAt 9880 =
    ⟨⟨0, [((1 : F), 23547)]⟩, ⟨0, [((1 : F), 36352)]⟩, ⟨0, [((1 : F), 36353)]⟩⟩ := by
  decide +kernel

theorem mE2_17 : growAt 9881 =
    ⟨⟨0, [((1 : F), 23547)]⟩, ⟨1, [((-1 : F), 36353)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_17 : growAt 9882 =
    ⟨⟨0, [((1 : F), 36352)]⟩, ⟨1, [((-1 : F), 36353)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_18 : growAt 9884 =
    ⟨⟨0, [((1 : F), 23947)]⟩, ⟨0, [((1 : F), 36357)]⟩, ⟨0, [((1 : F), 36358)]⟩⟩ := by
  decide +kernel

theorem mE2_18 : growAt 9885 =
    ⟨⟨0, [((1 : F), 23947)]⟩, ⟨1, [((-1 : F), 36358)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_18 : growAt 9886 =
    ⟨⟨0, [((1 : F), 36357)]⟩, ⟨1, [((-1 : F), 36358)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_19 : growAt 9888 =
    ⟨⟨0, [((1 : F), 24347)]⟩, ⟨0, [((1 : F), 36362)]⟩, ⟨0, [((1 : F), 36363)]⟩⟩ := by
  decide +kernel

theorem mE2_19 : growAt 9889 =
    ⟨⟨0, [((1 : F), 24347)]⟩, ⟨1, [((-1 : F), 36363)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_19 : growAt 9890 =
    ⟨⟨0, [((1 : F), 36362)]⟩, ⟨1, [((-1 : F), 36363)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_20 : growAt 9892 =
    ⟨⟨0, [((1 : F), 24747)]⟩, ⟨0, [((1 : F), 36367)]⟩, ⟨0, [((1 : F), 36368)]⟩⟩ := by
  decide +kernel

theorem mE2_20 : growAt 9893 =
    ⟨⟨0, [((1 : F), 24747)]⟩, ⟨1, [((-1 : F), 36368)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_20 : growAt 9894 =
    ⟨⟨0, [((1 : F), 36367)]⟩, ⟨1, [((-1 : F), 36368)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_21 : growAt 9896 =
    ⟨⟨0, [((1 : F), 25147)]⟩, ⟨0, [((1 : F), 36372)]⟩, ⟨0, [((1 : F), 36373)]⟩⟩ := by
  decide +kernel

theorem mE2_21 : growAt 9897 =
    ⟨⟨0, [((1 : F), 25147)]⟩, ⟨1, [((-1 : F), 36373)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_21 : growAt 9898 =
    ⟨⟨0, [((1 : F), 36372)]⟩, ⟨1, [((-1 : F), 36373)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_22 : growAt 9900 =
    ⟨⟨0, [((1 : F), 25547)]⟩, ⟨0, [((1 : F), 36377)]⟩, ⟨0, [((1 : F), 36378)]⟩⟩ := by
  decide +kernel

theorem mE2_22 : growAt 9901 =
    ⟨⟨0, [((1 : F), 25547)]⟩, ⟨1, [((-1 : F), 36378)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_22 : growAt 9902 =
    ⟨⟨0, [((1 : F), 36377)]⟩, ⟨1, [((-1 : F), 36378)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_23 : growAt 9904 =
    ⟨⟨0, [((1 : F), 25947)]⟩, ⟨0, [((1 : F), 36382)]⟩, ⟨0, [((1 : F), 36383)]⟩⟩ := by
  decide +kernel

theorem mE2_23 : growAt 9905 =
    ⟨⟨0, [((1 : F), 25947)]⟩, ⟨1, [((-1 : F), 36383)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_23 : growAt 9906 =
    ⟨⟨0, [((1 : F), 36382)]⟩, ⟨1, [((-1 : F), 36383)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mE1_24 : growAt 9908 =
    ⟨⟨0, [((1 : F), 26347)]⟩, ⟨0, [((1 : F), 36387)]⟩, ⟨0, [((1 : F), 36388)]⟩⟩ := by
  decide +kernel

theorem mE2_24 : growAt 9909 =
    ⟨⟨0, [((1 : F), 26347)]⟩, ⟨1, [((-1 : F), 36388)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel

theorem mE3_24 : growAt 9910 =
    ⟨⟨0, [((1 : F), 36387)]⟩, ⟨1, [((-1 : F), 36388)]⟩, ⟨0, []⟩⟩ := by
  decide +kernel


theorem mP_0 : growAt 9819 =
    ⟨⟨1, [((-1 : F), 36269)]⟩, ⟨1, [((-1 : F), 36273)]⟩, ⟨0, [((1 : F), 36276)]⟩⟩ := by
  decide +kernel


theorem mP_1 : growAt 9823 =
    ⟨⟨0, [((1 : F), 36276)]⟩, ⟨1, [((-1 : F), 36278)]⟩, ⟨0, [((1 : F), 36281)]⟩⟩ := by
  decide +kernel


theorem mP_2 : growAt 9827 =
    ⟨⟨0, [((1 : F), 36281)]⟩, ⟨1, [((-1 : F), 36283)]⟩, ⟨0, [((1 : F), 36286)]⟩⟩ := by
  decide +kernel


theorem mP_3 : growAt 9831 =
    ⟨⟨0, [((1 : F), 36286)]⟩, ⟨1, [((-1 : F), 36288)]⟩, ⟨0, [((1 : F), 36291)]⟩⟩ := by
  decide +kernel


theorem mP_4 : growAt 9835 =
    ⟨⟨0, [((1 : F), 36291)]⟩, ⟨1, [((-1 : F), 36293)]⟩, ⟨0, [((1 : F), 36296)]⟩⟩ := by
  decide +kernel


theorem mP_5 : growAt 9839 =
    ⟨⟨0, [((1 : F), 36296)]⟩, ⟨1, [((-1 : F), 36298)]⟩, ⟨0, [((1 : F), 36301)]⟩⟩ := by
  decide +kernel


theorem mP_6 : growAt 9843 =
    ⟨⟨0, [((1 : F), 36301)]⟩, ⟨1, [((-1 : F), 36303)]⟩, ⟨0, [((1 : F), 36306)]⟩⟩ := by
  decide +kernel


theorem mP_7 : growAt 9847 =
    ⟨⟨0, [((1 : F), 36306)]⟩, ⟨1, [((-1 : F), 36308)]⟩, ⟨0, [((1 : F), 36311)]⟩⟩ := by
  decide +kernel


theorem mP_8 : growAt 9851 =
    ⟨⟨0, [((1 : F), 36311)]⟩, ⟨1, [((-1 : F), 36313)]⟩, ⟨0, [((1 : F), 36316)]⟩⟩ := by
  decide +kernel


theorem mP_9 : growAt 9855 =
    ⟨⟨0, [((1 : F), 36316)]⟩, ⟨1, [((-1 : F), 36318)]⟩, ⟨0, [((1 : F), 36321)]⟩⟩ := by
  decide +kernel


theorem mP_10 : growAt 9859 =
    ⟨⟨0, [((1 : F), 36321)]⟩, ⟨1, [((-1 : F), 36323)]⟩, ⟨0, [((1 : F), 36326)]⟩⟩ := by
  decide +kernel


theorem mP_11 : growAt 9863 =
    ⟨⟨0, [((1 : F), 36326)]⟩, ⟨1, [((-1 : F), 36328)]⟩, ⟨0, [((1 : F), 36331)]⟩⟩ := by
  decide +kernel


theorem mP_12 : growAt 9867 =
    ⟨⟨0, [((1 : F), 36331)]⟩, ⟨1, [((-1 : F), 36333)]⟩, ⟨0, [((1 : F), 36336)]⟩⟩ := by
  decide +kernel


theorem mP_13 : growAt 9871 =
    ⟨⟨0, [((1 : F), 36336)]⟩, ⟨1, [((-1 : F), 36338)]⟩, ⟨0, [((1 : F), 36341)]⟩⟩ := by
  decide +kernel


theorem mP_14 : growAt 9875 =
    ⟨⟨0, [((1 : F), 36341)]⟩, ⟨1, [((-1 : F), 36343)]⟩, ⟨0, [((1 : F), 36346)]⟩⟩ := by
  decide +kernel


theorem mP_15 : growAt 9879 =
    ⟨⟨0, [((1 : F), 36346)]⟩, ⟨1, [((-1 : F), 36348)]⟩, ⟨0, [((1 : F), 36351)]⟩⟩ := by
  decide +kernel


theorem mP_16 : growAt 9883 =
    ⟨⟨0, [((1 : F), 36351)]⟩, ⟨1, [((-1 : F), 36353)]⟩, ⟨0, [((1 : F), 36356)]⟩⟩ := by
  decide +kernel


theorem mP_17 : growAt 9887 =
    ⟨⟨0, [((1 : F), 36356)]⟩, ⟨1, [((-1 : F), 36358)]⟩, ⟨0, [((1 : F), 36361)]⟩⟩ := by
  decide +kernel


theorem mP_18 : growAt 9891 =
    ⟨⟨0, [((1 : F), 36361)]⟩, ⟨1, [((-1 : F), 36363)]⟩, ⟨0, [((1 : F), 36366)]⟩⟩ := by
  decide +kernel


theorem mP_19 : growAt 9895 =
    ⟨⟨0, [((1 : F), 36366)]⟩, ⟨1, [((-1 : F), 36368)]⟩, ⟨0, [((1 : F), 36371)]⟩⟩ := by
  decide +kernel


theorem mP_20 : growAt 9899 =
    ⟨⟨0, [((1 : F), 36371)]⟩, ⟨1, [((-1 : F), 36373)]⟩, ⟨0, [((1 : F), 36376)]⟩⟩ := by
  decide +kernel


theorem mP_21 : growAt 9903 =
    ⟨⟨0, [((1 : F), 36376)]⟩, ⟨1, [((-1 : F), 36378)]⟩, ⟨0, [((1 : F), 36381)]⟩⟩ := by
  decide +kernel


theorem mP_22 : growAt 9907 =
    ⟨⟨0, [((1 : F), 36381)]⟩, ⟨1, [((-1 : F), 36383)]⟩, ⟨0, [((1 : F), 36386)]⟩⟩ := by
  decide +kernel


theorem mP_23 : growAt 9911 =
    ⟨⟨0, [((1 : F), 36386)]⟩, ⟨1, [((-1 : F), 36388)]⟩, ⟨0, [((1 : F), 36391)]⟩⟩ := by
  decide +kernel


theorem mF : growAt 9912 = ⟨⟨0, [((1 : F), 36391)]⟩, ⟨1, []⟩, ⟨0, []⟩⟩ := by
  decide +kernel


/-- The `is_zero` gadget: `n ≠ 0` makes `z = 1`, so `n = 0 ↔ 1 − z = 1`. -/
theorem isZero_iff {n w z : F} (h1 : n * w = z) (h2 : n * (1 - z) = 0) :
    n = 0 ↔ 1 - z = 1 := by
  constructor
  · intro hn
    rw [hn, zero_mul] at h1
    rw [← h1]
    ring
  · intro hb
    rw [hb, mul_one] at h2
    exact h2
theorem mhout_0 : (wcallAt 37).plugs.getD (25 + 0) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 0) (LC.cst 0)) (negLC (mborrow 0)))
        (smulLC (W : ℤ) (mborrow 1)) := by
  decide +kernel

theorem mhout_1 : (wcallAt 37).plugs.getD (25 + 1) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 1) (LC.cst 0)) (negLC (mborrow 1)))
        (smulLC (W : ℤ) (mborrow 2)) := by
  decide +kernel

theorem mhout_2 : (wcallAt 37).plugs.getD (25 + 2) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 2) (LC.cst 0)) (negLC (mborrow 2)))
        (smulLC (W : ℤ) (mborrow 3)) := by
  decide +kernel

theorem mhout_3 : (wcallAt 37).plugs.getD (25 + 3) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 3) (LC.cst 0)) (negLC (mborrow 3)))
        (smulLC (W : ℤ) (mborrow 4)) := by
  decide +kernel

theorem mhout_4 : (wcallAt 37).plugs.getD (25 + 4) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 4) (LC.cst 0)) (negLC (mborrow 4)))
        (smulLC (W : ℤ) (mborrow 5)) := by
  decide +kernel

theorem mhout_5 : (wcallAt 37).plugs.getD (25 + 5) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 5) (LC.cst 0)) (negLC (mborrow 5)))
        (smulLC (W : ℤ) (mborrow 6)) := by
  decide +kernel

theorem mhout_6 : (wcallAt 37).plugs.getD (25 + 6) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 6) (LC.cst 0)) (negLC (mborrow 6)))
        (smulLC (W : ℤ) (mborrow 7)) := by
  decide +kernel

theorem mhout_7 : (wcallAt 37).plugs.getD (25 + 7) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 7) (LC.cst 0)) (negLC (mborrow 7)))
        (smulLC (W : ℤ) (mborrow 8)) := by
  decide +kernel

theorem mhout_8 : (wcallAt 37).plugs.getD (25 + 8) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 8) (LC.cst 0)) (negLC (mborrow 8)))
        (smulLC (W : ℤ) (mborrow 9)) := by
  decide +kernel

theorem mhout_9 : (wcallAt 37).plugs.getD (25 + 9) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 9) (LC.cst 0)) (negLC (mborrow 9)))
        (smulLC (W : ℤ) (mborrow 10)) := by
  decide +kernel

theorem mhout_10 : (wcallAt 37).plugs.getD (25 + 10) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 10) (LC.cst 0)) (negLC (mborrow 10)))
        (smulLC (W : ℤ) (mborrow 11)) := by
  decide +kernel

theorem mhout_11 : (wcallAt 37).plugs.getD (25 + 11) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 11) (LC.cst 0)) (negLC (mborrow 11)))
        (smulLC (W : ℤ) (mborrow 12)) := by
  decide +kernel

theorem mhout_12 : (wcallAt 37).plugs.getD (25 + 12) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 12) (LC.cst 0)) (negLC (mborrow 12)))
        (smulLC (W : ℤ) (mborrow 13)) := by
  decide +kernel

theorem mhout_13 : (wcallAt 37).plugs.getD (25 + 13) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 13) (LC.cst 0)) (negLC (mborrow 13)))
        (smulLC (W : ℤ) (mborrow 14)) := by
  decide +kernel

theorem mhout_14 : (wcallAt 37).plugs.getD (25 + 14) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 14) (LC.cst 0)) (negLC (mborrow 14)))
        (smulLC (W : ℤ) (mborrow 15)) := by
  decide +kernel

theorem mhout_15 : (wcallAt 37).plugs.getD (25 + 15) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 15) (LC.cst 0)) (negLC (mborrow 15)))
        (smulLC (W : ℤ) (mborrow 16)) := by
  decide +kernel

theorem mhout_16 : (wcallAt 37).plugs.getD (25 + 16) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 16) (LC.cst 0)) (negLC (mborrow 16)))
        (smulLC (W : ℤ) (mborrow 17)) := by
  decide +kernel

theorem mhout_17 : (wcallAt 37).plugs.getD (25 + 17) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 17) (LC.cst 0)) (negLC (mborrow 17)))
        (smulLC (W : ℤ) (mborrow 18)) := by
  decide +kernel

theorem mhout_18 : (wcallAt 37).plugs.getD (25 + 18) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 18) (LC.cst 0)) (negLC (mborrow 18)))
        (smulLC (W : ℤ) (mborrow 19)) := by
  decide +kernel

theorem mhout_19 : (wcallAt 37).plugs.getD (25 + 19) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 19) (LC.cst 0)) (negLC (mborrow 19)))
        (smulLC (W : ℤ) (mborrow 20)) := by
  decide +kernel

theorem mhout_20 : (wcallAt 37).plugs.getD (25 + 20) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 20) (LC.cst 0)) (negLC (mborrow 20)))
        (smulLC (W : ℤ) (mborrow 21)) := by
  decide +kernel

theorem mhout_21 : (wcallAt 37).plugs.getD (25 + 21) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 21) (LC.cst 0)) (negLC (mborrow 21)))
        (smulLC (W : ℤ) (mborrow 22)) := by
  decide +kernel

theorem mhout_22 : (wcallAt 37).plugs.getD (25 + 22) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 22) (LC.cst 0)) (negLC (mborrow 22)))
        (smulLC (W : ℤ) (mborrow 23)) := by
  decide +kernel

theorem mhout_23 : (wcallAt 37).plugs.getD (25 + 23) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 23) (LC.cst 0)) (negLC (mborrow 23)))
        (smulLC (W : ℤ) (mborrow 24)) := by
  decide +kernel

theorem mhout_24 : (wcallAt 37).plugs.getD (25 + 24) (LC.cst 0)
    = addLC (addLC ((wcallAt 40).plugs.getD (25 + 24) (LC.cst 0)) (negLC (mborrow 24)))
        (smulLC (W : ℤ) (mborrow 25)) := by
  decide +kernel

theorem mE1q_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 16747 * σ 36268 = σ 36269 := by
  have hr := growAt_sat (s36_sat h) 9813 (by decide)
  rw [mE1_0] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 16747 * (1 - σ 36269) = 0 := by
  have hr := growAt_sat (s36_sat h) 9814 (by decide)
  rw [mE2_0] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 17147 * σ 36272 = σ 36273 := by
  have hr := growAt_sat (s36_sat h) 9816 (by decide)
  rw [mE1_1] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 17147 * (1 - σ 36273) = 0 := by
  have hr := growAt_sat (s36_sat h) 9817 (by decide)
  rw [mE2_1] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 17547 * σ 36277 = σ 36278 := by
  have hr := growAt_sat (s36_sat h) 9820 (by decide)
  rw [mE1_2] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 17547 * (1 - σ 36278) = 0 := by
  have hr := growAt_sat (s36_sat h) 9821 (by decide)
  rw [mE2_2] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 17947 * σ 36282 = σ 36283 := by
  have hr := growAt_sat (s36_sat h) 9824 (by decide)
  rw [mE1_3] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 17947 * (1 - σ 36283) = 0 := by
  have hr := growAt_sat (s36_sat h) 9825 (by decide)
  rw [mE2_3] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 18347 * σ 36287 = σ 36288 := by
  have hr := growAt_sat (s36_sat h) 9828 (by decide)
  rw [mE1_4] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 18347 * (1 - σ 36288) = 0 := by
  have hr := growAt_sat (s36_sat h) 9829 (by decide)
  rw [mE2_4] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 18747 * σ 36292 = σ 36293 := by
  have hr := growAt_sat (s36_sat h) 9832 (by decide)
  rw [mE1_5] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 18747 * (1 - σ 36293) = 0 := by
  have hr := growAt_sat (s36_sat h) 9833 (by decide)
  rw [mE2_5] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 19147 * σ 36297 = σ 36298 := by
  have hr := growAt_sat (s36_sat h) 9836 (by decide)
  rw [mE1_6] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 19147 * (1 - σ 36298) = 0 := by
  have hr := growAt_sat (s36_sat h) 9837 (by decide)
  rw [mE2_6] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 19547 * σ 36302 = σ 36303 := by
  have hr := growAt_sat (s36_sat h) 9840 (by decide)
  rw [mE1_7] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 19547 * (1 - σ 36303) = 0 := by
  have hr := growAt_sat (s36_sat h) 9841 (by decide)
  rw [mE2_7] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 19947 * σ 36307 = σ 36308 := by
  have hr := growAt_sat (s36_sat h) 9844 (by decide)
  rw [mE1_8] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 19947 * (1 - σ 36308) = 0 := by
  have hr := growAt_sat (s36_sat h) 9845 (by decide)
  rw [mE2_8] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 20347 * σ 36312 = σ 36313 := by
  have hr := growAt_sat (s36_sat h) 9848 (by decide)
  rw [mE1_9] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 20347 * (1 - σ 36313) = 0 := by
  have hr := growAt_sat (s36_sat h) 9849 (by decide)
  rw [mE2_9] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 20747 * σ 36317 = σ 36318 := by
  have hr := growAt_sat (s36_sat h) 9852 (by decide)
  rw [mE1_10] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 20747 * (1 - σ 36318) = 0 := by
  have hr := growAt_sat (s36_sat h) 9853 (by decide)
  rw [mE2_10] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 21147 * σ 36322 = σ 36323 := by
  have hr := growAt_sat (s36_sat h) 9856 (by decide)
  rw [mE1_11] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 21147 * (1 - σ 36323) = 0 := by
  have hr := growAt_sat (s36_sat h) 9857 (by decide)
  rw [mE2_11] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 21547 * σ 36327 = σ 36328 := by
  have hr := growAt_sat (s36_sat h) 9860 (by decide)
  rw [mE1_12] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 21547 * (1 - σ 36328) = 0 := by
  have hr := growAt_sat (s36_sat h) 9861 (by decide)
  rw [mE2_12] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 21947 * σ 36332 = σ 36333 := by
  have hr := growAt_sat (s36_sat h) 9864 (by decide)
  rw [mE1_13] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 21947 * (1 - σ 36333) = 0 := by
  have hr := growAt_sat (s36_sat h) 9865 (by decide)
  rw [mE2_13] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 22347 * σ 36337 = σ 36338 := by
  have hr := growAt_sat (s36_sat h) 9868 (by decide)
  rw [mE1_14] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 22347 * (1 - σ 36338) = 0 := by
  have hr := growAt_sat (s36_sat h) 9869 (by decide)
  rw [mE2_14] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 22747 * σ 36342 = σ 36343 := by
  have hr := growAt_sat (s36_sat h) 9872 (by decide)
  rw [mE1_15] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 22747 * (1 - σ 36343) = 0 := by
  have hr := growAt_sat (s36_sat h) 9873 (by decide)
  rw [mE2_15] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 23147 * σ 36347 = σ 36348 := by
  have hr := growAt_sat (s36_sat h) 9876 (by decide)
  rw [mE1_16] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 23147 * (1 - σ 36348) = 0 := by
  have hr := growAt_sat (s36_sat h) 9877 (by decide)
  rw [mE2_16] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 23547 * σ 36352 = σ 36353 := by
  have hr := growAt_sat (s36_sat h) 9880 (by decide)
  rw [mE1_17] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 23547 * (1 - σ 36353) = 0 := by
  have hr := growAt_sat (s36_sat h) 9881 (by decide)
  rw [mE2_17] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 23947 * σ 36357 = σ 36358 := by
  have hr := growAt_sat (s36_sat h) 9884 (by decide)
  rw [mE1_18] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 23947 * (1 - σ 36358) = 0 := by
  have hr := growAt_sat (s36_sat h) 9885 (by decide)
  rw [mE2_18] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 24347 * σ 36362 = σ 36363 := by
  have hr := growAt_sat (s36_sat h) 9888 (by decide)
  rw [mE1_19] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 24347 * (1 - σ 36363) = 0 := by
  have hr := growAt_sat (s36_sat h) 9889 (by decide)
  rw [mE2_19] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 24747 * σ 36367 = σ 36368 := by
  have hr := growAt_sat (s36_sat h) 9892 (by decide)
  rw [mE1_20] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 24747 * (1 - σ 36368) = 0 := by
  have hr := growAt_sat (s36_sat h) 9893 (by decide)
  rw [mE2_20] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 25147 * σ 36372 = σ 36373 := by
  have hr := growAt_sat (s36_sat h) 9896 (by decide)
  rw [mE1_21] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 25147 * (1 - σ 36373) = 0 := by
  have hr := growAt_sat (s36_sat h) 9897 (by decide)
  rw [mE2_21] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 25547 * σ 36377 = σ 36378 := by
  have hr := growAt_sat (s36_sat h) 9900 (by decide)
  rw [mE1_22] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 25547 * (1 - σ 36378) = 0 := by
  have hr := growAt_sat (s36_sat h) 9901 (by decide)
  rw [mE2_22] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 25947 * σ 36382 = σ 36383 := by
  have hr := growAt_sat (s36_sat h) 9904 (by decide)
  rw [mE1_23] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 25947 * (1 - σ 36383) = 0 := by
  have hr := growAt_sat (s36_sat h) 9905 (by decide)
  rw [mE2_23] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mE1q_24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 26347 * σ 36387 = σ 36388 := by
  have hr := growAt_sat (s36_sat h) 9908 (by decide)
  rw [mE1_24] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

theorem mE2q_24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 26347 * (1 - σ 36388) = 0 := by
  have hr := growAt_sat (s36_sat h) 9909 (by decide)
  rw [mE2_24] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (1 - σ 36269) * (1 - σ 36273) = σ 36276 := by
  have hr := growAt_sat (s36_sat h) 9819 (by decide)
  rw [mP_0] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36276 * (1 - σ 36278) = σ 36281 := by
  have hr := growAt_sat (s36_sat h) 9823 (by decide)
  rw [mP_1] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36281 * (1 - σ 36283) = σ 36286 := by
  have hr := growAt_sat (s36_sat h) 9827 (by decide)
  rw [mP_2] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36286 * (1 - σ 36288) = σ 36291 := by
  have hr := growAt_sat (s36_sat h) 9831 (by decide)
  rw [mP_3] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36291 * (1 - σ 36293) = σ 36296 := by
  have hr := growAt_sat (s36_sat h) 9835 (by decide)
  rw [mP_4] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36296 * (1 - σ 36298) = σ 36301 := by
  have hr := growAt_sat (s36_sat h) 9839 (by decide)
  rw [mP_5] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36301 * (1 - σ 36303) = σ 36306 := by
  have hr := growAt_sat (s36_sat h) 9843 (by decide)
  rw [mP_6] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36306 * (1 - σ 36308) = σ 36311 := by
  have hr := growAt_sat (s36_sat h) 9847 (by decide)
  rw [mP_7] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36311 * (1 - σ 36313) = σ 36316 := by
  have hr := growAt_sat (s36_sat h) 9851 (by decide)
  rw [mP_8] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36316 * (1 - σ 36318) = σ 36321 := by
  have hr := growAt_sat (s36_sat h) 9855 (by decide)
  rw [mP_9] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36321 * (1 - σ 36323) = σ 36326 := by
  have hr := growAt_sat (s36_sat h) 9859 (by decide)
  rw [mP_10] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36326 * (1 - σ 36328) = σ 36331 := by
  have hr := growAt_sat (s36_sat h) 9863 (by decide)
  rw [mP_11] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36331 * (1 - σ 36333) = σ 36336 := by
  have hr := growAt_sat (s36_sat h) 9867 (by decide)
  rw [mP_12] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36336 * (1 - σ 36338) = σ 36341 := by
  have hr := growAt_sat (s36_sat h) 9871 (by decide)
  rw [mP_13] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36341 * (1 - σ 36343) = σ 36346 := by
  have hr := growAt_sat (s36_sat h) 9875 (by decide)
  rw [mP_14] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36346 * (1 - σ 36348) = σ 36351 := by
  have hr := growAt_sat (s36_sat h) 9879 (by decide)
  rw [mP_15] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36351 * (1 - σ 36353) = σ 36356 := by
  have hr := growAt_sat (s36_sat h) 9883 (by decide)
  rw [mP_16] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36356 * (1 - σ 36358) = σ 36361 := by
  have hr := growAt_sat (s36_sat h) 9887 (by decide)
  rw [mP_17] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36361 * (1 - σ 36363) = σ 36366 := by
  have hr := growAt_sat (s36_sat h) 9891 (by decide)
  rw [mP_18] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36366 * (1 - σ 36368) = σ 36371 := by
  have hr := growAt_sat (s36_sat h) 9895 (by decide)
  rw [mP_19] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36371 * (1 - σ 36373) = σ 36376 := by
  have hr := growAt_sat (s36_sat h) 9899 (by decide)
  rw [mP_20] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36376 * (1 - σ 36378) = σ 36381 := by
  have hr := growAt_sat (s36_sat h) 9903 (by decide)
  rw [mP_21] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36381 * (1 - σ 36383) = σ 36386 := by
  have hr := growAt_sat (s36_sat h) 9907 (by decide)
  rw [mP_22] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mPq_23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    σ 36386 * (1 - σ 36388) = σ 36391 := by
  have hr := growAt_sat (s36_sat h) 9911 (by decide)
  rw [mP_23] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval, sub_eq_add_neg] using hr

theorem mFq (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) : σ 36391 = 0 := by
  have hr := growAt_sat (s36_sat h) 9912 (by decide)
  rw [mF] at hr
  simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr

/-- `z` is a bit: `n·w = z` and `n·(1−z) = 0`. -/
theorem zBit {n w z : F} (h1 : n * w = z) (h2 : n * (1 - z) = 0) : z = 0 ∨ z = 1 := by
  rcases mul_eq_zero.mp h2 with hn | hz
  · left
    rw [hn, zero_mul] at h1
    exact h1.symm
  · right
    linear_combination -hz

/-- `b = 1 − z` is a bit when `z` is. -/
theorem bBit_of {b z : F} (h : b = 1 - z) (hz : z = 0 ∨ z = 1) : b = 0 ∨ b = 1 := by
  rcases hz with hz | hz
  · right; rw [h, hz]; ring
  · left; rw [h, hz]; ring

/-- The `z` value of limb `j`. -/
def mzF (j : ℕ) (σ : ℕ → F) : F := σ (mzvar j)
/-- The `w` value of limb `j`. -/
def mwF (j : ℕ) (σ : ℕ → F) : F := σ (mwvar j)
/-- The borrow bit `b_j = 1 − z_j`. -/
def mbF (j : ℕ) (σ : ℕ → F) : F := (ZLC.toF (mbLC j)).eval σ
/-- `borrow_i`. -/
def mborrowF (i : ℕ) (σ : ℕ → F) : F := (ZLC.toF (mborrow i)).eval σ
/-- The `minus_one` output limb `i` (the `require_lt` m plugs). -/
def mOutF (i : ℕ) (σ : ℕ → F) : F :=
  (ZLC.toF ((wcallAt 37).plugs.getD (25 + i) (LC.cst 0))).eval σ
/-- The input limb `i` (the square's m plugs). -/
def mNF (i : ℕ) (σ : ℕ → F) : F :=
  (ZLC.toF ((wcallAt 40).plugs.getD (25 + i) (LC.cst 0))).eval σ

theorem mbF_eq (j : ℕ) (σ : ℕ → F) : mbF j σ = 1 - mzF j σ := by
  simp [mbF, mbLC, mzF, ZLC.toF, Xark.R1cs.LC.eval]
  ring
end Xark.Circuits.Rsa2048
