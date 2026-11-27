/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.ConvertWide

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# The converted limbs' bounds

Each `yN j`/`yS j` is below `2^82` (the top limb below `2^80`), and each carry below
`2^118` — the facts the chain's contracts need, straight from the `range_derived`
blocks. Generated alongside `ConvertCols`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
theorem n_limb_bnd0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 16747).val < 2 ^ 82 :=
  gblock_sound 16747 16748 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1) (by decide +kernel))

theorem n_carry_bnd0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 16746).val < 2 ^ 118 :=
  gblock_sound 16746 16911 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 83) (by decide +kernel))

theorem n_limb_bnd1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 17147).val < 2 ^ 82 :=
  gblock_sound 17147 17148 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 202) (by decide +kernel))

theorem n_carry_bnd1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 17146).val < 2 ^ 118 :=
  gblock_sound 17146 17311 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 284) (by decide +kernel))

theorem n_limb_bnd2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 17547).val < 2 ^ 82 :=
  gblock_sound 17547 17548 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 403) (by decide +kernel))

theorem n_carry_bnd2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 17546).val < 2 ^ 118 :=
  gblock_sound 17546 17711 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 485) (by decide +kernel))

theorem n_limb_bnd3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 17947).val < 2 ^ 82 :=
  gblock_sound 17947 17948 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 604) (by decide +kernel))

theorem n_carry_bnd3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 17946).val < 2 ^ 118 :=
  gblock_sound 17946 18111 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 686) (by decide +kernel))

theorem n_limb_bnd4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 18347).val < 2 ^ 82 :=
  gblock_sound 18347 18348 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 805) (by decide +kernel))

theorem n_carry_bnd4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 18346).val < 2 ^ 118 :=
  gblock_sound 18346 18511 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 887) (by decide +kernel))

theorem n_limb_bnd5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 18747).val < 2 ^ 82 :=
  gblock_sound 18747 18748 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1006) (by decide +kernel))

theorem n_carry_bnd5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 18746).val < 2 ^ 118 :=
  gblock_sound 18746 18911 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1088) (by decide +kernel))

theorem n_limb_bnd6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 19147).val < 2 ^ 82 :=
  gblock_sound 19147 19148 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1207) (by decide +kernel))

theorem n_carry_bnd6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 19146).val < 2 ^ 118 :=
  gblock_sound 19146 19311 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1289) (by decide +kernel))

theorem n_limb_bnd7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 19547).val < 2 ^ 82 :=
  gblock_sound 19547 19548 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1408) (by decide +kernel))

theorem n_carry_bnd7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 19546).val < 2 ^ 118 :=
  gblock_sound 19546 19711 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1490) (by decide +kernel))

theorem n_limb_bnd8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 19947).val < 2 ^ 82 :=
  gblock_sound 19947 19948 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1609) (by decide +kernel))

theorem n_carry_bnd8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 19946).val < 2 ^ 118 :=
  gblock_sound 19946 20111 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1691) (by decide +kernel))

theorem n_limb_bnd9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 20347).val < 2 ^ 82 :=
  gblock_sound 20347 20348 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1810) (by decide +kernel))

theorem n_carry_bnd9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 20346).val < 2 ^ 118 :=
  gblock_sound 20346 20511 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 1892) (by decide +kernel))

theorem n_limb_bnd10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 20747).val < 2 ^ 82 :=
  gblock_sound 20747 20748 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2011) (by decide +kernel))

theorem n_carry_bnd10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 20746).val < 2 ^ 118 :=
  gblock_sound 20746 20911 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2093) (by decide +kernel))

theorem n_limb_bnd11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 21147).val < 2 ^ 82 :=
  gblock_sound 21147 21148 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2212) (by decide +kernel))

theorem n_carry_bnd11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 21146).val < 2 ^ 118 :=
  gblock_sound 21146 21311 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2294) (by decide +kernel))

theorem n_limb_bnd12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 21547).val < 2 ^ 82 :=
  gblock_sound 21547 21548 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2413) (by decide +kernel))

theorem n_carry_bnd12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 21546).val < 2 ^ 118 :=
  gblock_sound 21546 21711 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2495) (by decide +kernel))

theorem n_limb_bnd13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 21947).val < 2 ^ 82 :=
  gblock_sound 21947 21948 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2614) (by decide +kernel))

theorem n_carry_bnd13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 21946).val < 2 ^ 118 :=
  gblock_sound 21946 22111 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2696) (by decide +kernel))

theorem n_limb_bnd14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 22347).val < 2 ^ 82 :=
  gblock_sound 22347 22348 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2815) (by decide +kernel))

theorem n_carry_bnd14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 22346).val < 2 ^ 118 :=
  gblock_sound 22346 22511 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 2897) (by decide +kernel))

theorem n_limb_bnd15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 22747).val < 2 ^ 82 :=
  gblock_sound 22747 22748 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3016) (by decide +kernel))

theorem n_carry_bnd15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 22746).val < 2 ^ 118 :=
  gblock_sound 22746 22911 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3098) (by decide +kernel))

theorem n_limb_bnd16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 23147).val < 2 ^ 82 :=
  gblock_sound 23147 23148 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3217) (by decide +kernel))

theorem n_carry_bnd16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 23146).val < 2 ^ 118 :=
  gblock_sound 23146 23311 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3299) (by decide +kernel))

theorem n_limb_bnd17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 23547).val < 2 ^ 82 :=
  gblock_sound 23547 23548 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3418) (by decide +kernel))

theorem n_carry_bnd17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 23546).val < 2 ^ 118 :=
  gblock_sound 23546 23711 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3500) (by decide +kernel))

theorem n_limb_bnd18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 23947).val < 2 ^ 82 :=
  gblock_sound 23947 23948 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3619) (by decide +kernel))

theorem n_carry_bnd18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 23946).val < 2 ^ 118 :=
  gblock_sound 23946 24111 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3701) (by decide +kernel))

theorem n_limb_bnd19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 24347).val < 2 ^ 82 :=
  gblock_sound 24347 24348 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3820) (by decide +kernel))

theorem n_carry_bnd19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 24346).val < 2 ^ 118 :=
  gblock_sound 24346 24511 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 3902) (by decide +kernel))

theorem n_limb_bnd20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 24747).val < 2 ^ 82 :=
  gblock_sound 24747 24748 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4021) (by decide +kernel))

theorem n_carry_bnd20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 24746).val < 2 ^ 118 :=
  gblock_sound 24746 24911 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4103) (by decide +kernel))

theorem n_limb_bnd21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 25147).val < 2 ^ 82 :=
  gblock_sound 25147 25148 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4222) (by decide +kernel))

theorem n_carry_bnd21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 25146).val < 2 ^ 118 :=
  gblock_sound 25146 25311 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4304) (by decide +kernel))

theorem n_limb_bnd22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 25547).val < 2 ^ 82 :=
  gblock_sound 25547 25548 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4423) (by decide +kernel))

theorem n_carry_bnd22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 25546).val < 2 ^ 118 :=
  gblock_sound 25546 25711 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4505) (by decide +kernel))

theorem n_limb_bnd23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 25947).val < 2 ^ 82 :=
  gblock_sound 25947 25948 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4624) (by decide +kernel))

theorem n_carry_bnd23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 25946).val < 2 ^ 118 :=
  gblock_sound 25946 26111 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4706) (by decide +kernel))

theorem n_limb_bnd24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 26347).val < 2 ^ 80 :=
  gblock_sound 26347 26348 80 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4826) (by decide +kernel))

/-- Every converted modulus limb is below `2^82`. -/
theorem n_limb_lt82 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, (σ (nLimb.getD j 0)).val < 2 ^ 82 := by
  intro j hj
  interval_cases j
  · simpa [nLimb] using n_limb_bnd0 σ h
  · simpa [nLimb] using n_limb_bnd1 σ h
  · simpa [nLimb] using n_limb_bnd2 σ h
  · simpa [nLimb] using n_limb_bnd3 σ h
  · simpa [nLimb] using n_limb_bnd4 σ h
  · simpa [nLimb] using n_limb_bnd5 σ h
  · simpa [nLimb] using n_limb_bnd6 σ h
  · simpa [nLimb] using n_limb_bnd7 σ h
  · simpa [nLimb] using n_limb_bnd8 σ h
  · simpa [nLimb] using n_limb_bnd9 σ h
  · simpa [nLimb] using n_limb_bnd10 σ h
  · simpa [nLimb] using n_limb_bnd11 σ h
  · simpa [nLimb] using n_limb_bnd12 σ h
  · simpa [nLimb] using n_limb_bnd13 σ h
  · simpa [nLimb] using n_limb_bnd14 σ h
  · simpa [nLimb] using n_limb_bnd15 σ h
  · simpa [nLimb] using n_limb_bnd16 σ h
  · simpa [nLimb] using n_limb_bnd17 σ h
  · simpa [nLimb] using n_limb_bnd18 σ h
  · simpa [nLimb] using n_limb_bnd19 σ h
  · simpa [nLimb] using n_limb_bnd20 σ h
  · simpa [nLimb] using n_limb_bnd21 σ h
  · simpa [nLimb] using n_limb_bnd22 σ h
  · simpa [nLimb] using n_limb_bnd23 σ h
  · simpa [nLimb] using Nat.lt_of_lt_of_le (n_limb_bnd24 σ h) (by norm_num : 2 ^ 80 ≤ 2 ^ 82)

theorem s_limb_bnd0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 26508).val < 2 ^ 82 :=
  gblock_sound 26508 26509 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4907) (by decide +kernel))

theorem s_carry_bnd0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 26507).val < 2 ^ 118 :=
  gblock_sound 26507 26672 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 4989) (by decide +kernel))

theorem s_limb_bnd1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 26908).val < 2 ^ 82 :=
  gblock_sound 26908 26909 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5108) (by decide +kernel))

theorem s_carry_bnd1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 26907).val < 2 ^ 118 :=
  gblock_sound 26907 27072 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5190) (by decide +kernel))

theorem s_limb_bnd2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 27308).val < 2 ^ 82 :=
  gblock_sound 27308 27309 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5309) (by decide +kernel))

theorem s_carry_bnd2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 27307).val < 2 ^ 118 :=
  gblock_sound 27307 27472 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5391) (by decide +kernel))

theorem s_limb_bnd3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 27708).val < 2 ^ 82 :=
  gblock_sound 27708 27709 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5510) (by decide +kernel))

theorem s_carry_bnd3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 27707).val < 2 ^ 118 :=
  gblock_sound 27707 27872 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5592) (by decide +kernel))

theorem s_limb_bnd4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 28108).val < 2 ^ 82 :=
  gblock_sound 28108 28109 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5711) (by decide +kernel))

theorem s_carry_bnd4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 28107).val < 2 ^ 118 :=
  gblock_sound 28107 28272 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5793) (by decide +kernel))

theorem s_limb_bnd5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 28508).val < 2 ^ 82 :=
  gblock_sound 28508 28509 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5912) (by decide +kernel))

theorem s_carry_bnd5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 28507).val < 2 ^ 118 :=
  gblock_sound 28507 28672 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 5994) (by decide +kernel))

theorem s_limb_bnd6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 28908).val < 2 ^ 82 :=
  gblock_sound 28908 28909 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6113) (by decide +kernel))

theorem s_carry_bnd6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 28907).val < 2 ^ 118 :=
  gblock_sound 28907 29072 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6195) (by decide +kernel))

theorem s_limb_bnd7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 29308).val < 2 ^ 82 :=
  gblock_sound 29308 29309 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6314) (by decide +kernel))

theorem s_carry_bnd7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 29307).val < 2 ^ 118 :=
  gblock_sound 29307 29472 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6396) (by decide +kernel))

theorem s_limb_bnd8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 29708).val < 2 ^ 82 :=
  gblock_sound 29708 29709 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6515) (by decide +kernel))

theorem s_carry_bnd8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 29707).val < 2 ^ 118 :=
  gblock_sound 29707 29872 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6597) (by decide +kernel))

theorem s_limb_bnd9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 30108).val < 2 ^ 82 :=
  gblock_sound 30108 30109 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6716) (by decide +kernel))

theorem s_carry_bnd9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 30107).val < 2 ^ 118 :=
  gblock_sound 30107 30272 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6798) (by decide +kernel))

theorem s_limb_bnd10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 30508).val < 2 ^ 82 :=
  gblock_sound 30508 30509 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6917) (by decide +kernel))

theorem s_carry_bnd10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 30507).val < 2 ^ 118 :=
  gblock_sound 30507 30672 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 6999) (by decide +kernel))

theorem s_limb_bnd11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 30908).val < 2 ^ 82 :=
  gblock_sound 30908 30909 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7118) (by decide +kernel))

theorem s_carry_bnd11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 30907).val < 2 ^ 118 :=
  gblock_sound 30907 31072 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7200) (by decide +kernel))

theorem s_limb_bnd12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 31308).val < 2 ^ 82 :=
  gblock_sound 31308 31309 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7319) (by decide +kernel))

theorem s_carry_bnd12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 31307).val < 2 ^ 118 :=
  gblock_sound 31307 31472 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7401) (by decide +kernel))

theorem s_limb_bnd13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 31708).val < 2 ^ 82 :=
  gblock_sound 31708 31709 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7520) (by decide +kernel))

theorem s_carry_bnd13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 31707).val < 2 ^ 118 :=
  gblock_sound 31707 31872 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7602) (by decide +kernel))

theorem s_limb_bnd14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 32108).val < 2 ^ 82 :=
  gblock_sound 32108 32109 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7721) (by decide +kernel))

theorem s_carry_bnd14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 32107).val < 2 ^ 118 :=
  gblock_sound 32107 32272 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7803) (by decide +kernel))

theorem s_limb_bnd15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 32508).val < 2 ^ 82 :=
  gblock_sound 32508 32509 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 7922) (by decide +kernel))

theorem s_carry_bnd15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 32507).val < 2 ^ 118 :=
  gblock_sound 32507 32672 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8004) (by decide +kernel))

theorem s_limb_bnd16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 32908).val < 2 ^ 82 :=
  gblock_sound 32908 32909 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8123) (by decide +kernel))

theorem s_carry_bnd16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 32907).val < 2 ^ 118 :=
  gblock_sound 32907 33072 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8205) (by decide +kernel))

theorem s_limb_bnd17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 33308).val < 2 ^ 82 :=
  gblock_sound 33308 33309 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8324) (by decide +kernel))

theorem s_carry_bnd17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 33307).val < 2 ^ 118 :=
  gblock_sound 33307 33472 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8406) (by decide +kernel))

theorem s_limb_bnd18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 33708).val < 2 ^ 82 :=
  gblock_sound 33708 33709 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8525) (by decide +kernel))

theorem s_carry_bnd18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 33707).val < 2 ^ 118 :=
  gblock_sound 33707 33872 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8607) (by decide +kernel))

theorem s_limb_bnd19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 34108).val < 2 ^ 82 :=
  gblock_sound 34108 34109 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8726) (by decide +kernel))

theorem s_carry_bnd19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 34107).val < 2 ^ 118 :=
  gblock_sound 34107 34272 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8808) (by decide +kernel))

theorem s_limb_bnd20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 34508).val < 2 ^ 82 :=
  gblock_sound 34508 34509 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 8927) (by decide +kernel))

theorem s_carry_bnd20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 34507).val < 2 ^ 118 :=
  gblock_sound 34507 34672 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 9009) (by decide +kernel))

theorem s_limb_bnd21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 34908).val < 2 ^ 82 :=
  gblock_sound 34908 34909 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 9128) (by decide +kernel))

theorem s_carry_bnd21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 34907).val < 2 ^ 118 :=
  gblock_sound 34907 35072 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 9210) (by decide +kernel))

theorem s_limb_bnd22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 35308).val < 2 ^ 82 :=
  gblock_sound 35308 35309 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 9329) (by decide +kernel))

theorem s_carry_bnd22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 35307).val < 2 ^ 118 :=
  gblock_sound 35307 35472 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 9411) (by decide +kernel))

theorem s_limb_bnd23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 35708).val < 2 ^ 82 :=
  gblock_sound 35708 35709 82 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 9530) (by decide +kernel))

theorem s_carry_bnd23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 35707).val < 2 ^ 118 :=
  gblock_sound 35707 35872 118 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 9612) (by decide +kernel))

theorem s_limb_bnd24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 36108).val < 2 ^ 80 :=
  gblock_sound 36108 36109 80 (by norm_num) (by norm_num) σ
    (gblock_sat (s36_sat h) (k := 9732) (by decide +kernel))

/-- Every converted signature limb is below `2^82`. -/
theorem s_limb_lt82 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ j < 25, (σ (sLimb.getD j 0)).val < 2 ^ 82 := by
  intro j hj
  interval_cases j
  · simpa [sLimb] using s_limb_bnd0 σ h
  · simpa [sLimb] using s_limb_bnd1 σ h
  · simpa [sLimb] using s_limb_bnd2 σ h
  · simpa [sLimb] using s_limb_bnd3 σ h
  · simpa [sLimb] using s_limb_bnd4 σ h
  · simpa [sLimb] using s_limb_bnd5 σ h
  · simpa [sLimb] using s_limb_bnd6 σ h
  · simpa [sLimb] using s_limb_bnd7 σ h
  · simpa [sLimb] using s_limb_bnd8 σ h
  · simpa [sLimb] using s_limb_bnd9 σ h
  · simpa [sLimb] using s_limb_bnd10 σ h
  · simpa [sLimb] using s_limb_bnd11 σ h
  · simpa [sLimb] using s_limb_bnd12 σ h
  · simpa [sLimb] using s_limb_bnd13 σ h
  · simpa [sLimb] using s_limb_bnd14 σ h
  · simpa [sLimb] using s_limb_bnd15 σ h
  · simpa [sLimb] using s_limb_bnd16 σ h
  · simpa [sLimb] using s_limb_bnd17 σ h
  · simpa [sLimb] using s_limb_bnd18 σ h
  · simpa [sLimb] using s_limb_bnd19 σ h
  · simpa [sLimb] using s_limb_bnd20 σ h
  · simpa [sLimb] using s_limb_bnd21 σ h
  · simpa [sLimb] using s_limb_bnd22 σ h
  · simpa [sLimb] using s_limb_bnd23 σ h
  · simpa [sLimb] using Nat.lt_of_lt_of_le (s_limb_bnd24 σ h) (by norm_num : 2 ^ 80 ≤ 2 ^ 82)

end Xark.Circuits.Rsa2048
