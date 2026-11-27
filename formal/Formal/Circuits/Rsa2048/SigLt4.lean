/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.SigLt3

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# `minus_one(n) = n − 1`

The circuit's s545 is `require_lt(sig, m₋₁)` where s544 builds `m₋₁ = minus_one(n)`.
`s544`'s rows give, per limb, `out_i = n_i − borrow_i + W·borrow_{i+1}` with
`borrow_0 = 1` and `borrow_25 = 0`; this file telescopes the 25 identities into

```
Σ_i out_i·W^i = Σ_i n_i·W^i − borrow_0 + W²⁵·borrow_25 = chainN − 1.
```
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- The recurrence telescopes: the shifted sum cancels the untouched one up to the two
end borrows. -/
theorem telescope (a b c : ℕ → ℤ) (hc0 : c 0 = 1) (hc25 : c 25 = 0)
    (h : ∀ i < 25, a i = b i - c i + W * c (i + 1)) :
    (∑ i ∈ Finset.range 25, a i * W ^ i) = (∑ i ∈ Finset.range 25, b i * W ^ i) - 1 := by
  have hsum : (∑ i ∈ Finset.range 25, a i * W ^ i)
      = (∑ i ∈ Finset.range 25, b i * W ^ i) - (∑ i ∈ Finset.range 25, c i * W ^ i)
        + (∑ i ∈ Finset.range 25, c (i + 1) * W ^ (i + 1)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => by
      rw [h i (Finset.mem_range.mp hi), pow_succ]
      ring
  have hshift : (∑ i ∈ Finset.range 25, c (i + 1) * W ^ (i + 1))
      = (∑ j ∈ Finset.range 26, c j * W ^ j) - c 0 * W ^ 0 := by
    conv_rhs => rw [Finset.sum_range_succ']
    ring
  have hg25 : (∑ j ∈ Finset.range 26, c j * W ^ j)
      = (∑ j ∈ Finset.range 25, c j * W ^ j) + c 25 * W ^ 25 := by
    rw [Finset.sum_range_succ]
  have hc0' : c 0 * W ^ 0 = 1 := by rw [hc0, pow_zero, mul_one]
  have hc25' : c 25 * W ^ 25 = 0 := by rw [hc25, zero_mul]
  rw [hsum, hshift, hg25, hc0', hc25']
  ring

/-- `borrow_0 = 1`, so its value is `1`. -/
theorem borrowF_val_zero (σ : ℕ → F) : ((borrowF 0 σ).val : ℤ) = 1 := by
  have h : borrowF 0 σ = 1 := by
    simp [borrowF, borrow, ZLC.toF, Xark.R1cs.LC.eval]
  rw [h, ZMod.val_one]
  norm_num

/-- `borrow_25 = 0`, so its value is `0`. -/
theorem borrowF_val_25 (σ : ℕ → F) (h : Sat circuit σ) : ((borrowF 25 σ).val : ℤ) = 0 := by
  have ht := T σ h
  rw [show borrowF 25 σ = (ZLC.toF (borrow 25)).eval σ from rfl, ht, ZMod.val_zero,
    Nat.cast_zero]

/-- The value formula for every limb, dispatched by `interval_cases`. -/
theorem outVal (i : ℕ) (hi : i < 25) (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF i σ).val : ℤ) = ((nF i σ).val : ℤ) - ((borrowF i σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF (i + 1) σ).val : ℤ) := by
  interval_cases i
  · exact outVal_0 σ h
  · exact outVal_1 σ h
  · exact outVal_2 σ h
  · exact outVal_3 σ h
  · exact outVal_4 σ h
  · exact outVal_5 σ h
  · exact outVal_6 σ h
  · exact outVal_7 σ h
  · exact outVal_8 σ h
  · exact outVal_9 σ h
  · exact outVal_10 σ h
  · exact outVal_11 σ h
  · exact outVal_12 σ h
  · exact outVal_13 σ h
  · exact outVal_14 σ h
  · exact outVal_15 σ h
  · exact outVal_16 σ h
  · exact outVal_17 σ h
  · exact outVal_18 σ h
  · exact outVal_19 σ h
  · exact outVal_20 σ h
  · exact outVal_21 σ h
  · exact outVal_22 σ h
  · exact outVal_23 σ h
  · exact outVal_24 σ h

/-- **`minus_one`'s m plugs are `chainN − 1`**: the telescoped 25 limb identities. -/
theorem val_minus_one (σ : ℕ → F) (h : Sat circuit σ) :
    val (limb (callAt 545) σ 25) = chainN σ - 1 := by
  have hleft : val (limb (callAt 545) σ 25)
      = ∑ i ∈ Finset.range 25, ((outF i σ).val : ℤ) * W ^ i := rfl
  have hright : chainN σ = ∑ i ∈ Finset.range 25, ((nF i σ).val : ℤ) * W ^ i := rfl
  rw [hleft, hright]
  refine telescope (fun i => ((outF i σ).val : ℤ)) (fun i => ((nF i σ).val : ℤ))
    (fun i => ((borrowF i σ).val : ℤ)) (borrowF_val_zero σ) (borrowF_val_25 σ h) ?_
  intro i hi
  exact outVal i hi σ h


end Xark.Circuits.Rsa2048
