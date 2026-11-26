/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.GroupedColumnStep
import Formal.GroupedColumns
import Formal.ToBits

set_option linter.style.header false

/-!
# From a group carry's witness to its integer

`grouped_column_step` witnesses the carry `k` and pins it with `num = 2^164·k`
(row 0), where `num = S + cb - 2^88 + 2^252`; `Formal/GroupedColumnStep.lean`
proves `k < 2^89` and exposes the pin as `pin_eval`. This file closes the
arithmetic between them:

* `carry_of_step`: `2^164 · k` is below `2^253 < r` when `k < 2^89`, so a
  canonical numerator (`num < r`) makes the field identity an equality of
  naturals — `num = 2^164 · k` over the integers, not only mod `r`.
* `carry_of_sat`: the same straight from the step's rows: a satisfying assignment
  whose `numLC` is the cast of a canonical integer has
  `num = 2^164 · (vLC.eval σ)`, i.e. the `CarrySpec` row
  `Formal/GroupedColumns.lean`'s telescope consumes.

The remaining hypothesis is that `numLC.eval σ` *is* the cast of the integer
numerator: the column bound `< 2^251.7` that the limb range checks give. That is
the row bridge, still hand-proved.
-/

namespace Xark.Rsa.GroupedCarry

open Xark.Template Xark.R1cs
open Xark.Templates.GroupedColumnStep (numLC vLC template Spec pin_eval soundness)
open Xark.Rsa.GroupedColumns (Q BI OFF)

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- **The carry is the integer quotient.** If the numerator is a canonical field
element (`num < r`) and the carry's representative is below `2^89`, then
`2^164 * k` is below `2^253 < r` too, so the field identity `num = 2^164 · k`
holds between canonical representatives and is an equality of naturals. -/
theorem carry_of_step (num : ℕ) (k : F) (hnum : num < r) (hk : k.val < 2 ^ 89)
    (h : (num : F) = ((2 ^ 164 : ℕ) : F) * k) : num = 2 ^ 164 * k.val := by
  have hpow : 2 ^ 164 * 2 ^ 89 = 2 ^ 253 := by norm_num
  have hQ : 2 ^ 164 * k.val < r := by
    have h1 : 2 ^ 164 * k.val < 2 ^ 164 * 2 ^ 89 :=
      Nat.mul_lt_mul_of_pos_left hk (by positivity)
    rw [hpow] at h1
    exact lt_trans h1 (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num))
  have hval := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hnum, ZMod.val_mul,
    ZMod.val_natCast_of_lt (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num)),
    Nat.mod_eq_of_lt hQ] at hval
  exact hval

/-- **A `CarrySpec` row.** With no wrap in the numerator (`0 ≤ num < r`), the
step's carry satisfies the integer equation `num = 2^164 · k` the telescope uses. -/
theorem carry_row (num : ℤ) (k : F) (h0 : 0 ≤ num) (hlt : num < (r : ℤ))
    (hcast : (num : F) = ((2 ^ 164 : ℕ) : F) * k) (hk : k.val < 2 ^ 89) :
    num = Q * (k.val : ℤ) := by
  have hnum : num.toNat < r := by
    have h : (num.toNat : ℤ) = num := Int.toNat_of_nonneg h0
    exact_mod_cast (show (num.toNat : ℤ) < (r : ℤ) by omega)
  have hnat : ((num.toNat : ℕ) : F) = (num : F) := by
    have h := congrArg (fun z : ℤ => (z : F)) (Int.toNat_of_nonneg h0)
    simpa only [Int.cast_natCast] using h
  have hcast' : ((num.toNat : ℕ) : F) = ((2 ^ 164 : ℕ) : F) * k := by
    rw [hnat]
    exact hcast
  have h := carry_of_step num.toNat k hnum hk hcast'
  have h2 : (num.toNat : ℤ) = ((2 ^ 164 : ℕ) : ℤ) * (k.val : ℤ) := by
    rw [h]; push_cast; ring
  rw [Int.toNat_of_nonneg h0] at h2
  rwa [show ((2 ^ 164 : ℕ) : ℤ) = Q by norm_num [Q]] at h2

/-- **The step's rows give its `CarrySpec` row.** A satisfying assignment of
`grouped_column_step`, with `numLC` the cast of a canonical integer `num`, has
`num = 2^164 · k` over the integers. -/
theorem carry_of_sat (σ : TVar → F) (h : template.Sat σ) (num : ℤ)
    (h0 : 0 ≤ num) (hlt : num < (r : ℤ)) (hnum : numLC.eval σ = (num : F)) :
    num = Q * ((vLC.eval σ).val : ℤ) := by
  have hout : template.outputs = [vLC] := by decide +kernel
  have hk : (vLC.eval σ).val < 2 ^ 89 := by
    have hspec := soundness σ h
    simpa [Spec, Template.outs, hout] using hspec
  have hcast : (num : F) = ((2 ^ 164 : ℕ) : F) * (vLC.eval σ) := by
    rw [← hnum]
    exact pin_eval σ h
  exact carry_row num (vLC.eval σ) h0 hlt hcast hk

/-- The same row written as `grouped_columns` computes it:
`S + cb - 2^88 + 2^252 = 2^164 · k`, straight from the step's rows. -/
theorem step_row_of_sat (σ : TVar → F) (h : template.Sat σ) (S cb : ℤ)
    (h0 : 0 ≤ S + cb - BI + OFF) (hlt : S + cb - BI + OFF < (r : ℤ))
    (hnum : numLC.eval σ = (((S + cb - BI + OFF : ℤ)) : F)) :
    S + cb - BI + OFF = Q * ((vLC.eval σ).val : ℤ) :=
  carry_of_sat σ h (S + cb - BI + OFF) h0 hlt hnum

end Xark.Rsa.GroupedCarry
