/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.EmBytes

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# `sig < n`

`require_lt::<25, 82>(sig, m₋₁)` takes `m₋₁ = minus_one(n)` as its second limb vector.
s544's glue rows define that vector: per limb `i` the `is_zero` bit `b_i = 1 − z_i`,
and the product rows `borrow_{i+1}·b_{i+1} = borrow_{i+2}` with `borrow_0 = 1`,
`borrow_25 = 0`. The m plugs are `out_i = n_i − borrow_i + W·borrow_{i+1}`, so summing
gives `Σ out_i·W^i = n − 1`; the range check's `Spec` then gives `sig ≤ n − 1`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- The `is_zero` variable for limb `j` (the third row of its s544 block). -/
def zvar (j : ℕ) : ℕ := if j = 0 then 4353 else 4357 + 5 * (j - 1)

/-- `borrow_{i+2}`'s variable (the product row's `c`). -/
def nxt (i : ℕ) : ℕ := 4360 + 5 * i

/-- `1 − z_j`, the `is_zero` bit of limb `j`. -/
def bLC (j : ℕ) : ZLC := ⟨1, [(-1, zvar j)]⟩

/-- The borrow vector: `borrow_0 = 1`, `borrow_1 = b_0`, then the product hints. -/
def borrow : ℕ → ZLC
  | 0 => ⟨1, []⟩
  | 1 => bLC 0
  | (i + 2) => ⟨0, [(1, nxt i)]⟩

def addLC (l m : ZLC) : ZLC := ⟨l.const + m.const, l.terms ++ m.terms⟩
def negLC (l : ZLC) : ZLC := ⟨-l.const, l.terms.map fun t => (-t.1, t.2)⟩
def smulLC (c : ℤ) (l : ZLC) : ZLC := ⟨c * l.const, l.terms.map fun t => (c * t.1, t.2)⟩

/-- The integer rows of s544 (`.glue` keeps them as `ZRow`s). -/
def s544rows : List ZRow := match s544 with | .glue rs => rs | _ => []

def rowAt (i : ℕ) : ZRow := s544rows.getD i ⟨⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩⟩

theorem hout_0 :
    (callAt 545).plugs.getD (25 + 0) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 0) (LC.cst 0)) (negLC (borrow 0)))
          (smulLC W (borrow 1)) := by
  decide +kernel

theorem hout_1 :
    (callAt 545).plugs.getD (25 + 1) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 1) (LC.cst 0)) (negLC (borrow 1)))
          (smulLC W (borrow 2)) := by
  decide +kernel

theorem hout_2 :
    (callAt 545).plugs.getD (25 + 2) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 2) (LC.cst 0)) (negLC (borrow 2)))
          (smulLC W (borrow 3)) := by
  decide +kernel

theorem hout_3 :
    (callAt 545).plugs.getD (25 + 3) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 3) (LC.cst 0)) (negLC (borrow 3)))
          (smulLC W (borrow 4)) := by
  decide +kernel

theorem hout_4 :
    (callAt 545).plugs.getD (25 + 4) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 4) (LC.cst 0)) (negLC (borrow 4)))
          (smulLC W (borrow 5)) := by
  decide +kernel

theorem hout_5 :
    (callAt 545).plugs.getD (25 + 5) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 5) (LC.cst 0)) (negLC (borrow 5)))
          (smulLC W (borrow 6)) := by
  decide +kernel

theorem hout_6 :
    (callAt 545).plugs.getD (25 + 6) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 6) (LC.cst 0)) (negLC (borrow 6)))
          (smulLC W (borrow 7)) := by
  decide +kernel

theorem hout_7 :
    (callAt 545).plugs.getD (25 + 7) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 7) (LC.cst 0)) (negLC (borrow 7)))
          (smulLC W (borrow 8)) := by
  decide +kernel

theorem hout_8 :
    (callAt 545).plugs.getD (25 + 8) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 8) (LC.cst 0)) (negLC (borrow 8)))
          (smulLC W (borrow 9)) := by
  decide +kernel

theorem hout_9 :
    (callAt 545).plugs.getD (25 + 9) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 9) (LC.cst 0)) (negLC (borrow 9)))
          (smulLC W (borrow 10)) := by
  decide +kernel

theorem hout_10 :
    (callAt 545).plugs.getD (25 + 10) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 10) (LC.cst 0)) (negLC (borrow 10)))
          (smulLC W (borrow 11)) := by
  decide +kernel

theorem hout_11 :
    (callAt 545).plugs.getD (25 + 11) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 11) (LC.cst 0)) (negLC (borrow 11)))
          (smulLC W (borrow 12)) := by
  decide +kernel

theorem hout_12 :
    (callAt 545).plugs.getD (25 + 12) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 12) (LC.cst 0)) (negLC (borrow 12)))
          (smulLC W (borrow 13)) := by
  decide +kernel

theorem hout_13 :
    (callAt 545).plugs.getD (25 + 13) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 13) (LC.cst 0)) (negLC (borrow 13)))
          (smulLC W (borrow 14)) := by
  decide +kernel

theorem hout_14 :
    (callAt 545).plugs.getD (25 + 14) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 14) (LC.cst 0)) (negLC (borrow 14)))
          (smulLC W (borrow 15)) := by
  decide +kernel

theorem hout_15 :
    (callAt 545).plugs.getD (25 + 15) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 15) (LC.cst 0)) (negLC (borrow 15)))
          (smulLC W (borrow 16)) := by
  decide +kernel

theorem hout_16 :
    (callAt 545).plugs.getD (25 + 16) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 16) (LC.cst 0)) (negLC (borrow 16)))
          (smulLC W (borrow 17)) := by
  decide +kernel

theorem hout_17 :
    (callAt 545).plugs.getD (25 + 17) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 17) (LC.cst 0)) (negLC (borrow 17)))
          (smulLC W (borrow 18)) := by
  decide +kernel

theorem hout_18 :
    (callAt 545).plugs.getD (25 + 18) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 18) (LC.cst 0)) (negLC (borrow 18)))
          (smulLC W (borrow 19)) := by
  decide +kernel

theorem hout_19 :
    (callAt 545).plugs.getD (25 + 19) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 19) (LC.cst 0)) (negLC (borrow 19)))
          (smulLC W (borrow 20)) := by
  decide +kernel

theorem hout_20 :
    (callAt 545).plugs.getD (25 + 20) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 20) (LC.cst 0)) (negLC (borrow 20)))
          (smulLC W (borrow 21)) := by
  decide +kernel

theorem hout_21 :
    (callAt 545).plugs.getD (25 + 21) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 21) (LC.cst 0)) (negLC (borrow 21)))
          (smulLC W (borrow 22)) := by
  decide +kernel

theorem hout_22 :
    (callAt 545).plugs.getD (25 + 22) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 22) (LC.cst 0)) (negLC (borrow 22)))
          (smulLC W (borrow 23)) := by
  decide +kernel

theorem hout_23 :
    (callAt 545).plugs.getD (25 + 23) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 23) (LC.cst 0)) (negLC (borrow 23)))
          (smulLC W (borrow 24)) := by
  decide +kernel

theorem hout_24 :
    (callAt 545).plugs.getD (25 + 24) (LC.cst 0)
      = addLC (addLC ((callAt 548).plugs.getD (25 + 24) (LC.cst 0)) (negLC (borrow 24)))
          (smulLC W (borrow 25)) := by
  decide +kernel

theorem hprod_0 :
    (rowAt (4 * 0 + 7)).a = borrow 1 ∧
    (rowAt (4 * 0 + 7)).b = bLC 1 ∧
    (rowAt (4 * 0 + 7)).c = borrow 2 := by
  decide +kernel

theorem hprod_1 :
    (rowAt (4 * 1 + 7)).a = borrow 2 ∧
    (rowAt (4 * 1 + 7)).b = bLC 2 ∧
    (rowAt (4 * 1 + 7)).c = borrow 3 := by
  decide +kernel

theorem hprod_2 :
    (rowAt (4 * 2 + 7)).a = borrow 3 ∧
    (rowAt (4 * 2 + 7)).b = bLC 3 ∧
    (rowAt (4 * 2 + 7)).c = borrow 4 := by
  decide +kernel

theorem hprod_3 :
    (rowAt (4 * 3 + 7)).a = borrow 4 ∧
    (rowAt (4 * 3 + 7)).b = bLC 4 ∧
    (rowAt (4 * 3 + 7)).c = borrow 5 := by
  decide +kernel

theorem hprod_4 :
    (rowAt (4 * 4 + 7)).a = borrow 5 ∧
    (rowAt (4 * 4 + 7)).b = bLC 5 ∧
    (rowAt (4 * 4 + 7)).c = borrow 6 := by
  decide +kernel

theorem hprod_5 :
    (rowAt (4 * 5 + 7)).a = borrow 6 ∧
    (rowAt (4 * 5 + 7)).b = bLC 6 ∧
    (rowAt (4 * 5 + 7)).c = borrow 7 := by
  decide +kernel

theorem hprod_6 :
    (rowAt (4 * 6 + 7)).a = borrow 7 ∧
    (rowAt (4 * 6 + 7)).b = bLC 7 ∧
    (rowAt (4 * 6 + 7)).c = borrow 8 := by
  decide +kernel

theorem hprod_7 :
    (rowAt (4 * 7 + 7)).a = borrow 8 ∧
    (rowAt (4 * 7 + 7)).b = bLC 8 ∧
    (rowAt (4 * 7 + 7)).c = borrow 9 := by
  decide +kernel

theorem hprod_8 :
    (rowAt (4 * 8 + 7)).a = borrow 9 ∧
    (rowAt (4 * 8 + 7)).b = bLC 9 ∧
    (rowAt (4 * 8 + 7)).c = borrow 10 := by
  decide +kernel

theorem hprod_9 :
    (rowAt (4 * 9 + 7)).a = borrow 10 ∧
    (rowAt (4 * 9 + 7)).b = bLC 10 ∧
    (rowAt (4 * 9 + 7)).c = borrow 11 := by
  decide +kernel

theorem hprod_10 :
    (rowAt (4 * 10 + 7)).a = borrow 11 ∧
    (rowAt (4 * 10 + 7)).b = bLC 11 ∧
    (rowAt (4 * 10 + 7)).c = borrow 12 := by
  decide +kernel

theorem hprod_11 :
    (rowAt (4 * 11 + 7)).a = borrow 12 ∧
    (rowAt (4 * 11 + 7)).b = bLC 12 ∧
    (rowAt (4 * 11 + 7)).c = borrow 13 := by
  decide +kernel

theorem hprod_12 :
    (rowAt (4 * 12 + 7)).a = borrow 13 ∧
    (rowAt (4 * 12 + 7)).b = bLC 13 ∧
    (rowAt (4 * 12 + 7)).c = borrow 14 := by
  decide +kernel

theorem hprod_13 :
    (rowAt (4 * 13 + 7)).a = borrow 14 ∧
    (rowAt (4 * 13 + 7)).b = bLC 14 ∧
    (rowAt (4 * 13 + 7)).c = borrow 15 := by
  decide +kernel

theorem hprod_14 :
    (rowAt (4 * 14 + 7)).a = borrow 15 ∧
    (rowAt (4 * 14 + 7)).b = bLC 15 ∧
    (rowAt (4 * 14 + 7)).c = borrow 16 := by
  decide +kernel

theorem hprod_15 :
    (rowAt (4 * 15 + 7)).a = borrow 16 ∧
    (rowAt (4 * 15 + 7)).b = bLC 16 ∧
    (rowAt (4 * 15 + 7)).c = borrow 17 := by
  decide +kernel

theorem hprod_16 :
    (rowAt (4 * 16 + 7)).a = borrow 17 ∧
    (rowAt (4 * 16 + 7)).b = bLC 17 ∧
    (rowAt (4 * 16 + 7)).c = borrow 18 := by
  decide +kernel

theorem hprod_17 :
    (rowAt (4 * 17 + 7)).a = borrow 18 ∧
    (rowAt (4 * 17 + 7)).b = bLC 18 ∧
    (rowAt (4 * 17 + 7)).c = borrow 19 := by
  decide +kernel

theorem hprod_18 :
    (rowAt (4 * 18 + 7)).a = borrow 19 ∧
    (rowAt (4 * 18 + 7)).b = bLC 19 ∧
    (rowAt (4 * 18 + 7)).c = borrow 20 := by
  decide +kernel

theorem hprod_19 :
    (rowAt (4 * 19 + 7)).a = borrow 20 ∧
    (rowAt (4 * 19 + 7)).b = bLC 20 ∧
    (rowAt (4 * 19 + 7)).c = borrow 21 := by
  decide +kernel

theorem hprod_20 :
    (rowAt (4 * 20 + 7)).a = borrow 21 ∧
    (rowAt (4 * 20 + 7)).b = bLC 21 ∧
    (rowAt (4 * 20 + 7)).c = borrow 22 := by
  decide +kernel

theorem hprod_21 :
    (rowAt (4 * 21 + 7)).a = borrow 22 ∧
    (rowAt (4 * 21 + 7)).b = bLC 22 ∧
    (rowAt (4 * 21 + 7)).c = borrow 23 := by
  decide +kernel

theorem hprod_22 :
    (rowAt (4 * 22 + 7)).a = borrow 23 ∧
    (rowAt (4 * 22 + 7)).b = bLC 23 ∧
    (rowAt (4 * 22 + 7)).c = borrow 24 := by
  decide +kernel

theorem hprod_23 :
    (rowAt (4 * 23 + 7)).a = borrow 24 ∧
    (rowAt (4 * 23 + 7)).b = bLC 24 ∧
    (rowAt (4 * 23 + 7)).c = borrow 25 := by
  decide +kernel

theorem htop : (rowAt 100).a = borrow 25 := by
  decide +kernel

theorem hNa_0 : (rowAt 1).a = (callAt 548).plugs.getD (25 + 0) (LC.cst 0) := by
  decide +kernel

theorem hNb_0 : (rowAt 1).b = (⟨0, [(1, 4352)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_0 : (rowAt 1).c = (⟨0, [(1, zvar 0)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_0 : (rowAt 2).b = bLC 0 := by
  decide +kernel

theorem hNd_0 : (rowAt 3).a = (⟨0, [(1, 4352)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_0 : (rowAt 3).b = bLC 0 := by
  decide +kernel

theorem hNa_1 : (rowAt 4).a = (callAt 548).plugs.getD (25 + 1) (LC.cst 0) := by
  decide +kernel

theorem hNb_1 : (rowAt 4).b = (⟨0, [(1, 4356)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_1 : (rowAt 4).c = (⟨0, [(1, zvar 1)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_1 : (rowAt 5).b = bLC 1 := by
  decide +kernel

theorem hNd_1 : (rowAt 6).a = (⟨0, [(1, 4356)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_1 : (rowAt 6).b = bLC 1 := by
  decide +kernel

theorem hNa_2 : (rowAt 8).a = (callAt 548).plugs.getD (25 + 2) (LC.cst 0) := by
  decide +kernel

theorem hNb_2 : (rowAt 8).b = (⟨0, [(1, 4361)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_2 : (rowAt 8).c = (⟨0, [(1, zvar 2)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_2 : (rowAt 9).b = bLC 2 := by
  decide +kernel

theorem hNd_2 : (rowAt 10).a = (⟨0, [(1, 4361)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_2 : (rowAt 10).b = bLC 2 := by
  decide +kernel

theorem hNa_3 : (rowAt 12).a = (callAt 548).plugs.getD (25 + 3) (LC.cst 0) := by
  decide +kernel

theorem hNb_3 : (rowAt 12).b = (⟨0, [(1, 4366)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_3 : (rowAt 12).c = (⟨0, [(1, zvar 3)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_3 : (rowAt 13).b = bLC 3 := by
  decide +kernel

theorem hNd_3 : (rowAt 14).a = (⟨0, [(1, 4366)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_3 : (rowAt 14).b = bLC 3 := by
  decide +kernel

theorem hNa_4 : (rowAt 16).a = (callAt 548).plugs.getD (25 + 4) (LC.cst 0) := by
  decide +kernel

theorem hNb_4 : (rowAt 16).b = (⟨0, [(1, 4371)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_4 : (rowAt 16).c = (⟨0, [(1, zvar 4)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_4 : (rowAt 17).b = bLC 4 := by
  decide +kernel

theorem hNd_4 : (rowAt 18).a = (⟨0, [(1, 4371)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_4 : (rowAt 18).b = bLC 4 := by
  decide +kernel

theorem hNa_5 : (rowAt 20).a = (callAt 548).plugs.getD (25 + 5) (LC.cst 0) := by
  decide +kernel

theorem hNb_5 : (rowAt 20).b = (⟨0, [(1, 4376)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_5 : (rowAt 20).c = (⟨0, [(1, zvar 5)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_5 : (rowAt 21).b = bLC 5 := by
  decide +kernel

theorem hNd_5 : (rowAt 22).a = (⟨0, [(1, 4376)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_5 : (rowAt 22).b = bLC 5 := by
  decide +kernel

theorem hNa_6 : (rowAt 24).a = (callAt 548).plugs.getD (25 + 6) (LC.cst 0) := by
  decide +kernel

theorem hNb_6 : (rowAt 24).b = (⟨0, [(1, 4381)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_6 : (rowAt 24).c = (⟨0, [(1, zvar 6)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_6 : (rowAt 25).b = bLC 6 := by
  decide +kernel

theorem hNd_6 : (rowAt 26).a = (⟨0, [(1, 4381)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_6 : (rowAt 26).b = bLC 6 := by
  decide +kernel

theorem hNa_7 : (rowAt 28).a = (callAt 548).plugs.getD (25 + 7) (LC.cst 0) := by
  decide +kernel

theorem hNb_7 : (rowAt 28).b = (⟨0, [(1, 4386)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_7 : (rowAt 28).c = (⟨0, [(1, zvar 7)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_7 : (rowAt 29).b = bLC 7 := by
  decide +kernel

theorem hNd_7 : (rowAt 30).a = (⟨0, [(1, 4386)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_7 : (rowAt 30).b = bLC 7 := by
  decide +kernel

theorem hNa_8 : (rowAt 32).a = (callAt 548).plugs.getD (25 + 8) (LC.cst 0) := by
  decide +kernel

theorem hNb_8 : (rowAt 32).b = (⟨0, [(1, 4391)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_8 : (rowAt 32).c = (⟨0, [(1, zvar 8)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_8 : (rowAt 33).b = bLC 8 := by
  decide +kernel

theorem hNd_8 : (rowAt 34).a = (⟨0, [(1, 4391)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_8 : (rowAt 34).b = bLC 8 := by
  decide +kernel

theorem hNa_9 : (rowAt 36).a = (callAt 548).plugs.getD (25 + 9) (LC.cst 0) := by
  decide +kernel

theorem hNb_9 : (rowAt 36).b = (⟨0, [(1, 4396)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_9 : (rowAt 36).c = (⟨0, [(1, zvar 9)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_9 : (rowAt 37).b = bLC 9 := by
  decide +kernel

theorem hNd_9 : (rowAt 38).a = (⟨0, [(1, 4396)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_9 : (rowAt 38).b = bLC 9 := by
  decide +kernel

theorem hNa_10 : (rowAt 40).a = (callAt 548).plugs.getD (25 + 10) (LC.cst 0) := by
  decide +kernel

theorem hNb_10 : (rowAt 40).b = (⟨0, [(1, 4401)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_10 : (rowAt 40).c = (⟨0, [(1, zvar 10)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_10 : (rowAt 41).b = bLC 10 := by
  decide +kernel

theorem hNd_10 : (rowAt 42).a = (⟨0, [(1, 4401)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_10 : (rowAt 42).b = bLC 10 := by
  decide +kernel

theorem hNa_11 : (rowAt 44).a = (callAt 548).plugs.getD (25 + 11) (LC.cst 0) := by
  decide +kernel

theorem hNb_11 : (rowAt 44).b = (⟨0, [(1, 4406)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_11 : (rowAt 44).c = (⟨0, [(1, zvar 11)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_11 : (rowAt 45).b = bLC 11 := by
  decide +kernel

theorem hNd_11 : (rowAt 46).a = (⟨0, [(1, 4406)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_11 : (rowAt 46).b = bLC 11 := by
  decide +kernel

theorem hNa_12 : (rowAt 48).a = (callAt 548).plugs.getD (25 + 12) (LC.cst 0) := by
  decide +kernel

theorem hNb_12 : (rowAt 48).b = (⟨0, [(1, 4411)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_12 : (rowAt 48).c = (⟨0, [(1, zvar 12)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_12 : (rowAt 49).b = bLC 12 := by
  decide +kernel

theorem hNd_12 : (rowAt 50).a = (⟨0, [(1, 4411)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_12 : (rowAt 50).b = bLC 12 := by
  decide +kernel

theorem hNa_13 : (rowAt 52).a = (callAt 548).plugs.getD (25 + 13) (LC.cst 0) := by
  decide +kernel

theorem hNb_13 : (rowAt 52).b = (⟨0, [(1, 4416)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_13 : (rowAt 52).c = (⟨0, [(1, zvar 13)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_13 : (rowAt 53).b = bLC 13 := by
  decide +kernel

theorem hNd_13 : (rowAt 54).a = (⟨0, [(1, 4416)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_13 : (rowAt 54).b = bLC 13 := by
  decide +kernel

theorem hNa_14 : (rowAt 56).a = (callAt 548).plugs.getD (25 + 14) (LC.cst 0) := by
  decide +kernel

theorem hNb_14 : (rowAt 56).b = (⟨0, [(1, 4421)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_14 : (rowAt 56).c = (⟨0, [(1, zvar 14)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_14 : (rowAt 57).b = bLC 14 := by
  decide +kernel

theorem hNd_14 : (rowAt 58).a = (⟨0, [(1, 4421)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_14 : (rowAt 58).b = bLC 14 := by
  decide +kernel

theorem hNa_15 : (rowAt 60).a = (callAt 548).plugs.getD (25 + 15) (LC.cst 0) := by
  decide +kernel

theorem hNb_15 : (rowAt 60).b = (⟨0, [(1, 4426)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_15 : (rowAt 60).c = (⟨0, [(1, zvar 15)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_15 : (rowAt 61).b = bLC 15 := by
  decide +kernel

theorem hNd_15 : (rowAt 62).a = (⟨0, [(1, 4426)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_15 : (rowAt 62).b = bLC 15 := by
  decide +kernel

theorem hNa_16 : (rowAt 64).a = (callAt 548).plugs.getD (25 + 16) (LC.cst 0) := by
  decide +kernel

theorem hNb_16 : (rowAt 64).b = (⟨0, [(1, 4431)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_16 : (rowAt 64).c = (⟨0, [(1, zvar 16)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_16 : (rowAt 65).b = bLC 16 := by
  decide +kernel

theorem hNd_16 : (rowAt 66).a = (⟨0, [(1, 4431)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_16 : (rowAt 66).b = bLC 16 := by
  decide +kernel

theorem hNa_17 : (rowAt 68).a = (callAt 548).plugs.getD (25 + 17) (LC.cst 0) := by
  decide +kernel

theorem hNb_17 : (rowAt 68).b = (⟨0, [(1, 4436)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_17 : (rowAt 68).c = (⟨0, [(1, zvar 17)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_17 : (rowAt 69).b = bLC 17 := by
  decide +kernel

theorem hNd_17 : (rowAt 70).a = (⟨0, [(1, 4436)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_17 : (rowAt 70).b = bLC 17 := by
  decide +kernel

theorem hNa_18 : (rowAt 72).a = (callAt 548).plugs.getD (25 + 18) (LC.cst 0) := by
  decide +kernel

theorem hNb_18 : (rowAt 72).b = (⟨0, [(1, 4441)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_18 : (rowAt 72).c = (⟨0, [(1, zvar 18)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_18 : (rowAt 73).b = bLC 18 := by
  decide +kernel

theorem hNd_18 : (rowAt 74).a = (⟨0, [(1, 4441)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_18 : (rowAt 74).b = bLC 18 := by
  decide +kernel

theorem hNa_19 : (rowAt 76).a = (callAt 548).plugs.getD (25 + 19) (LC.cst 0) := by
  decide +kernel

theorem hNb_19 : (rowAt 76).b = (⟨0, [(1, 4446)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_19 : (rowAt 76).c = (⟨0, [(1, zvar 19)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_19 : (rowAt 77).b = bLC 19 := by
  decide +kernel

theorem hNd_19 : (rowAt 78).a = (⟨0, [(1, 4446)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_19 : (rowAt 78).b = bLC 19 := by
  decide +kernel

theorem hNa_20 : (rowAt 80).a = (callAt 548).plugs.getD (25 + 20) (LC.cst 0) := by
  decide +kernel

theorem hNb_20 : (rowAt 80).b = (⟨0, [(1, 4451)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_20 : (rowAt 80).c = (⟨0, [(1, zvar 20)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_20 : (rowAt 81).b = bLC 20 := by
  decide +kernel

theorem hNd_20 : (rowAt 82).a = (⟨0, [(1, 4451)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_20 : (rowAt 82).b = bLC 20 := by
  decide +kernel

theorem hNa_21 : (rowAt 84).a = (callAt 548).plugs.getD (25 + 21) (LC.cst 0) := by
  decide +kernel

theorem hNb_21 : (rowAt 84).b = (⟨0, [(1, 4456)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_21 : (rowAt 84).c = (⟨0, [(1, zvar 21)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_21 : (rowAt 85).b = bLC 21 := by
  decide +kernel

theorem hNd_21 : (rowAt 86).a = (⟨0, [(1, 4456)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_21 : (rowAt 86).b = bLC 21 := by
  decide +kernel

theorem hNa_22 : (rowAt 88).a = (callAt 548).plugs.getD (25 + 22) (LC.cst 0) := by
  decide +kernel

theorem hNb_22 : (rowAt 88).b = (⟨0, [(1, 4461)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_22 : (rowAt 88).c = (⟨0, [(1, zvar 22)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_22 : (rowAt 89).b = bLC 22 := by
  decide +kernel

theorem hNd_22 : (rowAt 90).a = (⟨0, [(1, 4461)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_22 : (rowAt 90).b = bLC 22 := by
  decide +kernel

theorem hNa_23 : (rowAt 92).a = (callAt 548).plugs.getD (25 + 23) (LC.cst 0) := by
  decide +kernel

theorem hNb_23 : (rowAt 92).b = (⟨0, [(1, 4466)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_23 : (rowAt 92).c = (⟨0, [(1, zvar 23)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_23 : (rowAt 93).b = bLC 23 := by
  decide +kernel

theorem hNd_23 : (rowAt 94).a = (⟨0, [(1, 4466)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_23 : (rowAt 94).b = bLC 23 := by
  decide +kernel

theorem hNa_24 : (rowAt 96).a = (callAt 548).plugs.getD (25 + 24) (LC.cst 0) := by
  decide +kernel

theorem hNb_24 : (rowAt 96).b = (⟨0, [(1, 4471)]⟩ : ZLC) := by
  decide +kernel

theorem hNc_24 : (rowAt 96).c = (⟨0, [(1, zvar 24)]⟩ : ZLC) := by
  decide +kernel

theorem hNb2_24 : (rowAt 97).b = bLC 24 := by
  decide +kernel

theorem hNd_24 : (rowAt 98).a = (⟨0, [(1, 4471)]⟩ : ZLC) := by
  decide +kernel

theorem hNe_24 : (rowAt 98).b = bLC 24 := by
  decide +kernel

end Xark.Circuits.Rsa2048
