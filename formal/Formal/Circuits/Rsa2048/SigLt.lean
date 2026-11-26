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

theorem s544_sat (σ : ℕ → F) (h : Sat circuit σ) : Sat s544.rows σ := by
  have hs := segSat (σ := σ) h (n := 544) (by decide)
  rwa [show seg 544 = s544 from rfl] at hs

theorem rowSat (σ : ℕ → F) (h : Sat circuit σ) (i : ℕ) (hi : i < s544.rows.length) :
    (s544.rows[i]).Sat σ := s544_sat σ h _ (List.getElem_mem hi)

/-- The modulus limb `i`'s field value (the same LC the chain calls read). -/
def nF (i : ℕ) (σ : ℕ → F) : F :=
  (ZLC.toF ((callAt 548).plugs.getD (25 + i) (LC.cst 0))).eval σ

def wF (i : ℕ) (σ : ℕ → F) : F := σ (if i = 0 then 4352 else 4357 + 5 * (i - 1) - 1)

def zF (i : ℕ) (σ : ℕ → F) : F := σ (if i = 0 then 4353 else 4357 + 5 * (i - 1))

theorem E1_0 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 0 σ * wF 0 σ = zF 0 σ := by
  have hrow := rowSat σ h 1 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[1]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 0) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[1]).b = ZLC.toF (⟨0, [(1, 4352)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[1]).c = ZLC.toF (⟨0, [(1, 4353)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_0 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 0 σ * (1 - zF 0 σ) = 0 := by
  have hrow := rowSat σ h 2 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[2]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 0) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[2]).b = ZLC.toF (bLC 0) from by decide +kernel,
      show (s544.rows[2]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_0 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 0 σ * (1 - zF 0 σ) = 0 := by
  have hrow := rowSat σ h 3 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[3]).a = ZLC.toF (⟨0, [(1, 4352)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[3]).b = ZLC.toF (bLC 0) from by decide +kernel,
      show (s544.rows[3]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_1 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 1 σ * wF 1 σ = zF 1 σ := by
  have hrow := rowSat σ h 4 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[4]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 1) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[4]).b = ZLC.toF (⟨0, [(1, 4356)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[4]).c = ZLC.toF (⟨0, [(1, 4357)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_1 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 1 σ * (1 - zF 1 σ) = 0 := by
  have hrow := rowSat σ h 5 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[5]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 1) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[5]).b = ZLC.toF (bLC 1) from by decide +kernel,
      show (s544.rows[5]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_1 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 1 σ * (1 - zF 1 σ) = 0 := by
  have hrow := rowSat σ h 6 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[6]).a = ZLC.toF (⟨0, [(1, 4356)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[6]).b = ZLC.toF (bLC 1) from by decide +kernel,
      show (s544.rows[6]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_2 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 2 σ * wF 2 σ = zF 2 σ := by
  have hrow := rowSat σ h 8 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[8]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 2) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[8]).b = ZLC.toF (⟨0, [(1, 4361)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[8]).c = ZLC.toF (⟨0, [(1, 4362)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_2 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 2 σ * (1 - zF 2 σ) = 0 := by
  have hrow := rowSat σ h 9 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[9]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 2) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[9]).b = ZLC.toF (bLC 2) from by decide +kernel,
      show (s544.rows[9]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_2 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 2 σ * (1 - zF 2 σ) = 0 := by
  have hrow := rowSat σ h 10 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[10]).a = ZLC.toF (⟨0, [(1, 4361)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[10]).b = ZLC.toF (bLC 2) from by decide +kernel,
      show (s544.rows[10]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_3 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 3 σ * wF 3 σ = zF 3 σ := by
  have hrow := rowSat σ h 12 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[12]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 3) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[12]).b = ZLC.toF (⟨0, [(1, 4366)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[12]).c = ZLC.toF (⟨0, [(1, 4367)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_3 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 3 σ * (1 - zF 3 σ) = 0 := by
  have hrow := rowSat σ h 13 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[13]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 3) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[13]).b = ZLC.toF (bLC 3) from by decide +kernel,
      show (s544.rows[13]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_3 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 3 σ * (1 - zF 3 σ) = 0 := by
  have hrow := rowSat σ h 14 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[14]).a = ZLC.toF (⟨0, [(1, 4366)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[14]).b = ZLC.toF (bLC 3) from by decide +kernel,
      show (s544.rows[14]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_4 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 4 σ * wF 4 σ = zF 4 σ := by
  have hrow := rowSat σ h 16 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[16]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 4) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[16]).b = ZLC.toF (⟨0, [(1, 4371)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[16]).c = ZLC.toF (⟨0, [(1, 4372)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_4 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 4 σ * (1 - zF 4 σ) = 0 := by
  have hrow := rowSat σ h 17 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[17]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 4) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[17]).b = ZLC.toF (bLC 4) from by decide +kernel,
      show (s544.rows[17]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_4 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 4 σ * (1 - zF 4 σ) = 0 := by
  have hrow := rowSat σ h 18 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[18]).a = ZLC.toF (⟨0, [(1, 4371)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[18]).b = ZLC.toF (bLC 4) from by decide +kernel,
      show (s544.rows[18]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_5 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 5 σ * wF 5 σ = zF 5 σ := by
  have hrow := rowSat σ h 20 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[20]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 5) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[20]).b = ZLC.toF (⟨0, [(1, 4376)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[20]).c = ZLC.toF (⟨0, [(1, 4377)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_5 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 5 σ * (1 - zF 5 σ) = 0 := by
  have hrow := rowSat σ h 21 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[21]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 5) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[21]).b = ZLC.toF (bLC 5) from by decide +kernel,
      show (s544.rows[21]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_5 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 5 σ * (1 - zF 5 σ) = 0 := by
  have hrow := rowSat σ h 22 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[22]).a = ZLC.toF (⟨0, [(1, 4376)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[22]).b = ZLC.toF (bLC 5) from by decide +kernel,
      show (s544.rows[22]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_6 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 6 σ * wF 6 σ = zF 6 σ := by
  have hrow := rowSat σ h 24 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[24]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 6) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[24]).b = ZLC.toF (⟨0, [(1, 4381)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[24]).c = ZLC.toF (⟨0, [(1, 4382)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_6 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 6 σ * (1 - zF 6 σ) = 0 := by
  have hrow := rowSat σ h 25 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[25]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 6) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[25]).b = ZLC.toF (bLC 6) from by decide +kernel,
      show (s544.rows[25]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_6 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 6 σ * (1 - zF 6 σ) = 0 := by
  have hrow := rowSat σ h 26 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[26]).a = ZLC.toF (⟨0, [(1, 4381)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[26]).b = ZLC.toF (bLC 6) from by decide +kernel,
      show (s544.rows[26]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_7 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 7 σ * wF 7 σ = zF 7 σ := by
  have hrow := rowSat σ h 28 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[28]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 7) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[28]).b = ZLC.toF (⟨0, [(1, 4386)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[28]).c = ZLC.toF (⟨0, [(1, 4387)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_7 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 7 σ * (1 - zF 7 σ) = 0 := by
  have hrow := rowSat σ h 29 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[29]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 7) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[29]).b = ZLC.toF (bLC 7) from by decide +kernel,
      show (s544.rows[29]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_7 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 7 σ * (1 - zF 7 σ) = 0 := by
  have hrow := rowSat σ h 30 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[30]).a = ZLC.toF (⟨0, [(1, 4386)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[30]).b = ZLC.toF (bLC 7) from by decide +kernel,
      show (s544.rows[30]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_8 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 8 σ * wF 8 σ = zF 8 σ := by
  have hrow := rowSat σ h 32 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[32]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 8) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[32]).b = ZLC.toF (⟨0, [(1, 4391)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[32]).c = ZLC.toF (⟨0, [(1, 4392)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_8 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 8 σ * (1 - zF 8 σ) = 0 := by
  have hrow := rowSat σ h 33 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[33]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 8) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[33]).b = ZLC.toF (bLC 8) from by decide +kernel,
      show (s544.rows[33]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_8 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 8 σ * (1 - zF 8 σ) = 0 := by
  have hrow := rowSat σ h 34 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[34]).a = ZLC.toF (⟨0, [(1, 4391)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[34]).b = ZLC.toF (bLC 8) from by decide +kernel,
      show (s544.rows[34]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_9 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 9 σ * wF 9 σ = zF 9 σ := by
  have hrow := rowSat σ h 36 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[36]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 9) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[36]).b = ZLC.toF (⟨0, [(1, 4396)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[36]).c = ZLC.toF (⟨0, [(1, 4397)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_9 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 9 σ * (1 - zF 9 σ) = 0 := by
  have hrow := rowSat σ h 37 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[37]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 9) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[37]).b = ZLC.toF (bLC 9) from by decide +kernel,
      show (s544.rows[37]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_9 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 9 σ * (1 - zF 9 σ) = 0 := by
  have hrow := rowSat σ h 38 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[38]).a = ZLC.toF (⟨0, [(1, 4396)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[38]).b = ZLC.toF (bLC 9) from by decide +kernel,
      show (s544.rows[38]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_10 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 10 σ * wF 10 σ = zF 10 σ := by
  have hrow := rowSat σ h 40 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[40]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 10) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[40]).b = ZLC.toF (⟨0, [(1, 4401)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[40]).c = ZLC.toF (⟨0, [(1, 4402)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_10 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 10 σ * (1 - zF 10 σ) = 0 := by
  have hrow := rowSat σ h 41 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[41]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 10) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[41]).b = ZLC.toF (bLC 10) from by decide +kernel,
      show (s544.rows[41]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_10 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 10 σ * (1 - zF 10 σ) = 0 := by
  have hrow := rowSat σ h 42 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[42]).a = ZLC.toF (⟨0, [(1, 4401)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[42]).b = ZLC.toF (bLC 10) from by decide +kernel,
      show (s544.rows[42]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_11 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 11 σ * wF 11 σ = zF 11 σ := by
  have hrow := rowSat σ h 44 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[44]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 11) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[44]).b = ZLC.toF (⟨0, [(1, 4406)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[44]).c = ZLC.toF (⟨0, [(1, 4407)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_11 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 11 σ * (1 - zF 11 σ) = 0 := by
  have hrow := rowSat σ h 45 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[45]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 11) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[45]).b = ZLC.toF (bLC 11) from by decide +kernel,
      show (s544.rows[45]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_11 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 11 σ * (1 - zF 11 σ) = 0 := by
  have hrow := rowSat σ h 46 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[46]).a = ZLC.toF (⟨0, [(1, 4406)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[46]).b = ZLC.toF (bLC 11) from by decide +kernel,
      show (s544.rows[46]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_12 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 12 σ * wF 12 σ = zF 12 σ := by
  have hrow := rowSat σ h 48 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[48]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 12) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[48]).b = ZLC.toF (⟨0, [(1, 4411)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[48]).c = ZLC.toF (⟨0, [(1, 4412)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_12 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 12 σ * (1 - zF 12 σ) = 0 := by
  have hrow := rowSat σ h 49 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[49]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 12) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[49]).b = ZLC.toF (bLC 12) from by decide +kernel,
      show (s544.rows[49]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_12 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 12 σ * (1 - zF 12 σ) = 0 := by
  have hrow := rowSat σ h 50 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[50]).a = ZLC.toF (⟨0, [(1, 4411)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[50]).b = ZLC.toF (bLC 12) from by decide +kernel,
      show (s544.rows[50]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_13 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 13 σ * wF 13 σ = zF 13 σ := by
  have hrow := rowSat σ h 52 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[52]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 13) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[52]).b = ZLC.toF (⟨0, [(1, 4416)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[52]).c = ZLC.toF (⟨0, [(1, 4417)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_13 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 13 σ * (1 - zF 13 σ) = 0 := by
  have hrow := rowSat σ h 53 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[53]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 13) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[53]).b = ZLC.toF (bLC 13) from by decide +kernel,
      show (s544.rows[53]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_13 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 13 σ * (1 - zF 13 σ) = 0 := by
  have hrow := rowSat σ h 54 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[54]).a = ZLC.toF (⟨0, [(1, 4416)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[54]).b = ZLC.toF (bLC 13) from by decide +kernel,
      show (s544.rows[54]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_14 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 14 σ * wF 14 σ = zF 14 σ := by
  have hrow := rowSat σ h 56 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[56]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 14) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[56]).b = ZLC.toF (⟨0, [(1, 4421)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[56]).c = ZLC.toF (⟨0, [(1, 4422)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_14 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 14 σ * (1 - zF 14 σ) = 0 := by
  have hrow := rowSat σ h 57 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[57]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 14) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[57]).b = ZLC.toF (bLC 14) from by decide +kernel,
      show (s544.rows[57]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_14 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 14 σ * (1 - zF 14 σ) = 0 := by
  have hrow := rowSat σ h 58 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[58]).a = ZLC.toF (⟨0, [(1, 4421)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[58]).b = ZLC.toF (bLC 14) from by decide +kernel,
      show (s544.rows[58]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_15 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 15 σ * wF 15 σ = zF 15 σ := by
  have hrow := rowSat σ h 60 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[60]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 15) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[60]).b = ZLC.toF (⟨0, [(1, 4426)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[60]).c = ZLC.toF (⟨0, [(1, 4427)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_15 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 15 σ * (1 - zF 15 σ) = 0 := by
  have hrow := rowSat σ h 61 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[61]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 15) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[61]).b = ZLC.toF (bLC 15) from by decide +kernel,
      show (s544.rows[61]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_15 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 15 σ * (1 - zF 15 σ) = 0 := by
  have hrow := rowSat σ h 62 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[62]).a = ZLC.toF (⟨0, [(1, 4426)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[62]).b = ZLC.toF (bLC 15) from by decide +kernel,
      show (s544.rows[62]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_16 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 16 σ * wF 16 σ = zF 16 σ := by
  have hrow := rowSat σ h 64 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[64]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 16) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[64]).b = ZLC.toF (⟨0, [(1, 4431)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[64]).c = ZLC.toF (⟨0, [(1, 4432)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_16 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 16 σ * (1 - zF 16 σ) = 0 := by
  have hrow := rowSat σ h 65 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[65]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 16) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[65]).b = ZLC.toF (bLC 16) from by decide +kernel,
      show (s544.rows[65]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_16 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 16 σ * (1 - zF 16 σ) = 0 := by
  have hrow := rowSat σ h 66 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[66]).a = ZLC.toF (⟨0, [(1, 4431)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[66]).b = ZLC.toF (bLC 16) from by decide +kernel,
      show (s544.rows[66]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_17 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 17 σ * wF 17 σ = zF 17 σ := by
  have hrow := rowSat σ h 68 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[68]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 17) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[68]).b = ZLC.toF (⟨0, [(1, 4436)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[68]).c = ZLC.toF (⟨0, [(1, 4437)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_17 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 17 σ * (1 - zF 17 σ) = 0 := by
  have hrow := rowSat σ h 69 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[69]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 17) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[69]).b = ZLC.toF (bLC 17) from by decide +kernel,
      show (s544.rows[69]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_17 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 17 σ * (1 - zF 17 σ) = 0 := by
  have hrow := rowSat σ h 70 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[70]).a = ZLC.toF (⟨0, [(1, 4436)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[70]).b = ZLC.toF (bLC 17) from by decide +kernel,
      show (s544.rows[70]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_18 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 18 σ * wF 18 σ = zF 18 σ := by
  have hrow := rowSat σ h 72 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[72]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 18) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[72]).b = ZLC.toF (⟨0, [(1, 4441)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[72]).c = ZLC.toF (⟨0, [(1, 4442)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_18 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 18 σ * (1 - zF 18 σ) = 0 := by
  have hrow := rowSat σ h 73 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[73]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 18) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[73]).b = ZLC.toF (bLC 18) from by decide +kernel,
      show (s544.rows[73]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_18 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 18 σ * (1 - zF 18 σ) = 0 := by
  have hrow := rowSat σ h 74 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[74]).a = ZLC.toF (⟨0, [(1, 4441)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[74]).b = ZLC.toF (bLC 18) from by decide +kernel,
      show (s544.rows[74]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_19 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 19 σ * wF 19 σ = zF 19 σ := by
  have hrow := rowSat σ h 76 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[76]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 19) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[76]).b = ZLC.toF (⟨0, [(1, 4446)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[76]).c = ZLC.toF (⟨0, [(1, 4447)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_19 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 19 σ * (1 - zF 19 σ) = 0 := by
  have hrow := rowSat σ h 77 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[77]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 19) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[77]).b = ZLC.toF (bLC 19) from by decide +kernel,
      show (s544.rows[77]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_19 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 19 σ * (1 - zF 19 σ) = 0 := by
  have hrow := rowSat σ h 78 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[78]).a = ZLC.toF (⟨0, [(1, 4446)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[78]).b = ZLC.toF (bLC 19) from by decide +kernel,
      show (s544.rows[78]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_20 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 20 σ * wF 20 σ = zF 20 σ := by
  have hrow := rowSat σ h 80 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[80]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 20) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[80]).b = ZLC.toF (⟨0, [(1, 4451)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[80]).c = ZLC.toF (⟨0, [(1, 4452)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_20 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 20 σ * (1 - zF 20 σ) = 0 := by
  have hrow := rowSat σ h 81 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[81]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 20) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[81]).b = ZLC.toF (bLC 20) from by decide +kernel,
      show (s544.rows[81]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_20 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 20 σ * (1 - zF 20 σ) = 0 := by
  have hrow := rowSat σ h 82 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[82]).a = ZLC.toF (⟨0, [(1, 4451)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[82]).b = ZLC.toF (bLC 20) from by decide +kernel,
      show (s544.rows[82]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_21 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 21 σ * wF 21 σ = zF 21 σ := by
  have hrow := rowSat σ h 84 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[84]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 21) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[84]).b = ZLC.toF (⟨0, [(1, 4456)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[84]).c = ZLC.toF (⟨0, [(1, 4457)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_21 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 21 σ * (1 - zF 21 σ) = 0 := by
  have hrow := rowSat σ h 85 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[85]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 21) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[85]).b = ZLC.toF (bLC 21) from by decide +kernel,
      show (s544.rows[85]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_21 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 21 σ * (1 - zF 21 σ) = 0 := by
  have hrow := rowSat σ h 86 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[86]).a = ZLC.toF (⟨0, [(1, 4456)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[86]).b = ZLC.toF (bLC 21) from by decide +kernel,
      show (s544.rows[86]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_22 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 22 σ * wF 22 σ = zF 22 σ := by
  have hrow := rowSat σ h 88 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[88]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 22) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[88]).b = ZLC.toF (⟨0, [(1, 4461)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[88]).c = ZLC.toF (⟨0, [(1, 4462)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_22 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 22 σ * (1 - zF 22 σ) = 0 := by
  have hrow := rowSat σ h 89 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[89]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 22) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[89]).b = ZLC.toF (bLC 22) from by decide +kernel,
      show (s544.rows[89]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_22 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 22 σ * (1 - zF 22 σ) = 0 := by
  have hrow := rowSat σ h 90 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[90]).a = ZLC.toF (⟨0, [(1, 4461)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[90]).b = ZLC.toF (bLC 22) from by decide +kernel,
      show (s544.rows[90]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_23 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 23 σ * wF 23 σ = zF 23 σ := by
  have hrow := rowSat σ h 92 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[92]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 23) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[92]).b = ZLC.toF (⟨0, [(1, 4466)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[92]).c = ZLC.toF (⟨0, [(1, 4467)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_23 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 23 σ * (1 - zF 23 σ) = 0 := by
  have hrow := rowSat σ h 93 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[93]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 23) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[93]).b = ZLC.toF (bLC 23) from by decide +kernel,
      show (s544.rows[93]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_23 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 23 σ * (1 - zF 23 σ) = 0 := by
  have hrow := rowSat σ h 94 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[94]).a = ZLC.toF (⟨0, [(1, 4466)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[94]).b = ZLC.toF (bLC 23) from by decide +kernel,
      show (s544.rows[94]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E1_24 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 24 σ * wF 24 σ = zF 24 σ := by
  have hrow := rowSat σ h 96 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[96]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 24) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[96]).b = ZLC.toF (⟨0, [(1, 4471)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[96]).c = ZLC.toF (⟨0, [(1, 4472)]⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, wF, zF, zvar] using hrow

theorem E2_24 (σ : ℕ → F) (h : Sat circuit σ) :
    nF 24 σ * (1 - zF 24 σ) = 0 := by
  have hrow := rowSat σ h 97 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[97]).a = ZLC.toF ((callAt 548).plugs.getD (25 + 24) (LC.cst 0)) from by decide +kernel,
      show (s544.rows[97]).b = ZLC.toF (bLC 24) from by decide +kernel,
      show (s544.rows[97]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, nF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem E3_24 (σ : ℕ → F) (h : Sat circuit σ) :
    wF 24 σ * (1 - zF 24 σ) = 0 := by
  have hrow := rowSat σ h 98 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[98]).a = ZLC.toF (⟨0, [(1, 4471)]⟩ : ZLC) from by decide +kernel,
      show (s544.rows[98]).b = ZLC.toF (bLC 24) from by decide +kernel,
      show (s544.rows[98]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, wF, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_0 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 1)).eval σ * (1 - zF 1 σ) = (ZLC.toF (borrow 2)).eval σ := by
  have hrow := rowSat σ h 7 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[7]).a = ZLC.toF (borrow 1) from by decide +kernel,
      show (s544.rows[7]).b = ZLC.toF (bLC 1) from by decide +kernel,
      show (s544.rows[7]).c = ZLC.toF (borrow 2) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_1 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 2)).eval σ * (1 - zF 2 σ) = (ZLC.toF (borrow 3)).eval σ := by
  have hrow := rowSat σ h 11 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[11]).a = ZLC.toF (borrow 2) from by decide +kernel,
      show (s544.rows[11]).b = ZLC.toF (bLC 2) from by decide +kernel,
      show (s544.rows[11]).c = ZLC.toF (borrow 3) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_2 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 3)).eval σ * (1 - zF 3 σ) = (ZLC.toF (borrow 4)).eval σ := by
  have hrow := rowSat σ h 15 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[15]).a = ZLC.toF (borrow 3) from by decide +kernel,
      show (s544.rows[15]).b = ZLC.toF (bLC 3) from by decide +kernel,
      show (s544.rows[15]).c = ZLC.toF (borrow 4) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_3 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 4)).eval σ * (1 - zF 4 σ) = (ZLC.toF (borrow 5)).eval σ := by
  have hrow := rowSat σ h 19 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[19]).a = ZLC.toF (borrow 4) from by decide +kernel,
      show (s544.rows[19]).b = ZLC.toF (bLC 4) from by decide +kernel,
      show (s544.rows[19]).c = ZLC.toF (borrow 5) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_4 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 5)).eval σ * (1 - zF 5 σ) = (ZLC.toF (borrow 6)).eval σ := by
  have hrow := rowSat σ h 23 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[23]).a = ZLC.toF (borrow 5) from by decide +kernel,
      show (s544.rows[23]).b = ZLC.toF (bLC 5) from by decide +kernel,
      show (s544.rows[23]).c = ZLC.toF (borrow 6) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_5 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 6)).eval σ * (1 - zF 6 σ) = (ZLC.toF (borrow 7)).eval σ := by
  have hrow := rowSat σ h 27 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[27]).a = ZLC.toF (borrow 6) from by decide +kernel,
      show (s544.rows[27]).b = ZLC.toF (bLC 6) from by decide +kernel,
      show (s544.rows[27]).c = ZLC.toF (borrow 7) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_6 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 7)).eval σ * (1 - zF 7 σ) = (ZLC.toF (borrow 8)).eval σ := by
  have hrow := rowSat σ h 31 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[31]).a = ZLC.toF (borrow 7) from by decide +kernel,
      show (s544.rows[31]).b = ZLC.toF (bLC 7) from by decide +kernel,
      show (s544.rows[31]).c = ZLC.toF (borrow 8) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_7 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 8)).eval σ * (1 - zF 8 σ) = (ZLC.toF (borrow 9)).eval σ := by
  have hrow := rowSat σ h 35 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[35]).a = ZLC.toF (borrow 8) from by decide +kernel,
      show (s544.rows[35]).b = ZLC.toF (bLC 8) from by decide +kernel,
      show (s544.rows[35]).c = ZLC.toF (borrow 9) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_8 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 9)).eval σ * (1 - zF 9 σ) = (ZLC.toF (borrow 10)).eval σ := by
  have hrow := rowSat σ h 39 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[39]).a = ZLC.toF (borrow 9) from by decide +kernel,
      show (s544.rows[39]).b = ZLC.toF (bLC 9) from by decide +kernel,
      show (s544.rows[39]).c = ZLC.toF (borrow 10) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_9 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 10)).eval σ * (1 - zF 10 σ) = (ZLC.toF (borrow 11)).eval σ := by
  have hrow := rowSat σ h 43 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[43]).a = ZLC.toF (borrow 10) from by decide +kernel,
      show (s544.rows[43]).b = ZLC.toF (bLC 10) from by decide +kernel,
      show (s544.rows[43]).c = ZLC.toF (borrow 11) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_10 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 11)).eval σ * (1 - zF 11 σ) = (ZLC.toF (borrow 12)).eval σ := by
  have hrow := rowSat σ h 47 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[47]).a = ZLC.toF (borrow 11) from by decide +kernel,
      show (s544.rows[47]).b = ZLC.toF (bLC 11) from by decide +kernel,
      show (s544.rows[47]).c = ZLC.toF (borrow 12) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_11 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 12)).eval σ * (1 - zF 12 σ) = (ZLC.toF (borrow 13)).eval σ := by
  have hrow := rowSat σ h 51 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[51]).a = ZLC.toF (borrow 12) from by decide +kernel,
      show (s544.rows[51]).b = ZLC.toF (bLC 12) from by decide +kernel,
      show (s544.rows[51]).c = ZLC.toF (borrow 13) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_12 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 13)).eval σ * (1 - zF 13 σ) = (ZLC.toF (borrow 14)).eval σ := by
  have hrow := rowSat σ h 55 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[55]).a = ZLC.toF (borrow 13) from by decide +kernel,
      show (s544.rows[55]).b = ZLC.toF (bLC 13) from by decide +kernel,
      show (s544.rows[55]).c = ZLC.toF (borrow 14) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_13 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 14)).eval σ * (1 - zF 14 σ) = (ZLC.toF (borrow 15)).eval σ := by
  have hrow := rowSat σ h 59 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[59]).a = ZLC.toF (borrow 14) from by decide +kernel,
      show (s544.rows[59]).b = ZLC.toF (bLC 14) from by decide +kernel,
      show (s544.rows[59]).c = ZLC.toF (borrow 15) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_14 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 15)).eval σ * (1 - zF 15 σ) = (ZLC.toF (borrow 16)).eval σ := by
  have hrow := rowSat σ h 63 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[63]).a = ZLC.toF (borrow 15) from by decide +kernel,
      show (s544.rows[63]).b = ZLC.toF (bLC 15) from by decide +kernel,
      show (s544.rows[63]).c = ZLC.toF (borrow 16) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_15 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 16)).eval σ * (1 - zF 16 σ) = (ZLC.toF (borrow 17)).eval σ := by
  have hrow := rowSat σ h 67 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[67]).a = ZLC.toF (borrow 16) from by decide +kernel,
      show (s544.rows[67]).b = ZLC.toF (bLC 16) from by decide +kernel,
      show (s544.rows[67]).c = ZLC.toF (borrow 17) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_16 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 17)).eval σ * (1 - zF 17 σ) = (ZLC.toF (borrow 18)).eval σ := by
  have hrow := rowSat σ h 71 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[71]).a = ZLC.toF (borrow 17) from by decide +kernel,
      show (s544.rows[71]).b = ZLC.toF (bLC 17) from by decide +kernel,
      show (s544.rows[71]).c = ZLC.toF (borrow 18) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_17 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 18)).eval σ * (1 - zF 18 σ) = (ZLC.toF (borrow 19)).eval σ := by
  have hrow := rowSat σ h 75 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[75]).a = ZLC.toF (borrow 18) from by decide +kernel,
      show (s544.rows[75]).b = ZLC.toF (bLC 18) from by decide +kernel,
      show (s544.rows[75]).c = ZLC.toF (borrow 19) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_18 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 19)).eval σ * (1 - zF 19 σ) = (ZLC.toF (borrow 20)).eval σ := by
  have hrow := rowSat σ h 79 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[79]).a = ZLC.toF (borrow 19) from by decide +kernel,
      show (s544.rows[79]).b = ZLC.toF (bLC 19) from by decide +kernel,
      show (s544.rows[79]).c = ZLC.toF (borrow 20) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_19 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 20)).eval σ * (1 - zF 20 σ) = (ZLC.toF (borrow 21)).eval σ := by
  have hrow := rowSat σ h 83 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[83]).a = ZLC.toF (borrow 20) from by decide +kernel,
      show (s544.rows[83]).b = ZLC.toF (bLC 20) from by decide +kernel,
      show (s544.rows[83]).c = ZLC.toF (borrow 21) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_20 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 21)).eval σ * (1 - zF 21 σ) = (ZLC.toF (borrow 22)).eval σ := by
  have hrow := rowSat σ h 87 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[87]).a = ZLC.toF (borrow 21) from by decide +kernel,
      show (s544.rows[87]).b = ZLC.toF (bLC 21) from by decide +kernel,
      show (s544.rows[87]).c = ZLC.toF (borrow 22) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_21 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 22)).eval σ * (1 - zF 22 σ) = (ZLC.toF (borrow 23)).eval σ := by
  have hrow := rowSat σ h 91 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[91]).a = ZLC.toF (borrow 22) from by decide +kernel,
      show (s544.rows[91]).b = ZLC.toF (bLC 22) from by decide +kernel,
      show (s544.rows[91]).c = ZLC.toF (borrow 23) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_22 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 23)).eval σ * (1 - zF 23 σ) = (ZLC.toF (borrow 24)).eval σ := by
  have hrow := rowSat σ h 95 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[95]).a = ZLC.toF (borrow 23) from by decide +kernel,
      show (s544.rows[95]).b = ZLC.toF (bLC 23) from by decide +kernel,
      show (s544.rows[95]).c = ZLC.toF (borrow 24) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem P_23 (σ : ℕ → F) (h : Sat circuit σ) :
    (ZLC.toF (borrow 24)).eval σ * (1 - zF 24 σ) = (ZLC.toF (borrow 25)).eval σ := by
  have hrow := rowSat σ h 99 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[99]).a = ZLC.toF (borrow 24) from by decide +kernel,
      show (s544.rows[99]).b = ZLC.toF (bLC 24) from by decide +kernel,
      show (s544.rows[99]).c = ZLC.toF (borrow 25) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval, zF, bLC, zvar, sub_eq_add_neg] using hrow

theorem T (σ : ℕ → F) (h : Sat circuit σ) : (ZLC.toF (borrow 25)).eval σ = 0 := by
  have hrow := rowSat σ h 100 (by decide)
  rw [Xark.R1cs.Row.Sat] at hrow
  rw [show (s544.rows[100]).a = ZLC.toF (borrow 25) from by decide +kernel,
      show (s544.rows[100]).b = ZLC.toF (⟨1, []⟩ : ZLC) from by decide +kernel,
      show (s544.rows[100]).c = ZLC.toF (⟨0, []⟩ : ZLC) from by decide +kernel] at hrow
  simpa [ZLC.toF, Xark.R1cs.LC.eval] using hrow

end Xark.Circuits.Rsa2048
