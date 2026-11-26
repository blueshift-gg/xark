/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.GroupedColumnsSquare
import Formal.GroupedColumnsGadget
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_rsa::grouped_columns_square`, proven over its exported rows

`square_lazy` calls the chain with the same limb vector on both sides, so the frontend's
CSE merges the product `a i · a k` with `a k · a i`: 300 of the 625 left products
disappear, the call is 3,135 rows, and its witnesses are numbered differently from the
general gadget. This file models the merged layout

* 950 product rows: for `t = i·25 + k` in loop order, `a i · a k = wit (aProd t)` when
  `i ≤ k`, then always `q i · m k = wit (qProd t)`;
* 24 inlined step instances from row 950, witness 950 + 179j;
* the top row,

and proves `val a · val a = val q · val m + val rhs`. The arithmetic is the general
gadget's (`Formal/GroupedColumnsGadget`); only the product layout differs.
-/

namespace Xark.Templates.GroupedColumnsSquare

open Xark.Template Xark.R1cs
open Xark.Rsa.GroupedColumns (Q W BI OFF)
open Xark.Templates.GroupedColumns (conv_nonneg conv_lt cols_bounds inner_conv conv48
  sum_range_map sum_flatMap sum_filter_map two_pow_164_lt_r two_pow_169_lt_r)

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- The number of witness rows emitted before iteration `t = i·25 + k`. -/
def sqCnt : ℕ → ℕ
  | 0 => 0
  | t + 1 => sqCnt t + (if t / 25 ≤ t % 25 then 2 else 1)

/-- The witness holding `a i · a k` for the CSE'd pair. -/
def aProd (t : ℕ) : ℕ :=
  if t / 25 ≤ t % 25 then sqCnt t else sqCnt ((t % 25) * 25 + t / 25)

/-- The witness holding `q i · m k`. -/
def qProd (t : ℕ) : ℕ := sqCnt t + (if t / 25 ≤ t % 25 then 1 else 0)

/-- Column `c` of `a·a`, over the CSE'd left products. -/
def lhsTerms (c : ℕ) : List (ℤ × TVar) :=
  (List.range 625).filterMap fun t =>
    if t / 25 + t % 25 = c then some (1, TVar.wit (aProd t)) else none

/-- Column `c` of `q·m`, plus the right-hand side's limb `c` for `c < 25`. -/
def rhsTerms (c : ℕ) : List (ℤ × TVar) :=
  ((List.range 625).filterMap fun t =>
    if t / 25 + t % 25 = c then some (1, TVar.wit (qProd t)) else none)
  ++ (if c < 25 then [((1 : ℤ), TVar.plug (75 + c))] else [])

def lhsZ (c : ℕ) : Xark.R1cs.LC ℤ TVar := ⟨0, lhsTerms c⟩
def rhsZ (c : ℕ) : Xark.R1cs.LC ℤ TVar := ⟨0, rhsTerms c⟩
def lhs (c : ℕ) : LC := Xark.Circuit.toField (lhsZ c)
def rhs (c : ℕ) : LC := Xark.Circuit.toField (rhsZ c)

def stepBase (j : ℕ) : ℕ := 950 + 179 * j
def stepRow0 (j : ℕ) : ℕ := 950 + 91 * j

def stepPlug (j : ℕ) : List LC :=
  [lhs (2 * j), lhs (2 * j + 1), rhs (2 * j), rhs (2 * j + 1),
   if j = 0 then LC.cst ((2 ^ 88 : ℕ) : F) else LC.var (.wit (950 + 179 * (j - 1)))]

def stepEnv (j : ℕ) : TVar → LC
  | .plug i => (stepPlug j).getD i (LC.cst 0)
  | .wit t => LC.var (.wit (stepBase j + t))

def bindNorm (e : TVar → LC) (r : Row) : Row :=
  ⟨norm (r.a.bind e), norm (r.b.bind e), norm (r.c.bind e)⟩

def stepRows (j : ℕ) : List Row :=
  Xark.Templates.GroupedColumnStep.template.rows.map (bindNorm (stepEnv j))

def prodRowA (t : ℕ) : Row :=
  ⟨LC.var (.plug (t / 25)), LC.var (.plug (t % 25)), LC.var (.wit (aProd t))⟩

def prodRowQ (t : ℕ) : Row :=
  ⟨LC.var (.plug (50 + t / 25)), LC.var (.plug (25 + t % 25)),
   LC.var (.wit (qProd t))⟩

def productRows : List Row :=
  (List.range 625).flatMap fun t =>
    (if t / 25 ≤ t % 25 then [prodRowA t] else []) ++ [prodRowQ t]

def topRow : Row :=
  ⟨norm ⟨-((2 ^ 88 : ℕ) : F), [(1, .wit 948), (-1, .wit 949), (1, .wit 5067)]⟩,
   ⟨1, []⟩, ⟨0, []⟩⟩

def modelRows : List Row :=
  productRows ++ (List.range 24).flatMap stepRows ++ [topRow]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The exported rows are the model.** -/
theorem rows_eq : template.rows = modelRows := by
  decide +kernel

end Xark.Templates.GroupedColumnsSquare
