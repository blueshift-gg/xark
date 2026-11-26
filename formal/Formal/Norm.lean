/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Template
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The exporter's normalization of a linear combination

`crates/frontend/src/gadgets.rs::template` renames a recorded call's variables (plugs
`0 … n-1`, then the call's own witnesses) and sorts each combination's terms by that
code; `xtask/src/lean.rs::render` then prints them. A model built by `bind`ing a
template's rows (`Formal/Circuit.lean`'s `LC.bind`) is a raw `flatMap` of the template's
terms, so it keeps the template's order and repeats a variable when two plugged
combinations read it. Comparing such a model with the exported template therefore
needs the same sort-merge applied to every bound row.

`normTerms` is that normalization: insertion-sort the terms with the exporter's
variable order (`Xark.Template.varLe`, plugs before witnesses), fold `addTerm` over
them (a variable appears once, at its first occurrence, with its coefficients summed),
and drop zero coefficients. Both steps are structural, so `decide +kernel` can evaluate
the model — well-founded recursion does not reduce in the kernel. `eval_norm` says the
normalization preserves the value, which is what lets a `Sat`-based proof reason about
the normalized rows.
-/

namespace Xark.R1cs

section

variable {F : Type*} [CommRing F] {V : Type*} [DecidableEq V] [DecidableEq F]

/-- Insert `t` into `l` keeping it sorted by `le`. -/
def insertTerm (le : V → V → Bool) (t : F × V) : List (F × V) → List (F × V)
  | [] => [t]
  | u :: us => if le t.2 u.2 then t :: u :: us else u :: insertTerm le t us

/-- Insertion sort by `le` (stable). -/
def sortTerms (le : V → V → Bool) : List (F × V) → List (F × V)
  | [] => []
  | t :: ts => insertTerm le t (sortTerms le ts)

/-- Add `t`'s coefficient to the first term with its variable, or append it. -/
def addTerm (t : F × V) : List (F × V) → List (F × V)
  | [] => [t]
  | u :: us => if t.2 = u.2 then (t.1 + u.1, u.2) :: us else u :: addTerm t us

/-- The frontend's normalization of a term list: sorted by variable, each variable once
with its coefficients summed, zero coefficients dropped. -/
def normTerms (le : V → V → Bool) (l : List (F × V)) : List (F × V) :=
  ((sortTerms le l).foldl (fun acc t => addTerm t acc) []).filter fun t => t.1 ≠ 0

theorem eval_insertTerm (le : V → V → Bool) (t : F × V) (l : List (F × V)) (σ : V → F) :
    ((insertTerm le t l).map fun t => t.1 * σ t.2).sum
      = ((l.map fun t => t.1 * σ t.2).sum) + t.1 * σ t.2 := by
  induction l with
  | nil => simp [insertTerm]
  | cons u us ih =>
    rw [insertTerm]
    by_cases h : le t.2 u.2 = true
    · simp only [h, if_true, List.map_cons, List.sum_cons]
      ring
    · have hf : le t.2 u.2 = false := by simpa using h
      simp only [hf, Bool.false_eq_true, if_false, List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem eval_sortTerms (le : V → V → Bool) (l : List (F × V)) (σ : V → F) :
    ((sortTerms le l).map fun t => t.1 * σ t.2).sum
      = (l.map fun t => t.1 * σ t.2).sum := by
  induction l with
  | nil => simp [sortTerms]
  | cons t ts ih =>
    rw [sortTerms, eval_insertTerm, ih, List.map_cons, List.sum_cons]
    ring

theorem eval_addTerm (t : F × V) (l : List (F × V)) (σ : V → F) :
    ((addTerm t l).map fun t => t.1 * σ t.2).sum
      = ((l.map fun t => t.1 * σ t.2).sum) + t.1 * σ t.2 := by
  induction l with
  | nil => simp [addTerm]
  | cons u us ih =>
    rw [addTerm]
    by_cases h : t.2 = u.2
    · simp only [if_pos h, List.map_cons, List.sum_cons]
      rw [← h]
      ring
    · simp only [if_neg h, List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem eval_foldl_addTerm (acc : List (F × V)) (l : List (F × V)) (σ : V → F) :
    ((l.foldl (fun acc t => addTerm t acc) acc).map fun t => t.1 * σ t.2).sum
      = ((acc.map fun t => t.1 * σ t.2).sum) + (l.map fun t => t.1 * σ t.2).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [ih, eval_addTerm, List.map_cons, List.sum_cons]
    ring

theorem eval_filter_zero (l : List (F × V)) (σ : V → F) :
    ((l.filter fun t => t.1 ≠ 0).map fun t => t.1 * σ t.2).sum
      = (l.map fun t => t.1 * σ t.2).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.filter_cons]
    by_cases h : t.1 = 0
    · have hd : decide (t.1 ≠ 0) = false := by simp [h]
      simp only [hd, Bool.false_eq_true, if_false, List.map_cons, List.sum_cons]
      rw [ih]
      simp [h]
    · have hd : decide (t.1 ≠ 0) = true := by simp [h]
      simp only [hd, if_true, List.map_cons, List.sum_cons]
      rw [ih]

theorem eval_normTerms (le : V → V → Bool) (l : List (F × V)) (σ : V → F) :
    ((normTerms le l).map fun t => t.1 * σ t.2).sum
      = (l.map fun t => t.1 * σ t.2).sum := by
  simp only [normTerms, eval_filter_zero, eval_foldl_addTerm, eval_sortTerms, List.map_nil,
    List.sum_nil, zero_add]

end

end Xark.R1cs

namespace Xark.Template

/-- The exporter's variable order: a call's plugs in index order, then its witnesses. -/
def varLe : TVar → TVar → Bool
  | .plug i, .plug j => i ≤ j
  | .plug _, .wit _ => true
  | .wit _, .plug _ => false
  | .wit i, .wit j => i ≤ j

/-- The frontend's normalization: sorted by variable, merged, zero coefficients dropped. -/
def normTerms (l : List (F × TVar)) : List (F × TVar) :=
  Xark.R1cs.normTerms varLe l

/-- The normalized combination: the same constant and the normalized terms. -/
def norm (l : LC) : LC := ⟨l.const, normTerms l.terms⟩

/-- **Normalization preserves the value.** -/
theorem eval_normTerms (l : List (F × TVar)) (σ : TVar → F) :
    ((normTerms l).map fun t => t.1 * σ t.2).sum
      = (l.map fun t => t.1 * σ t.2).sum :=
  Xark.R1cs.eval_normTerms varLe l σ

/-- **The normalized combination has the same value.** -/
theorem eval_norm (l : LC) (σ : TVar → F) : (norm l).eval σ = l.eval σ := by
  simp only [norm, Xark.R1cs.LC.eval, eval_normTerms]

end Xark.Template
