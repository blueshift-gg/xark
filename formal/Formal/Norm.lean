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

`mergeTerms` is the merge: a variable appears once, at its first occurrence, with the
coefficients summed and zero coefficients dropped. `Xark.Template.normTerms` sorts with
the exporter's variable order first — `varLe`, plugs before witnesses — and then merges,
so its output is exactly what the frontend emits. `eval_norm` says the normalization
preserves the value, which is what lets a `Sat`-based proof reason about the normalized
rows.
-/

namespace Xark.R1cs

section

variable {F : Type*} [CommRing F] {V : Type*} [DecidableEq V] [DecidableEq F]

/-- Each variable once, at its first occurrence, coefficients summed, zeros dropped. -/
def mergeTerms : List (F × V) → List (F × V)
  | [] => []
  | t :: ts =>
    let c := t.1 + ((ts.filter fun u => u.2 == t.2).map Prod.fst).sum
    let rest := mergeTerms (ts.filter fun u => u.2 != t.2)
    if c = 0 then rest else (c, t.2) :: rest
  termination_by l => l.length
  decreasing_by
    simp_wf
    simpa using List.length_filter_le (fun x : { x // x ∈ ts } => (x : F × V).2 != t.2) ts.attach

/-- The `v`-terms' value factors the coefficient sum out of the variable. -/
theorem sum_filter_beq (l : List (F × V)) (v : V) (σ : V → F) :
    ((l.filter fun u => u.2 == v).map fun u => u.1 * σ u.2).sum
      = ((l.filter fun u => u.2 == v).map Prod.fst).sum * σ v := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    rw [List.filter_cons]
    by_cases h : (t.2 == v) = true
    · have ht : t.2 = v := beq_iff_eq.mp h
      simp only [h, if_true, List.map_cons, List.sum_cons]
      rw [ht, ih]; ring
    · have hf : (t.2 == v) = false := by simpa using h
      simp [hf]
      exact ih

/-- A term list's value splits into its `v`-terms and the rest. -/
theorem sum_filter_bne (l : List (F × V)) (v : V) (σ : V → F) :
    ((l.filter fun u => u.2 == v).map fun u => u.1 * σ u.2).sum
      + ((l.filter fun u => u.2 != v).map fun u => u.1 * σ u.2).sum
      = (l.map fun u => u.1 * σ u.2).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    rw [List.filter_cons, List.filter_cons]
    by_cases h : (t.2 == v) = true
    · have hne : (t.2 != v) = false := by rw [bne]; simp [h]
      simp only [h, hne, if_true, if_false, Bool.false_eq_true,
        List.map_cons, List.sum_cons]
      linear_combination ih
    · have hne : (t.2 != v) = true := by rw [bne]; simp [h]
      have hf : (t.2 == v) = false := by simpa using h
      simp only [hf, hne, if_true, if_false, Bool.false_eq_true,
        List.map_cons, List.sum_cons]
      linear_combination ih

/-- **Merging preserves the value.** -/
theorem eval_mergeTerms (l : List (F × V)) (σ : V → F) :
    ((mergeTerms l).map fun t => t.1 * σ t.2).sum
      = (l.map fun t => t.1 * σ t.2).sum := by
  -- Length induction rather than `mergeTerms.induct`: the latter's motive mentions the
  -- compiled `attach` form of the filtered list, which the exported rows do not.
  have aux : ∀ n, ∀ l : List (F × V), l.length ≤ n →
      ((mergeTerms l).map fun t => t.1 * σ t.2).sum
        = (l.map fun t => t.1 * σ t.2).sum := by
    intro n
    induction n with
    | zero =>
      intro l hl
      have hl' : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hl)
      subst hl'
      rw [mergeTerms.eq_def]
    | succ n ih =>
      intro l hl
      cases l with
      | nil => rw [mergeTerms.eq_def]
      | cons t ts =>
        rw [mergeTerms.eq_def]
        dsimp only
        have hlen : (ts.filter fun u => u.2 != t.2).length ≤ n := by
          have h1 := List.length_filter_le (fun u => u.2 != t.2) ts
          simp only [List.length_cons] at hl
          omega
        have hih := ih (ts.filter fun u => u.2 != t.2) hlen
        have hsplit := sum_filter_bne ts t.2 σ
        rw [sum_filter_beq ts t.2 σ] at hsplit
        by_cases h : t.1 + ((ts.filter fun u => u.2 == t.2).map Prod.fst).sum = 0
        · rw [if_pos h, hih]
          simp only [List.map_cons, List.sum_cons]
          linear_combination hsplit - (σ t.2) * h
        · rw [if_neg h, List.map_cons, List.sum_cons, hih]
          simp only [List.map_cons, List.sum_cons]
          linear_combination hsplit
  exact aux l.length l le_rfl

end

end Xark.R1cs

namespace Xark.Template

/-- The exporter's variable order: a call's plugs in index order, then its witnesses. -/
def varLe : TVar → TVar → Bool
  | .plug i, .plug j => i ≤ j
  | .plug _, .wit _ => true
  | .wit _, .plug _ => false
  | .wit i, .wit j => i ≤ j

/-- `varLe` on a term list: compare the terms' variables. -/
def termLe (a b : F × TVar) : Bool := varLe a.2 b.2

/-- The frontend's normalization of a term list: sorted by variable, each variable once
with its coefficients summed, zero coefficients dropped. -/
def normTerms (l : List (F × TVar)) : List (F × TVar) :=
  Xark.R1cs.mergeTerms (l.mergeSort termLe)

/-- The normalized combination: the same constant and the normalized terms. -/
def norm (l : LC) : LC := ⟨l.const, normTerms l.terms⟩

/-- **Normalization preserves the value.** -/
theorem eval_normTerms (l : List (F × TVar)) (σ : TVar → F) :
    ((normTerms l).map fun t => t.1 * σ t.2).sum
      = (l.map fun t => t.1 * σ t.2).sum := by
  rw [normTerms, Xark.R1cs.eval_mergeTerms]
  exact (List.Perm.sum_eq ((List.mergeSort_perm l termLe).map fun t => t.1 * σ t.2))

/-- **The normalized combination has the same value.** -/
theorem eval_norm (l : LC) (σ : TVar → F) : (norm l).eval σ = l.eval σ := by
  simp only [norm, Xark.R1cs.LC.eval, eval_normTerms]

end Xark.Template
