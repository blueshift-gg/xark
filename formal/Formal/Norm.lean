/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Rewrites
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The frontend's normalization of a linear combination

`crates/frontend/src/gadgets.rs` records a gadget's rows after the frontend has
normalized each linear combination: a variable appears once, at its first occurrence,
with its coefficients summed, and zero coefficients are dropped. `Formal/Circuit.lean`'s
`LC.bind` is a raw `flatMap`, so a model built by `bind`ing a template's rows keeps the
terms in the template's order and repeats a variable when two plugged combinations read
it. Comparing such a model with the exported template therefore needs this
normalization applied to every bound row.

`normTerms` is it: the head term's variable is collected out of the tail, the
coefficients are summed, the term is dropped when the sum is zero, and the recursion
continues on the remaining terms. `eval_norm` says it preserves the value, which is what
lets a `Sat`-based proof reason about the normalized rows.
-/

namespace Xark.R1cs

variable {F : Type*} [CommRing F] {V : Type*} [DecidableEq V] [DecidableEq F]

/-- The frontend's normalization of a term list: each variable at its first occurrence,
its coefficients summed, zero coefficients dropped. -/
def normTerms : List (F × V) → List (F × V)
  | [] => []
  | t :: ts =>
    let c := t.1 + ((ts.filter fun u => u.2 == t.2).map Prod.fst).sum
    let rest := normTerms (ts.filter fun u => u.2 != t.2)
    if c = 0 then rest else (c, t.2) :: rest
  termination_by l => l.length
  decreasing_by
    simp_wf
    simpa using List.length_filter_le (fun x : { x // x ∈ ts } => (x : F × V).2 != t.2) ts.attach

/-- The combination with its terms normalized. -/
def norm (l : Xark.R1cs.LC F V) : Xark.R1cs.LC F V := ⟨l.const, normTerms l.terms⟩

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

/-- **Normalization preserves the value.** -/
theorem eval_normTerms (l : List (F × V)) (σ : V → F) :
    ((normTerms l).map fun t => t.1 * σ t.2).sum
      = (l.map fun t => t.1 * σ t.2).sum := by
  -- Length induction rather than `normTerms.induct`: the latter's motive mentions the
  -- compiled `attach` form of the filtered list, which the exported rows do not.
  have aux : ∀ n, ∀ l : List (F × V), l.length ≤ n →
      ((normTerms l).map fun t => t.1 * σ t.2).sum
        = (l.map fun t => t.1 * σ t.2).sum := by
    intro n
    induction n with
    | zero =>
      intro l hl
      have hl' : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hl)
      subst hl'
      rw [normTerms.eq_def]
    | succ n ih =>
      intro l hl
      cases l with
      | nil => rw [normTerms.eq_def]
      | cons t ts =>
        rw [normTerms.eq_def]
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

/-- **The normalized combination has the same value.** -/
theorem eval_norm (l : Xark.R1cs.LC F V) (σ : V → F) :
    (norm l).eval σ = l.eval σ := by
  simp only [norm, Xark.R1cs.LC.eval, eval_normTerms]

end Xark.R1cs
