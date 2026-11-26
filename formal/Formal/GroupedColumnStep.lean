/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.GroupedColumnStep
import Formal.ToBits
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `xark_rsa::grouped_column_step`, proven over its exported rows

The step's `range_derived::<89>` emits 88 boolean low bits and one derived top
bit `top = k − Σ 2ⁱ bᵢ`, pinned by `top · (top − 2⁸⁸) = 0`. The rows therefore
prove `k < 2⁸⁹` with no input assumption; the affine identity
`k = (S + cb − 2⁸⁸ + 2²⁵²) · 2⁻¹⁶⁴` is the output expression itself.
-/

namespace Xark.Templates.GroupedColumnStep

open Xark.Template Xark.R1cs
open Xark.Templates.Add32 (IsBit isBit_val word_lt sum_map_range isBit_of_mul_self)

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- The output `k`, as the exported linear combination. -/
def vLC : LC := template.outputs.getD 0 ⟨0, []⟩

/-- The 88 low bits of `k`, at weights `2⁰ … 2⁸⁷`. -/
def accLC : LC :=
  ⟨0, (List.range 88).map fun i => (((2 ^ i : ℕ) : F), .wit (2 * i))⟩

def negTerms (l : List (F × TVar)) : List (F × TVar) :=
  l.map fun t => (-t.1, t.2)

/-- `top = k − Σ 2ⁱ bᵢ`. -/
def topA : LC := ⟨vLC.const, vLC.terms ++ negTerms accLC.terms⟩

/-- `top − 2⁸⁸`. -/
def topB : LC := ⟨topA.const - ((2 ^ 88 : ℕ) : F), topA.terms⟩

/-- `bᵢ · bᵢ = bᵢ`. -/
def bitRow (i : ℕ) : Row :=
  ⟨LC.var (.wit (2 * i)), LC.var (.wit (2 * i)), LC.var (.wit (2 * i))⟩

/-- `top · (top − 2⁸⁸) = 0`. -/
def topRow : Row := ⟨topA, topB, ⟨0, []⟩⟩

def modelRows : List Row := (List.range 88).map bitRow ++ [topRow]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows := by
  decide +kernel

/-- The step's contract: the output is below `2⁸⁹`. -/
def Spec (_ins outs : List F) : Prop :=
  (outs.getD 0 0).val < 2 ^ 89

/-- No input assumption: the range check is unconditional. -/
def Assumptions (_ins : List F) : Prop := True

/-- **Soundness.** Every satisfying assignment has its output below `2⁸⁹`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [Template.Sat, rows_eq] at h
  have hbits : ∀ i < 88, IsBit (σ (.wit (2 * i))) := by
    intro i hi
    have hmem : bitRow i ∈ modelRows := by
      simp only [modelRows, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨i, hi, rfl⟩
    have hrow := h (bitRow i) hmem
    exact isBit_of_mul_self (by simpa [Row.Sat, bitRow] using hrow)
  have hrow : topA.eval σ * topB.eval σ = 0 := by
    have := h topRow (by simp [modelRows])
    simpa [Row.Sat, topRow, LC.eval] using this
  have hB : topB.eval σ = topA.eval σ - ((2 ^ 88 : ℕ) : F) := by
    simp only [topB, LC.eval]
    ring
  rw [hB] at hrow
  have htop : topA.eval σ = 0 ∨ topA.eval σ = ((2 ^ 88 : ℕ) : F) := by
    rcases mul_eq_zero.mp hrow with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  let v : ℕ → ℕ := fun i => (σ (.wit (2 * i))).val
  have hv : ∀ i < 88, v i ≤ 1 := fun i hi => isBit_val (hbits i hi)
  have hW := word_lt v 88 hv
  have hcast : ((∑ i ∈ Finset.range 88, 2 ^ i * v i : ℕ) : F) = accLC.eval σ := by
    simp only [accLC, LC.eval, List.map_map, Function.comp_def, sum_map_range]
    push_cast
    simp only [v, ZMod.natCast_val, ZMod.cast_id', id]
    ring
  have hlt : (accLC.eval σ).val < 2 ^ 88 := by
    rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hW (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num)))]
    exact hW
  have hneg :
      (List.map (fun t => t.1 * σ t.2) (negTerms accLC.terms)).sum =
        - (List.map (fun t => t.1 * σ t.2) accLC.terms).sum := by
    induction accLC.terms with
    | nil => simp [negTerms]
    | cons t ts ih => simp [negTerms] at ih ⊢; rw [ih]; ring
  have hvLC : vLC.eval σ = accLC.eval σ + topA.eval σ := by
    simp only [topA, negTerms, LC.eval, List.map_append, List.sum_append]
    simp only [negTerms] at hneg
    rw [hneg]
    simp [accLC]
    ring
  have hvlt : (vLC.eval σ).val < 2 ^ 89 := by
    rw [hvLC, ZMod.val_add]
    have h2 : (accLC.eval σ).val + (topA.eval σ).val < 2 ^ 89 := by
      rcases htop with h0 | h1
      · rw [h0, ZMod.val_zero, add_zero]
        exact lt_trans hlt (by norm_num : 2 ^ 88 < 2 ^ 89)
      · rw [h1, ZMod.val_natCast_of_lt (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num))]
        omega
    rw [Nat.mod_eq_of_lt (lt_trans h2 (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num)))]
    exact h2
  have hout : template.outputs = [vLC] := by
    decide +kernel
  have houts : template.outs σ = [vLC.eval σ] := by
    simp [Template.outs, hout]
  simp [Spec, houts]
  exact hvlt

end Xark.Templates.GroupedColumnStep
