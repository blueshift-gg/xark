/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The integer behind a linear combination

A circuit's linear combinations hold integer coefficients (`ZLC`); the field value
`(l.toF).eval σ` is the shadow — the integer `l`'s coefficients multiply out against the
variables' canonical representatives — read in `F` (`shadow_toF`, no bound needed).

`shadow_eq_of_eval` is the direction soundness needs: when that field value is the cast of
an integer `z` and both the shadow and `z` lie in `[0, r)`, the shadow *is* `z`. That is
what turns a call's plugs (`Σ product variables`, the columns) into integers without
trusting that no wrap happened: a wrapped sum would leave `[0, r)` and the hypothesis
would fail.

The chain's assembly applies this to `GroupedColumnStep.numLC` through `Call.plugs`
(`shadow σ plugLC` is the column sum) and to each product row (`val_of_mul`).
-/

namespace Xark.Circuit

open Xark.R1cs Xark.Template

/-- A list of integers casts termwise. -/
theorem cast_list_sum (l : List ℤ) : ((l.sum : ℤ) : F) = (l.map fun z : ℤ => (z : F)).sum := by
  induction l with
  | nil => simp
  | cons z zs ih => rw [List.sum_cons, List.map_cons, List.sum_cons, Int.cast_add, ih]

/-- Two canonical representatives below `r` that agree in `F` are equal. -/
theorem int_cast_inj {a b : ℤ} (h0 : 0 ≤ a) (ha : a < (r : ℤ)) (hb0 : 0 ≤ b)
    (hb : b < (r : ℤ)) (h : (a : F) = (b : F)) : a = b := by
  have ha' : (a.toNat : ℕ) < r := by
    have h1 : a.toNat = a := Int.toNat_of_nonneg h0
    omega
  have hb' : (b.toNat : ℕ) < r := by
    have h1 : b.toNat = b := Int.toNat_of_nonneg hb0
    omega
  have ha2 : ((a.toNat : ℕ) : F) = (a : F) := by
    rw [show ((a.toNat : ℕ) : F) = (((a.toNat : ℕ) : ℤ) : F) from (Int.cast_natCast _).symm,
      Int.toNat_of_nonneg h0]
  have hb2 : ((b.toNat : ℕ) : F) = (b : F) := by
    rw [show ((b.toNat : ℕ) : F) = (((b.toNat : ℕ) : ℤ) : F) from (Int.cast_natCast _).symm,
      Int.toNat_of_nonneg hb0]
  have h' : ((a.toNat : ℕ) : F) = ((b.toNat : ℕ) : F) := by rw [ha2, hb2]; exact h
  have := congrArg ZMod.val h'
  rw [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this
  omega

variable {V : Type*}

/-- An integer-coefficient combination read in the field. -/
def toField (l : Xark.R1cs.LC ℤ V) : Xark.R1cs.LC F V :=
  ⟨(l.const : F), l.terms.map fun t => ((t.1 : F), t.2)⟩

/-- The integer a `ZLC` denotes under `σ`: its constant plus each integer coefficient times
the variable's canonical representative. -/
def shadow (σ : V → F) (l : Xark.R1cs.LC ℤ V) : ℤ :=
  l.const + (l.terms.map fun t => t.1 * ((σ t.2).val : ℤ)).sum

/-- **The field value is the shadow.** `toF l`'s value is the shadow read in `F`; the
integer coefficients and the variables' representatives multiply out exactly. -/
theorem shadow_toF (σ : V → F) (l : Xark.R1cs.LC ℤ V) :
    (toField l).eval σ = ((shadow σ l : ℤ) : F) := by
  obtain ⟨c, ts⟩ := l
  simp only [toField, shadow, Xark.R1cs.LC.eval]
  rw [Int.cast_add, Int.cast_list_sum]
  congr 1
  rw [List.map_map]
  have hfun : ((fun t : F × V => t.1 * σ t.2) ∘ (fun t : ℤ × V => ((t.1 : F), t.2)))
      = ((fun z : ℤ => (z : F)) ∘ (fun t : ℤ × V => t.1 * ((σ t.2).val : ℤ))) := by
    funext t
    simp only [Function.comp_apply]
    show (t.1 : F) * σ t.2 = ((t.1 * ((σ t.2).val : ℤ) : ℤ) : F)
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hfun, ← List.map_map]

/-- **No wrap.** If a combination's field value is the cast of an integer `z`, and both the
shadow and `z` are below `r`, then the shadow is `z`: the field identification cannot hide
a difference of `r`. -/
theorem shadow_eq_of_eval {σ : V → F} {l : Xark.R1cs.LC ℤ V} {z : ℤ}
    (h : (toField l).eval σ = (z : F)) (h0 : 0 ≤ shadow σ l) (hlt : shadow σ l < (r : ℤ))
    (hz0 : 0 ≤ z) (hzt : z < (r : ℤ)) : shadow σ l = z := by
  have heq : ((shadow σ l : ℤ) : F) = (z : F) := by rw [← shadow_toF, h]
  exact int_cast_inj h0 hlt hz0 hzt heq

/-- A product row's output variable holds the product of the factors' shadows: if the row
holds, both factors' values are casts of integers and their product is below `r`, then the
variable's representative is that product. -/
theorem val_of_mul {σ : V → F} {a b : ℤ} {t : V}
    (h : σ t = (a : F) * (b : F)) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b < (r : ℤ)) :
    (σ t).val = (a * b).toNat := by
  have hcast : ((a * b : ℤ) : F) = σ t := by
    rw [h]
    push_cast
    rfl
  have hlt : (a * b).toNat < r := by
    have h1 : (a * b).toNat = a * b := Int.toNat_of_nonneg (by positivity)
    omega
  have h2 : (((a * b).toNat : ℕ) : F) = σ t := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by positivity)]
    exact hcast
  rw [← h2]
  exact ZMod.val_natCast_of_lt hlt

/-- **A plug's shadow is its products' sum.** Every variable of the combination is a
product row's output whose factors' values are the integers `fa`, `fb`; then the shadow is
the combination's constant plus the coefficients times the integer products. This is the
step from the circuit's product rows to a column's integer value. -/
theorem shadow_of_products {σ : ℕ → F} {l : ZLC} (fa fb : ℕ → ℤ)
    (hterm : ∀ t ∈ l.terms, σ t.2 = (fa t.2 : F) * (fb t.2 : F))
    (ha : ∀ t ∈ l.terms, 0 ≤ fa t.2) (hb : ∀ t ∈ l.terms, 0 ≤ fb t.2)
    (hab : ∀ t ∈ l.terms, fa t.2 * fb t.2 < (r : ℤ)) :
    shadow σ l = l.const + (l.terms.map fun t => t.1 * (fa t.2 * fb t.2)).sum := by
  simp only [shadow]
  have hmap : l.terms.map (fun t : ℤ × ℕ => t.1 * (((σ t.2).val : ℕ) : ℤ))
      = l.terms.map fun t => t.1 * (fa t.2 * fb t.2) := by
    refine List.map_congr_left fun t ht => ?_
    show t.1 * (((σ t.2).val : ℕ) : ℤ) = t.1 * (fa t.2 * fb t.2)
    rw [val_of_mul (hterm t ht) (ha t ht) (hb t ht) (hab t ht),
      Int.toNat_of_nonneg (by have := ha t ht; have := hb t ht; positivity)]
  rw [hmap]

end Xark.Circuit
