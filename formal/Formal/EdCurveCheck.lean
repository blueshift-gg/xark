/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.EdCheck
import Formal.Templates.EdFCheck
import Formal.Templates.EdOnCurveCheck
import Formal.Templates.EdDoubleCheck
import Formal.Templates.EdAddCheck
import Formal.Templates.EdTorsionCheck
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

/-!
# Ed25519's curve checks, proven over their exported rows

Each check range-checks its hinted coordinates below `2³²` (`8 × 32`-bit limbs) and
certifies them by `mul_cert_25519` calls whose operands are linear forms of its plugs
(`Formal/EdCheck.lean`: `modelRows`, `rows_eq` by `decide +kernel`). Each
assumes its input limbs below `2³⁵` (a canonical coordinate or `4p − v`); `EdCheck.lo_hi`
then bounds every operand limb below `2³⁶`, `mul_cert_25519`'s assumption.

* `EdFCheck`: `f = d·x·y`.
* `EdOnCurveCheck`: `(x, y)` is on Ed25519.
* `EdDoubleCheck`: on the curve, `(x₂, y₂) = dbl (x, y)`.
* `EdAddCheck`: for points on the curve and `f₂ = d·x₂·y₂`, `(x₃, y₃) = addE P₁ P₂`, the
  complete affine sum (`Ed25519.complete`: both denominators are nonzero).
* `EdTorsionCheck`: `x·y·(x² + y²) = 0`, on the curve the points of order dividing 8
  (`Ed25519.torsion_iff`).
-/

namespace Xark.Ed25519

/-- The complete affine sum on Ed25519. -/
noncomputable def addE (P Q : Fp × Fp) : Fp × Fp :=
  ((P.1 * Q.2 + P.2 * Q.1) / (1 + d * P.1 * Q.1 * P.2 * Q.2),
    (P.2 * Q.2 + P.1 * Q.1) / (1 - d * P.1 * Q.1 * P.2 * Q.2))

theorem addE_on (P Q : Fp × Fp) (hP : OnEdwards d P.1 P.2) (hQ : OnEdwards d Q.1 Q.2) :
    OnEdwards d (addE P Q).1 (addE P Q).2 := by
  obtain ⟨h1, h2⟩ := complete _ _ _ _ hP hQ
  refine edwards_add_on_curve d P.1 P.2 Q.1 Q.2 _ _ hP hQ ?_ ?_ h1 h2
  · simp only [addE]; rw [div_mul_cancel₀ _ h1]
  · simp only [addE]; rw [div_mul_cancel₀ _ h2]

end Xark.Ed25519

namespace Xark.Templates.EdFCheck
open Xark.Template Xark.R1cs Xark.Templates.EdCheck
open Xark.Templates.EcK1Check (OpD OpD.lc)
open Xark.Ed25519 (Fp d)
export Xark.Templates.Add32 (IsBit)

/-- Plug vectors `x = 0`, `y = 1`, `f = 2`: `x·y − d⁻¹·f ≡ 0`. -/
def blk : Blk
  | _, 0 => (z0, [(1, 0)]) | _, 1 => (z0, [(1, 1)]) | _, 2 => (cstv dInv, []) | _, 3 => (z0, [(1, 2)])
  | _, _ => (z0, [])

abbrev ops : ℕ → ℕ → OpD := ops' blk

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows 16 8 1 ops := by decide +kernel
theorem inputs_eq : template.inputs = (List.range (16 + 8)).map fun j => LC.var (.plug j) := by
  decide +kernel
theorem outputs_eq : template.outputs = [] := by decide +kernel
theorem idx : ∀ n < 1, ∀ m < 56, ∀ t ∈ (ops n m).2, t.2 < 16 + 8 := by decide +kernel
theorem lo_hi : ∀ n < 1, ∀ m < 56, 0 ≤ (ops n m).lo (bdOf 16) ∧ (ops n m).hi (bdOf 16) < 2 ^ 36 := by
  decide +kernel

/-- The input assumption: the input limbs (plugs `0..15`) are below `2³⁵`. -/
def Assumptions (ins : List F) : Prop := ∀ i < 16, (ins.getD i 0).val < 2 ^ 35

/-- The hinted limbs (plugs `16..23`) are below `2³²`. -/
def Ranged (ins : List F) : Prop := ∀ i, 16 ≤ i → i < 16 + 8 → (ins.getD i 0).val < 2 ^ 32

theorem X_eq (σ : TVar → F) (k : ℕ) (hk : 8 * k + 8 ≤ 16 + 8) : X (template.ins σ) k = Y σ k :=
  X_of template _ inputs_eq σ k hk

theorem sound₀ (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Ranged (template.ins σ) ∧ ∀ n < 1, Eqn blk n σ :=
  model_sound template 16 8 1 blk inputs_eq rows_eq idx lo_hi σ ha h

theorem eqn0 (σ : TVar → F) : Eqn blk 0 σ ↔ Y σ 0 * Y σ 1 - (dInv : Fp) * Y σ 2 = 0 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

/-- `f`'s limbs are below `2³²` and `f = d·x·y`. -/
def Spec (ins : List F) : Prop := Ranged ins ∧ X ins 2 = d * X ins 0 * X ins 1

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  obtain ⟨hr, he⟩ := sound₀ σ ha h
  have c0 := (eqn0 σ).mp (he 0 (by norm_num))
  refine ⟨hr, ?_⟩
  rw [X_eq σ 0 (by norm_num), X_eq σ 1 (by norm_num), X_eq σ 2 (by norm_num)]
  linear_combination (-d) * c0 - Y σ 2 * d_dInv

end Xark.Templates.EdFCheck

namespace Xark.Templates.EdOnCurveCheck
open Xark.Template Xark.R1cs Xark.Templates.EdCheck
open Xark.Templates.EcK1Check (OpD OpD.lc)
open Xark.Ed25519 (Fp d)
export Xark.Templates.Add32 (IsBit)

/-- Plug vectors `x = 0`, `y = 1`, `s = 2`, `u = 3`: `x·x ≡ s`, `y·y ≡ u`,
`s·u − d⁻¹·(4p + u − s − 1) ≡ 0`. -/
def blk : Blk
  | 0, 0 => (z0, [(1, 0)]) | 0, 1 => (z0, [(1, 0)]) | 0, 6 => (z0, [(1, 2)])
  | 1, 0 => (z0, [(1, 1)]) | 1, 1 => (z0, [(1, 1)]) | 1, 6 => (z0, [(1, 3)])
  | 2, 0 => (z0, [(1, 2)]) | 2, 1 => (z0, [(1, 3)]) | 2, 2 => (cstv dInv, [])
  | 2, 3 => (b4 (-1), [(1, 3), (-1, 2)])
  | _, _ => (z0, [])

abbrev ops : ℕ → ℕ → OpD := ops' blk

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows 16 16 3 ops := by decide +kernel
theorem inputs_eq : template.inputs = (List.range (16 + 16)).map fun j => LC.var (.plug j) := by
  decide +kernel
theorem outputs_eq : template.outputs = [] := by decide +kernel
theorem idx : ∀ n < 3, ∀ m < 56, ∀ t ∈ (ops n m).2, t.2 < 16 + 16 := by decide +kernel
theorem lo_hi : ∀ n < 3, ∀ m < 56, 0 ≤ (ops n m).lo (bdOf 16) ∧ (ops n m).hi (bdOf 16) < 2 ^ 36 := by
  decide +kernel

/-- The input assumption: the input limbs (plugs `0..15`) are below `2³⁵`. -/
def Assumptions (ins : List F) : Prop := ∀ i < 16, (ins.getD i 0).val < 2 ^ 35

/-- The hinted limbs (plugs `16..31`) are below `2³²`. -/
def Ranged (ins : List F) : Prop := ∀ i, 16 ≤ i → i < 16 + 16 → (ins.getD i 0).val < 2 ^ 32

theorem X_eq (σ : TVar → F) (k : ℕ) (hk : 8 * k + 8 ≤ 16 + 16) : X (template.ins σ) k = Y σ k :=
  X_of template _ inputs_eq σ k hk

theorem sound₀ (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Ranged (template.ins σ) ∧ ∀ n < 3, Eqn blk n σ :=
  model_sound template 16 16 3 blk inputs_eq rows_eq idx lo_hi σ ha h

theorem eqn0 (σ : TVar → F) : Eqn blk 0 σ ↔ Y σ 0 * Y σ 0 = Y σ 2 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn1 (σ : TVar → F) : Eqn blk 1 σ ↔ Y σ 1 * Y σ 1 = Y σ 3 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn2 (σ : TVar → F) : Eqn blk 2 σ ↔ Y σ 2 * Y σ 3 - (dInv : Fp) * (-1 + Y σ 3 - Y σ 2) = 0 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

/-- `s`, `u` below `2³²` and `(x, y)` on the curve. -/
def Spec (ins : List F) : Prop := Ranged ins ∧ OnEdwards d (X ins 0) (X ins 1)

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  obtain ⟨hr, he⟩ := sound₀ σ ha h
  have c0 := (eqn0 σ).mp (he 0 (by norm_num))
  have c1 := (eqn1 σ).mp (he 1 (by norm_num))
  have c2 := (eqn2 σ).mp (he 2 (by norm_num))
  refine ⟨hr, ?_⟩
  rw [X_eq σ 0 (by norm_num), X_eq σ 1 (by norm_num), OnEdwards]
  linear_combination -d * c2 + c1 - c0 - d * Y σ 0 ^ 2 * c1 - d * Y σ 3 * c0 -
    (Y σ 3 - Y σ 2 - 1) * d_dInv

end Xark.Templates.EdOnCurveCheck

namespace Xark.Templates.EdDoubleCheck
open Xark.Template Xark.R1cs Xark.Templates.EdCheck
open Xark.Templates.EcK1Check (OpD OpD.lc)
open Xark.Ed25519 (Fp d)
export Xark.Templates.Add32 (IsBit)

/-- Plug vectors `x = 0`, `y = 1`, `s = 2`, `u = 3`, `x₂ = 4`, `y₂ = 5`: `x·x ≡ s`,
`y·y ≡ u`, `x₂·(4p + u − s) − 2x·y ≡ 0`, `y₂·(4p + 2 − u + s) ≡ u + s`. -/
def blk : Blk
  | 0, 0 => (z0, [(1, 0)]) | 0, 1 => (z0, [(1, 0)]) | 0, 6 => (z0, [(1, 2)])
  | 1, 0 => (z0, [(1, 1)]) | 1, 1 => (z0, [(1, 1)]) | 1, 6 => (z0, [(1, 3)])
  | 2, 0 => (z0, [(1, 4)]) | 2, 1 => (b4 0, [(1, 3), (-1, 2)]) | 2, 2 => (sm 0, [(2, 0)])
  | 2, 3 => (z0, [(1, 1)])
  | 3, 0 => (z0, [(1, 5)]) | 3, 1 => (b4 2, [(-1, 3), (1, 2)]) | 3, 6 => (sm 0, [(1, 3), (1, 2)])
  | _, _ => (z0, [])

abbrev ops : ℕ → ℕ → OpD := ops' blk

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows 16 32 4 ops := by decide +kernel
theorem inputs_eq : template.inputs = (List.range (16 + 32)).map fun j => LC.var (.plug j) := by
  decide +kernel
theorem outputs_eq : template.outputs = [] := by decide +kernel
theorem idx : ∀ n < 4, ∀ m < 56, ∀ t ∈ (ops n m).2, t.2 < 16 + 32 := by decide +kernel
theorem lo_hi : ∀ n < 4, ∀ m < 56, 0 ≤ (ops n m).lo (bdOf 16) ∧ (ops n m).hi (bdOf 16) < 2 ^ 36 := by
  decide +kernel

/-- The input assumption: the input limbs (plugs `0..15`) are below `2³⁵`. -/
def Assumptions (ins : List F) : Prop := ∀ i < 16, (ins.getD i 0).val < 2 ^ 35

/-- The hinted limbs (plugs `16..47`) are below `2³²`. -/
def Ranged (ins : List F) : Prop := ∀ i, 16 ≤ i → i < 16 + 32 → (ins.getD i 0).val < 2 ^ 32

theorem X_eq (σ : TVar → F) (k : ℕ) (hk : 8 * k + 8 ≤ 16 + 32) : X (template.ins σ) k = Y σ k :=
  X_of template _ inputs_eq σ k hk

theorem sound₀ (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Ranged (template.ins σ) ∧ ∀ n < 4, Eqn blk n σ :=
  model_sound template 16 32 4 blk inputs_eq rows_eq idx lo_hi σ ha h

theorem eqn0 (σ : TVar → F) : Eqn blk 0 σ ↔ Y σ 0 * Y σ 0 = Y σ 2 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn1 (σ : TVar → F) : Eqn blk 1 σ ↔ Y σ 1 * Y σ 1 = Y σ 3 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn2 (σ : TVar → F) : Eqn blk 2 σ ↔ Y σ 4 * (Y σ 3 - Y σ 2) - 2 * Y σ 0 * Y σ 1 = 0 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn3 (σ : TVar → F) : Eqn blk 3 σ ↔ Y σ 5 * (2 - Y σ 3 + Y σ 2) = Y σ 3 + Y σ 2 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

/-- The hinted limbs below `2³²` and, for `(x, y)` on the curve, `(x₂, y₂) = 2·(x, y)`. -/
def Spec (ins : List F) : Prop :=
  Ranged ins ∧ (OnEdwards d (X ins 0) (X ins 1) →
    (X ins 4, X ins 5) = Xark.Ed25519.dbl (X ins 0, X ins 1))

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  obtain ⟨hr, he⟩ := sound₀ σ ha h
  have c0 := (eqn0 σ).mp (he 0 (by norm_num))
  have c1 := (eqn1 σ).mp (he 1 (by norm_num))
  have c2 := (eqn2 σ).mp (he 2 (by norm_num))
  have c3 := (eqn3 σ).mp (he 3 (by norm_num))
  refine ⟨hr, fun hc => ?_⟩
  simp only [X_eq σ 0 (by norm_num), X_eq σ 1 (by norm_num), X_eq σ 4 (by norm_num),
    X_eq σ 5 (by norm_num)] at hc ⊢
  obtain ⟨hn1, hn2⟩ := Xark.Ed25519.double_dens _ _ hc
  simp only [Xark.Ed25519.dbl, Prod.mk.injEq]
  rw [eq_div_iff hn1, eq_div_iff hn2]
  constructor
  · linear_combination c2 + Y σ 4 * (c1 - c0)
  · linear_combination c3 + (Y σ 5 - 1) * c0 - (Y σ 5 + 1) * c1

end Xark.Templates.EdDoubleCheck

namespace Xark.Templates.EdAddCheck
open Xark.Template Xark.R1cs Xark.Templates.EdCheck
open Xark.Templates.EcK1Check (OpD OpD.lc)
open Xark.Ed25519 (Fp d)
export Xark.Templates.Add32 (IsBit)

/-- Plug vectors `x₁ = 0`, `y₁ = 1`, `x₂ = 2`, `y₂ = 3`, `f₂ = 4`, `t = 5`, `e = 6`,
`x₃ = 7`, `y₃ = 8`: `x₁·y₁ ≡ t`, `t·f₂ ≡ e`, `x₃·(1 + e) − x₁·y₂ − y₁·x₂ ≡ 0`,
`y₃·(4p + 1 − e) − y₁·y₂ − x₁·x₂ ≡ 0`. -/
def blk : Blk
  | 0, 0 => (z0, [(1, 0)]) | 0, 1 => (z0, [(1, 1)]) | 0, 6 => (z0, [(1, 5)])
  | 1, 0 => (z0, [(1, 5)]) | 1, 1 => (z0, [(1, 4)]) | 1, 6 => (z0, [(1, 6)])
  | 2, 0 => (z0, [(1, 7)]) | 2, 1 => (sm 1, [(1, 6)]) | 2, 2 => (z0, [(1, 0)])
  | 2, 3 => (z0, [(1, 3)]) | 2, 4 => (z0, [(1, 1)]) | 2, 5 => (z0, [(1, 2)])
  | 3, 0 => (z0, [(1, 8)]) | 3, 1 => (b4 1, [(-1, 6)]) | 3, 2 => (z0, [(1, 1)])
  | 3, 3 => (z0, [(1, 3)]) | 3, 4 => (z0, [(1, 0)]) | 3, 5 => (z0, [(1, 2)])
  | _, _ => (z0, [])

abbrev ops : ℕ → ℕ → OpD := ops' blk

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows 40 32 4 ops := by decide +kernel
theorem inputs_eq : template.inputs = (List.range (40 + 32)).map fun j => LC.var (.plug j) := by
  decide +kernel
theorem outputs_eq : template.outputs = [] := by decide +kernel
theorem idx : ∀ n < 4, ∀ m < 56, ∀ t ∈ (ops n m).2, t.2 < 40 + 32 := by decide +kernel
theorem lo_hi : ∀ n < 4, ∀ m < 56, 0 ≤ (ops n m).lo (bdOf 40) ∧ (ops n m).hi (bdOf 40) < 2 ^ 36 := by
  decide +kernel

/-- The input assumption: the input limbs (plugs `0..39`) are below `2³⁵`. -/
def Assumptions (ins : List F) : Prop := ∀ i < 40, (ins.getD i 0).val < 2 ^ 35

/-- The hinted limbs (plugs `40..71`) are below `2³²`. -/
def Ranged (ins : List F) : Prop := ∀ i, 40 ≤ i → i < 40 + 32 → (ins.getD i 0).val < 2 ^ 32

theorem X_eq (σ : TVar → F) (k : ℕ) (hk : 8 * k + 8 ≤ 40 + 32) : X (template.ins σ) k = Y σ k :=
  X_of template _ inputs_eq σ k hk

theorem sound₀ (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Ranged (template.ins σ) ∧ ∀ n < 4, Eqn blk n σ :=
  model_sound template 40 32 4 blk inputs_eq rows_eq idx lo_hi σ ha h

theorem eqn0 (σ : TVar → F) : Eqn blk 0 σ ↔ Y σ 0 * Y σ 1 = Y σ 5 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn1 (σ : TVar → F) : Eqn blk 1 σ ↔ Y σ 5 * Y σ 4 = Y σ 6 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn2 (σ : TVar → F) : Eqn blk 2 σ ↔ Y σ 7 * (1 + Y σ 6) - Y σ 0 * Y σ 3 - Y σ 1 * Y σ 2 = 0 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn3 (σ : TVar → F) : Eqn blk 3 σ ↔ Y σ 8 * (1 - Y σ 6) - Y σ 1 * Y σ 3 - Y σ 0 * Y σ 2 = 0 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

/-- The hinted limbs below `2³²` and, for `P₁`, `P₂` on the curve and `f₂ = d·x₂·y₂`,
`(x₃, y₃) = P₁ + P₂`. -/
def Spec (ins : List F) : Prop :=
  Ranged ins ∧ (OnEdwards d (X ins 0) (X ins 1) → OnEdwards d (X ins 2) (X ins 3) →
    X ins 4 = d * X ins 2 * X ins 3 →
    (X ins 7, X ins 8) = Xark.Ed25519.addE (X ins 0, X ins 1) (X ins 2, X ins 3))

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  obtain ⟨hr, he⟩ := sound₀ σ ha h
  have c0 := (eqn0 σ).mp (he 0 (by norm_num))
  have c1 := (eqn1 σ).mp (he 1 (by norm_num))
  have c2 := (eqn2 σ).mp (he 2 (by norm_num))
  have c3 := (eqn3 σ).mp (he 3 (by norm_num))
  refine ⟨hr, fun h1 h2 hf => ?_⟩
  simp only [X_eq σ 0 (by norm_num), X_eq σ 1 (by norm_num), X_eq σ 2 (by norm_num),
    X_eq σ 3 (by norm_num), X_eq σ 4 (by norm_num), X_eq σ 7 (by norm_num),
    X_eq σ 8 (by norm_num)] at h1 h2 hf ⊢
  obtain ⟨hn1, hn2⟩ := Xark.Ed25519.complete _ _ _ _ h1 h2
  have h6 : Y σ 6 = d * Y σ 0 * Y σ 2 * Y σ 1 * Y σ 3 := by
    linear_combination -c1 - Y σ 4 * c0 + Y σ 0 * Y σ 1 * hf
  simp only [Xark.Ed25519.addE, Prod.mk.injEq]
  rw [eq_div_iff hn1, eq_div_iff hn2]
  constructor
  · linear_combination c2 - Y σ 7 * h6
  · linear_combination c3 + Y σ 8 * h6

end Xark.Templates.EdAddCheck

namespace Xark.Templates.EdTorsionCheck
open Xark.Template Xark.R1cs Xark.Templates.EdCheck
open Xark.Templates.EcK1Check (OpD OpD.lc)
open Xark.Ed25519 (Fp d)
export Xark.Templates.Add32 (IsBit)

/-- Plug vectors `x = 0`, `y = 1`, `s = 2`, `u = 3`, `m = 4`: `x·x ≡ s`, `y·y ≡ u`,
`x·y ≡ m`, `m·(s + u) ≡ 0`. -/
def blk : Blk
  | 0, 0 => (z0, [(1, 0)]) | 0, 1 => (z0, [(1, 0)]) | 0, 6 => (z0, [(1, 2)])
  | 1, 0 => (z0, [(1, 1)]) | 1, 1 => (z0, [(1, 1)]) | 1, 6 => (z0, [(1, 3)])
  | 2, 0 => (z0, [(1, 0)]) | 2, 1 => (z0, [(1, 1)]) | 2, 6 => (z0, [(1, 4)])
  | 3, 0 => (z0, [(1, 4)]) | 3, 1 => (sm 0, [(1, 2), (1, 3)])
  | _, _ => (z0, [])

abbrev ops : ℕ → ℕ → OpD := ops' blk

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows 16 24 4 ops := by decide +kernel
theorem inputs_eq : template.inputs = (List.range (16 + 24)).map fun j => LC.var (.plug j) := by
  decide +kernel
theorem outputs_eq : template.outputs = [] := by decide +kernel
theorem idx : ∀ n < 4, ∀ m < 56, ∀ t ∈ (ops n m).2, t.2 < 16 + 24 := by decide +kernel
theorem lo_hi : ∀ n < 4, ∀ m < 56, 0 ≤ (ops n m).lo (bdOf 16) ∧ (ops n m).hi (bdOf 16) < 2 ^ 36 := by
  decide +kernel

/-- The input assumption: the input limbs (plugs `0..15`) are below `2³⁵`. -/
def Assumptions (ins : List F) : Prop := ∀ i < 16, (ins.getD i 0).val < 2 ^ 35

/-- The hinted limbs (plugs `16..39`) are below `2³²`. -/
def Ranged (ins : List F) : Prop := ∀ i, 16 ≤ i → i < 16 + 24 → (ins.getD i 0).val < 2 ^ 32

theorem X_eq (σ : TVar → F) (k : ℕ) (hk : 8 * k + 8 ≤ 16 + 24) : X (template.ins σ) k = Y σ k :=
  X_of template _ inputs_eq σ k hk

theorem sound₀ (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Ranged (template.ins σ) ∧ ∀ n < 4, Eqn blk n σ :=
  model_sound template 16 24 4 blk inputs_eq rows_eq idx lo_hi σ ha h

theorem eqn0 (σ : TVar → F) : Eqn blk 0 σ ↔ Y σ 0 * Y σ 0 = Y σ 2 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn1 (σ : TVar → F) : Eqn blk 1 σ ↔ Y σ 1 * Y σ 1 = Y σ 3 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn2 (σ : TVar → F) : Eqn blk 2 σ ↔ Y σ 0 * Y σ 1 = Y σ 4 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

theorem eqn3 (σ : TVar → F) : Eqn blk 3 σ ↔ Y σ 4 * (Y σ 2 + Y σ 3) = 0 := by
  simp only [Eqn, V, blk, num_z0, num_dInv, num_b4, num_sm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_zero]
  constructor <;> intro h <;> linear_combination h

/-- The hinted limbs below `2³²` and `x·y·(x² + y²) = 0`: on the curve, `8·(x, y) = O`. -/
def Spec (ins : List F) : Prop :=
  Ranged ins ∧ X ins 0 * X ins 1 * (X ins 0 ^ 2 + X ins 1 ^ 2) = 0

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  obtain ⟨hr, he⟩ := sound₀ σ ha h
  have c0 := (eqn0 σ).mp (he 0 (by norm_num))
  have c1 := (eqn1 σ).mp (he 1 (by norm_num))
  have c2 := (eqn2 σ).mp (he 2 (by norm_num))
  have c3 := (eqn3 σ).mp (he 3 (by norm_num))
  refine ⟨hr, ?_⟩
  rw [X_eq σ 0 (by norm_num), X_eq σ 1 (by norm_num)]
  linear_combination c3 + (Y σ 2 + Y σ 3) * c2 + Y σ 0 * Y σ 1 * (c0 + c1)

end Xark.Templates.EdTorsionCheck
