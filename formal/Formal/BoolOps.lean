/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.Xor
import Formal.Templates.Or
import Formal.GrumpkinGroup

set_option linter.style.header false

/-!
# `Field::xor` and `Field::or`, proven over their exported rows, and their constant folds

`Formal/Templates/Xor.lean` and `Formal/Templates/Or.lean` are the R1CS the frontend
emits for one call of `Field::xor` / `Field::or` on two fresh variables
(`cargo xtask lean-export xor` / `or`): one row each, `(2a) · b = a + b − c` and
`a · b = a + b − c`, with the output `c` hinted. For each template:

* `sat_iff`: the row holds iff `c = a + b − 2ab` (resp. `a + b − ab`), for **any**
  field inputs, so `c` has no prover freedom;
* `soundness`: on input bits, `c` is the bit `a ⊕ b` (resp. `a ∨ b`);
* `fold_lhs` / `fold_rhs`: with either input the constant `k`, the row holds iff
  `c = k + (1 − 2k)·x` (resp. `k + (1 − k)·x`), `x` the other input. That linear form
  is what the frontend emits in place of the row and `c` (`host.rs`, `Intr::Xor`), so a
  folded call is this template with `k` substituted and `c` eliminated, which
  `Xark.R1cs.elim_sound` shows changes no solution.

The input assumption of `soundness` (bits) is the caller's: `Field::xor` documents it,
and every caller in the gadget crates passes outputs of `to_bits`, `hint_bit` pinned by
`require_bool`, or an earlier XOR/AND/NOT of bits. `sat_iff` and the folds need none.
-/

open Xark.Template Xark.R1cs

namespace Xark.Templates.Xor

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The input assumption: both inputs are bits. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The spec: the result is the bit `a ⊕ b`. -/
def Spec (ins outs : List F) : Prop :=
  outs = [if ins.getD 0 0 = ins.getD 1 0 then 0 else 1]

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1)] := by
  decide +kernel

theorem outputs_eq : template.outputs = [LC.var (.wit 0)] := by
  decide +kernel

theorem rows_eq : template.rows =
    [⟨⟨0, [(2, .plug 0)]⟩, LC.var (.plug 1), ⟨0, [(1, .plug 0), (1, .plug 1), (-1, .wit 0)]⟩⟩] := by
  decide +kernel

theorem ins_eq (σ : TVar → F) : template.ins σ = [σ (.plug 0), σ (.plug 1)] := by
  simp [Template.ins, inputs_eq]

theorem outs_eq (σ : TVar → F) : template.outs σ = [σ (.wit 0)] := by
  simp [Template.outs, outputs_eq]

/-- The row holds iff the output is `a + b − 2ab`, whatever the inputs. -/
theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    σ (.wit 0) = σ (.plug 0) + σ (.plug 1) - 2 * σ (.plug 0) * σ (.plug 1) := by
  simp only [Template.Sat, rows_eq, Xark.R1cs.Sat, List.mem_singleton, forall_eq, Row.Sat,
    LC.eval, LC.var, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  constructor <;> intro h <;> linear_combination h

/-- **Soundness.** On input bits, every assignment satisfying the row outputs `a ⊕ b`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [ins_eq] at ha ⊢
  rw [outs_eq, (sat_iff σ).mp h]
  have h0 : IsBit (σ (.plug 0)) := ha _ (by simp)
  have h1 : IsBit (σ (.plug 1)) := ha _ (by simp)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    norm_num [Spec, h0, h1]

/-- **Folding a constant left operand.** With input `0` the constant `k`, the row
holds iff the output is `k + (1 − 2k)·b`. -/
theorem fold_lhs (k : F) (σ : TVar → F) :
    Xark.R1cs.Sat (Xark.R1cs.subst template.rows (.plug 0) (LC.cst k)) σ ↔
      σ (.wit 0) = k + (1 - 2 * k) * σ (.plug 1) := by
  rw [Xark.R1cs.sat_subst]
  change template.Sat _ ↔ _
  rw [sat_iff]
  simp only [LC.eval_cst, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne, TVar.plug.injEq]
  constructor <;> intro h <;> linear_combination h

/-- **Folding a constant right operand.** With input `1` the constant `k`, the row
holds iff the output is `k + (1 − 2k)·a`. -/
theorem fold_rhs (k : F) (σ : TVar → F) :
    Xark.R1cs.Sat (Xark.R1cs.subst template.rows (.plug 1) (LC.cst k)) σ ↔
      σ (.wit 0) = k + (1 - 2 * k) * σ (.plug 0) := by
  rw [Xark.R1cs.sat_subst]
  change template.Sat _ ↔ _
  rw [sat_iff]
  simp only [LC.eval_cst, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne, TVar.plug.injEq]
  constructor <;> intro h <;> linear_combination h

/-- **Its outputs are bits** (on input bits): a producer of bits for the calls it feeds
(`lean-export --coverage`, "assumptions discharged by producer"). -/
theorem outs_isBit (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    ∀ v ∈ template.outs σ, IsBit v := by
  have hs := soundness σ ha h
  rw [Spec] at hs
  rw [hs]
  intro v hv
  rw [List.mem_singleton] at hv
  subst hv
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end Xark.Templates.Xor

namespace Xark.Templates.Or

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The input assumption: both inputs are bits. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The spec: the result is the bit `a ∨ b`. -/
def Spec (ins outs : List F) : Prop :=
  outs = [if ins.getD 0 0 = 0 ∧ ins.getD 1 0 = 0 then 0 else 1]

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1)] := by
  decide +kernel

theorem outputs_eq : template.outputs = [LC.var (.wit 0)] := by
  decide +kernel

theorem rows_eq : template.rows =
    [⟨LC.var (.plug 0), LC.var (.plug 1), ⟨0, [(1, .plug 0), (1, .plug 1), (-1, .wit 0)]⟩⟩] := by
  decide +kernel

theorem ins_eq (σ : TVar → F) : template.ins σ = [σ (.plug 0), σ (.plug 1)] := by
  simp [Template.ins, inputs_eq]

theorem outs_eq (σ : TVar → F) : template.outs σ = [σ (.wit 0)] := by
  simp [Template.outs, outputs_eq]

/-- The row holds iff the output is `a + b − ab`, whatever the inputs. -/
theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    σ (.wit 0) = σ (.plug 0) + σ (.plug 1) - σ (.plug 0) * σ (.plug 1) := by
  simp only [Template.Sat, rows_eq, Xark.R1cs.Sat, List.mem_singleton, forall_eq, Row.Sat,
    LC.eval, LC.var, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  constructor <;> intro h <;> linear_combination h

/-- **Soundness.** On input bits, every assignment satisfying the row outputs `a ∨ b`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [ins_eq] at ha ⊢
  rw [outs_eq, (sat_iff σ).mp h]
  have h0 : IsBit (σ (.plug 0)) := ha _ (by simp)
  have h1 : IsBit (σ (.plug 1)) := ha _ (by simp)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    simp [Spec, h0, h1]

/-- **Folding a constant left operand.** With input `0` the constant `k`, the row
holds iff the output is `k + (1 − k)·b`. -/
theorem fold_lhs (k : F) (σ : TVar → F) :
    Xark.R1cs.Sat (Xark.R1cs.subst template.rows (.plug 0) (LC.cst k)) σ ↔
      σ (.wit 0) = k + (1 - k) * σ (.plug 1) := by
  rw [Xark.R1cs.sat_subst]
  change template.Sat _ ↔ _
  rw [sat_iff]
  simp only [LC.eval_cst, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne, TVar.plug.injEq]
  constructor <;> intro h <;> linear_combination h

/-- **Folding a constant right operand.** With input `1` the constant `k`, the row
holds iff the output is `k + (1 − k)·a`. -/
theorem fold_rhs (k : F) (σ : TVar → F) :
    Xark.R1cs.Sat (Xark.R1cs.subst template.rows (.plug 1) (LC.cst k)) σ ↔
      σ (.wit 0) = k + (1 - k) * σ (.plug 0) := by
  rw [Xark.R1cs.sat_subst]
  change template.Sat _ ↔ _
  rw [sat_iff]
  simp only [LC.eval_cst, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne, TVar.plug.injEq]
  constructor <;> intro h <;> linear_combination h

/-- **Its outputs are bits** (on input bits): a producer of bits for the calls it feeds
(`lean-export --coverage`, "assumptions discharged by producer"). -/
theorem outs_isBit (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    ∀ v ∈ template.outs σ, IsBit v := by
  have hs := soundness σ ha h
  rw [Spec] at hs
  rw [hs]
  intro v hv
  rw [List.mem_singleton] at hv
  subst hv
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end Xark.Templates.Or
