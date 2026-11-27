/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.Sha256EmBits82
import Formal.Circuits.Rsa2048.ChainBits
import Formal.RsaEm

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# `sha256_em_bits_82`: the encoded message's limbs

The gadget emits no rows: its 25 outputs are the linear combinations
`EM82_CONST q + Σ_t 2^t · digestBit_{82q+t}`. This file proves its contract: with
`ins j` the value of plug `j`, the output limb `q` is `emOut ins q`, RFC 8017's prefix
plus the digest's bits in the 82-bit representation.
-/

namespace Xark.Templates.Sha256EmBits82

open Xark.Template Xark.R1cs

/-- The gadget reads its inputs and assumes nothing more. -/
def Assumptions (_ : List F) : Prop := True

/-- The contract: output limb `q` is the encoded message's limb `q`. -/
def Spec (ins outs : List F) : Prop :=
  ∀ q < 25, outs.getD q 0
    = ((Xark.Rsa.Em.emOut (fun j => ((ins.getD j 0).val : ℤ)) q : ℤ) : F)

/-- The digest bits that land in limb `q`: 82, except the top limb's 10. -/
def w (q : ℕ) : ℕ := min 82 (256 - 82 * q)

/-- Limb `q` as the linear combination the gadget emits. -/
def model (q : ℕ) : LC :=
  ⟨((Xark.Rsa.Em.em82 q : ℤ) : F),
    (List.range (w q)).map fun t => (((2 : F) ^ t), TVar.plug (82 * q + t))⟩

/-- `getD` through a map. -/
theorem getD_map (l : List LC) (f : LC → F) (q : ℕ) (d : LC) :
    (l.map f).getD q (f d) = f (l.getD q d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[q]? with
  | none => simp
  | some x => simp

theorem list_sum_range_map (m : ℕ) (f : ℕ → F) :
    ((List.range m).map f).sum = ∑ t ∈ Finset.range m, f t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem eval_model (q : ℕ) (σ : TVar → F) :
    (model q).eval σ = ((Xark.Rsa.Em.em82 q : ℤ) : F)
      + ∑ t ∈ Finset.range (w q), ((2 : F) ^ t) * σ (.plug (82 * q + t)) := by
  simp only [model, Xark.R1cs.LC.eval, List.map_map, Function.comp_def]
  exact congrArg (fun x => ((Xark.Rsa.Em.em82 q : ℤ) : F) + x) (list_sum_range_map _ _)

/-- The emitted limb is the model's linear combination. -/
theorem outputs_eq (q : ℕ) (hq : q < 25) :
    template.outputs.getD q ⟨0, []⟩ = model q := by
  interval_cases q <;> rfl

theorem inputs_eq :
    template.inputs = (List.range 256).map (fun j => (⟨0, [(1, TVar.plug j)]⟩ : LC)) := by
  rfl

/-- The template's inputs are the 256 digest-bit plugs. -/
theorem ins_eq (σ : TVar → F) :
    template.ins σ = (List.range 256).map (fun j => σ (.plug j)) := by
  rw [Template.ins, inputs_eq, List.map_map]
  congr 1
  funext j
  simp [Xark.R1cs.LC.eval]

theorem ins_getD (σ : TVar → F) {j : ℕ} (hj : j < 256) :
    (template.ins σ).getD j 0 = σ (.plug j) := by
  rw [ins_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp

theorem limbOf_eq_zero (bits : ℕ → ℤ) (q : ℕ) (h : 256 ≤ 82 * q) :
    Xark.Rsa.Bytes.limbOf bits 82 256 q = 0 := by
  rw [Xark.Rsa.Bytes.limbOf]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg (by omega)]

theorem outs_getD (σ : TVar → F) (q : ℕ) :
    (template.outs σ).getD q 0 = (template.outputs.getD q ⟨0, []⟩).eval σ := by
  have h := getD_map template.outputs (fun x => x.eval σ) q ⟨0, []⟩
  simpa [Template.outs, Xark.R1cs.LC.eval] using h

/-- **The gadget's contract.** -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  have _ := h
  intro q hq
  rw [outs_getD]
  rw [outputs_eq q hq, eval_model, Xark.Rsa.Em.emOut]
  rcases lt_or_ge q 3 with h3 | h3
  · have hw : w q = 82 := by unfold w; omega
    rw [hw, Xark.Circuits.Rsa2048.limbOf_full _ q 256 (by omega)]
    rw [Int.cast_add, Int.cast_sum]
    refine congrArg (fun x => ((Xark.Rsa.Em.em82 q : ℤ) : F) + x) ?_
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    rw [show (template.ins σ).getD (82 * q + t) 0 = σ (.plug (82 * q + t)) from
      ins_getD σ (by omega)]
    rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast,
      ZMod.natCast_zmod_val, mul_comm]
  · rcases eq_or_lt_of_le h3 with rfl | h4
    · have hw : w 3 = 10 := by unfold w; norm_num
      rw [hw, Xark.Circuits.Rsa2048.limbOf_small _ 3 10 (by norm_num) (by norm_num)]
      rw [Int.cast_add, Int.cast_sum]
      refine congrArg (fun x => ((Xark.Rsa.Em.em82 3 : ℤ) : F) + x) ?_
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht' := Finset.mem_range.mp ht
      rw [show (template.ins σ).getD (82 * 3 + t) 0 = σ (.plug (82 * 3 + t)) from
        ins_getD σ (by omega)]
      rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast,
        ZMod.natCast_zmod_val, mul_comm]
    · have hw : w q = 0 := by unfold w; omega
      rw [hw, limbOf_eq_zero _ q (by omega)]
      simp

end Xark.Templates.Sha256EmBits82
