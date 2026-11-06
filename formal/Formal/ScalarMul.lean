/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.ScalarMul
import Formal.SignedMul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_grumpkin::scalar_mul`: soundness

The exported template (`Formal/Templates/ScalarMul.lean`) reads 128 bits (plugs
`0..127`, little-endian) and a point `P = (plug 128, plug 129)`. Its rows are the
on-curve rows, one booleanity row `bᵢ·bᵢ = bᵢ` per bit (`boolRows`), and `signed_mul`'s
rows for 128 bits (`rows_eq`, checked by the kernel), so `SignedMul.sound` gives
`soundness`: with no input assumption, the rows force `P` onto Grumpkin and the output
to the affine point `s·P` (`s ≠ 0·P`, so `s·P ≠ 0`: `s = 0` is rejected).
-/

namespace Xark.Templates.ScalarMul

open Xark.Template Xark.R1cs Xark.GrumpkinMul Xark.SignedMul WeierstrassCurve.Affine

/-- Where `scalar_mul`'s call puts things: the bits are plugs `0..127`, `P` is
`(plug 128, plug 129)`, the steps' variables start at `128`, `corr = −(2¹²⁸·O)`. -/
def layout : Layout := ⟨128, 128, .plug 128, .plug 129, fun i => v1 (.plug i), corrX, corrY⟩

/-- `bᵢ · bᵢ = bᵢ` for each bit plug. -/
def boolRows : List Row := (List.range 128).map fun i => ⟨v1 (.plug i), v1 (.plug i), v1 (.plug i)⟩

theorem rows_eq : template.rows = onCurveRows layout ++ boolRows ++ smRows layout := by
  decide +kernel
theorem inputs_eq : template.inputs = (List.range 130).map fun i => v1 (.plug i) := by
  decide +kernel
theorem outputs_eq : template.outputs =
    [⟨corrX, [(1, .wit 1784), (-1, .wit 1788), (-1, .wit 1796), (-1, .wit 1798), (1, .wit 1803)]⟩,
      ⟨0, [(-1, .wit 1791), (1, .wit 1804)]⟩] := by
  decide +kernel

/-! ### Spec -/

/-- The scalar the 128 input bits spell, little-endian. -/
def scalar (ins : List F) : ℕ := ∑ i ∈ Finset.range 128, 2 ^ i * (ins.getD i 0).val

/-- The spec: the 128 scalar inputs are bits, `P` is on Grumpkin and the output is the
affine point `s·P`. -/
def Spec (ins outs : List F) : Prop :=
  (∀ i < 128, IsBit (ins.getD i 0)) ∧
  ∃ (hP : grumpkinCurve.Nonsingular (ins.getD 128 0) (ins.getD 129 0))
    (hR : grumpkinCurve.Nonsingular (outs.getD 0 0) (outs.getD 1 0)),
    (Point.some _ _ hR : GrumpkinPoint) = scalar ins • Point.some _ _ hP

theorem ins_getD (σ : TVar → F) {i : ℕ} (hi : i < 130) :
    (template.ins σ).getD i 0 = σ (.plug i) := by
  simp [Template.ins, inputs_eq, List.getD_eq_getElem?_getD, hi, v1, LC.eval]

theorem outs_eq (σ : TVar → F) : template.outs σ = [outX layout σ, outY layout σ] := by
  have e1 : TVar.wit (sq1 layout (layout.n - 1)) = .wit 1784 := by decide
  have e2 : TVar.wit (sq2 layout (layout.n - 1)) = .wit 1788 := by decide
  have e3 : TVar.wit (yv layout (layout.n - 1)) = .wit 1791 := by decide
  have e4 : fw layout 4 = .wit 1796 := by decide
  have e6 : fw layout 6 = .wit 1798 := by decide
  have e11 : fw layout 11 = .wit 1803 := by decide
  have e12 : fw layout 12 = .wit 1804 := by decide
  simp only [Template.outs, outputs_eq, outX, outY, e1, e2, e3, e4, e6, e11, e12,
    show layout.cX = corrX from rfl, List.map_cons, List.map_nil, LC.eval, List.sum_cons,
    List.sum_nil, List.cons.injEq, and_true]
  constructor <;> ring

theorem sat_iff (σ : TVar → F) : template.Sat σ ↔ (∀ r ∈ onCurveRows layout, r.Sat σ) ∧
    (∀ r ∈ boolRows, r.Sat σ) ∧ ∀ r ∈ smRows layout, r.Sat σ := by
  rw [Template.Sat, rows_eq]
  simp only [Xark.R1cs.Sat, List.mem_append]
  exact ⟨fun h => ⟨fun r hr => h r (Or.inl (Or.inl hr)), fun r hr => h r (Or.inl (Or.inr hr)),
      fun r hr => h r (Or.inr hr)⟩,
    fun h r hr => hr.elim (fun hr => hr.elim (h.1 r) (h.2.1 r)) (h.2.2 r)⟩

/-! ### Soundness -/

theorem bit_eval (i : ℕ) (σ : TVar → F) : (layout.bit i).eval σ = σ (.plug i) := by
  simp [layout, v1, LC.eval]

/-- **Soundness.** Any assignment satisfying the exported rows has `P` on Grumpkin, its
128 scalar inputs bits, and outputs the affine point `s·P`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  obtain ⟨hon, hbits, hsm⟩ := (sat_iff σ).mp h
  have hbit : ∀ i < layout.n, IsBit ((layout.bit i).eval (σ)) := fun i hi => by
    have := hbits _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simp only [v1, Row.Sat, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, zero_add, add_zero, one_mul] at this
    rw [bit_eval]
    exact Xark.Templates.Add32.isBit_of_mul_self this
  obtain ⟨hP, hR, e⟩ := sound layout (by decide) corrNs corr_eq hon hsm hbit
  have hsc : scalar (template.ins σ) = SignedMul.scalar layout σ :=
    Finset.sum_congr rfl fun i hi => by
      rw [ins_getD σ (by have : layout.n = 128 := rfl; simp at hi; omega), bit_eval]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [ins_getD σ (by omega), ← bit_eval i σ]; exact hbit i hi
  rw [hsc, ins_getD σ (show 128 < 130 by norm_num), ins_getD σ (show 129 < 130 by norm_num),
    outs_eq]
  exact ⟨hP, hR, e⟩

end Xark.Templates.ScalarMul
