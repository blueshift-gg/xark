/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.WideScalarMul
import Formal.SignedMul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_grumpkin::wide_scalar_mul`: soundness

The exported template (`Formal/Templates/WideScalarMul.lean`) reads a scalar as two
limbs `lo = plug 0`, `hi = plug 1` and a point `P = (plug 2, plug 3)`. Its rows are the
two limbs' `to_bits::<127>` (bits `1..126` hinted and pinned by booleanity, bit `0` the
linear form they leave, pinned by `b₀(b₀ − 1) = 0`: zkGolf T9, `bitRows`) and then
`signed_mul`'s rows for 254 bits (`rows_eq`, checked by the kernel), bit `i` being
`lo`'s bit `i` for `i < 127` and `hi`'s bit `i − 127` above.

`soundness`: with no assumption, the rows force `lo, hi < 2¹²⁷`, `P` onto Grumpkin,
and the output to the affine point `(lo + 2¹²⁷·hi)·P`. Every input condition is this
template's own rows (the bits by `to_bits`, `P` by the on-curve rows).
-/

namespace Xark.Templates.WideScalarMul

open Xark.Template Xark.R1cs Xark.GrumpkinMul Xark.SignedMul WeierstrassCurve.Affine

/-- A limb's bit `0`: what its hinted bits `1..126` (`w k … w (k + 125)`) leave of
it (zkGolf T9, as in `Formal/ToBits.lean`). -/
def lowLC (p k : ℕ) : LC :=
  ⟨0, (1, .plug p) :: (List.range 126).map fun i => (-((2 ^ (i + 1) : ℕ) : F), .wit (k + i))⟩

/-- Bit `i` of limb `p`, whose bits `1..126` are `w k …`. -/
def limbBit (p k i : ℕ) : LC := if i = 0 then lowLC p k else v1 (.wit (k + (i - 1)))

/-- Bit `i` of `lo + 2¹²⁷·hi`: `lo`'s bits `1..126` are `w3…w128`, `hi`'s `w129…w254`. -/
def bitVar (i : ℕ) : LC := if i < 127 then limbBit 0 3 i else limbBit 1 129 (i - 127)

/-- Where `wide_scalar_mul`'s call puts `signed_mul`'s rows. -/
def layout : Layout := ⟨254, 252, .plug 2, .plug 3, bitVar, corr254X, corr254Y⟩

def boolRow (k : ℕ) : Row := ⟨v1 (.wit k), v1 (.wit k), v1 (.wit k)⟩

/-- `b₀ · (b₀ − 1) = 0`. -/
def lowRow (p k : ℕ) : Row := ⟨lowLC p k, ⟨-1, (lowLC p k).terms⟩, ⟨0, []⟩⟩

def bitRows : List Row :=
  (List.range 126).map (fun i => boolRow (3 + i)) ++ [lowRow 0 3] ++
    (List.range 126).map (fun i => boolRow (129 + i)) ++ [lowRow 1 129]

theorem rows_eq : template.rows = onCurveRows layout ++ bitRows ++ smRows layout := by
  decide +kernel
theorem inputs_eq : template.inputs = (List.range 4).map fun i => v1 (.plug i) := by
  decide +kernel
theorem outputs_eq : template.outputs =
    [⟨corr254X, [(1, .wit 3546), (-1, .wit 3550), (-1, .wit 3558), (-1, .wit 3560),
      (1, .wit 3565)]⟩, ⟨0, [(-1, .wit 3553), (1, .wit 3566)]⟩] := by
  decide +kernel

/-! ### Spec -/

/-- The scalar `lo + 2¹²⁷·hi`. -/
def scalar (ins : List F) : ℕ := (ins.getD 0 0).val + 2 ^ 127 * (ins.getD 1 0).val

/-- The spec: both limbs are below `2¹²⁷`, `P` is on Grumpkin, and the output is the
affine point `(lo + 2¹²⁷·hi)·P`. -/
def Spec (ins outs : List F) : Prop :=
  (ins.getD 0 0).val < 2 ^ 127 ∧ (ins.getD 1 0).val < 2 ^ 127 ∧
    ∃ (hP : grumpkinCurve.Nonsingular (ins.getD 2 0) (ins.getD 3 0))
      (hR : grumpkinCurve.Nonsingular (outs.getD 0 0) (outs.getD 1 0)),
      (Point.some _ _ hR : GrumpkinPoint) = scalar ins • Point.some _ _ hP

theorem ins_getD (σ : TVar → F) {i : ℕ} (hi : i < 4) :
    (template.ins σ).getD i 0 = σ (.plug i) := by
  simp [Template.ins, inputs_eq, List.getD_eq_getElem?_getD, hi, v1, LC.eval]

theorem outs_eq (σ : TVar → F) : template.outs σ = [outX layout σ, outY layout σ] := by
  have e1 : TVar.wit (sq1 layout (layout.n - 1)) = .wit 3546 := by decide
  have e2 : TVar.wit (sq2 layout (layout.n - 1)) = .wit 3550 := by decide
  have e3 : TVar.wit (yv layout (layout.n - 1)) = .wit 3553 := by decide
  have e4 : fw layout 4 = .wit 3558 := by decide
  have e6 : fw layout 6 = .wit 3560 := by decide
  have e11 : fw layout 11 = .wit 3565 := by decide
  have e12 : fw layout 12 = .wit 3566 := by decide
  simp only [Template.outs, outputs_eq, outX, outY, e1, e2, e3, e4, e6, e11, e12,
    show layout.cX = corr254X from rfl, List.map_cons, List.map_nil, LC.eval, List.sum_cons,
    List.sum_nil, List.cons.injEq, and_true]
  constructor <;> ring

theorem sat_iff (σ : TVar → F) : template.Sat σ ↔ (∀ r ∈ onCurveRows layout, r.Sat σ) ∧
    (∀ r ∈ bitRows, r.Sat σ) ∧ ∀ r ∈ smRows layout, r.Sat σ := by
  rw [Template.Sat, rows_eq]
  simp only [Xark.R1cs.Sat, List.mem_append]
  exact ⟨fun h => ⟨fun r hr => h r (Or.inl (Or.inl hr)), fun r hr => h r (Or.inl (Or.inr hr)),
      fun r hr => h r (Or.inr hr)⟩,
    fun h r hr => hr.elim (fun hr => hr.elim (h.1 r) (h.2.1 r)) (h.2.2 r)⟩

theorem eval_v1' (x : TVar) (σ : TVar → F) : (v1 x).eval σ = σ x := by
  simp [v1, LC.eval]

theorem eval_low (p k : ℕ) (σ : TVar → F) : (lowLC p k).eval σ =
    σ (.plug p) - ∑ i ∈ Finset.range 126, ((2 ^ (i + 1) : ℕ) : F) * σ (.wit (k + i)) := by
  simp only [lowLC, LC.eval, List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
    Xark.Templates.Add32.sum_map_range, neg_mul, Finset.sum_neg_distrib]
  ring

theorem eval_lowB (p k : ℕ) (σ : TVar → F) :
    (⟨-1, (lowLC p k).terms⟩ : LC).eval σ = (lowLC p k).eval σ - 1 := by
  simp only [LC.eval, lowLC]; ring

/-- A limb's `to_bits` rows: its bits are bits and it is their word, below `2¹²⁷`. -/
theorem limb_bits {σ : TVar → F} (h : ∀ r ∈ bitRows, r.Sat σ) (p k : ℕ)
    (hb : ∀ i < 126, boolRow (k + i) ∈ bitRows) (hr : lowRow p k ∈ bitRows) :
    (∀ i < 127, IsBit ((limbBit p k i).eval σ)) ∧
      (σ (.plug p)).val = ∑ i ∈ Finset.range 127, 2 ^ i * ((limbBit p k i).eval σ).val := by
  have hw : ∀ i < 126, IsBit (σ (.wit (k + i))) := fun i hi => by
    have := h _ (hb i hi)
    simp only [boolRow, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, zero_add, add_zero, one_mul] at this
    exact Xark.Templates.Add32.isBit_of_mul_self this
  have hlow : IsBit ((lowLC p k).eval σ) := by
    have := h _ hr
    simp only [Row.Sat, lowRow, eval_lowB] at this
    have h0 : (lowLC p k).eval σ * ((lowLC p k).eval σ - 1) = 0 := by
      rw [this]; simp [LC.eval]
    rcases mul_eq_zero.mp h0 with e | e
    · exact Or.inl e
    · exact Or.inr (by linear_combination e)
  have hbit : ∀ i < 127, IsBit ((limbBit p k i).eval σ) := fun i hi => by
    rcases i with _ | i
    · simpa [limbBit] using hlow
    · simpa [limbBit, eval_v1'] using hw i (by omega)
  refine ⟨hbit, ?_⟩
  let v : ℕ → ℕ := fun i => ((limbBit p k i).eval σ).val
  have hv : ∀ i < 127, v i ≤ 1 := fun i hi => Xark.Templates.Add32.isBit_val (hbit i hi)
  have hW := Xark.Templates.Add32.word_lt v 127 hv
  have hcast : ((∑ i ∈ Finset.range 127, 2 ^ i * v i : ℕ) : F) = σ (.plug p) := by
    rw [Finset.sum_range_succ']
    push_cast
    simp only [v, limbBit, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, eval_v1',
      ZMod.natCast_val, ZMod.cast_id', id, one_mul]
    rw [eval_low]
    push_cast
    ring
  rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hW (by unfold r; norm_num))]

theorem mem_lo {i : ℕ} (hi : i < 126) : boolRow (3 + i) ∈ bitRows :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))

theorem mem_hi {i : ℕ} (hi : i < 126) : boolRow (129 + i) ∈ bitRows :=
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))

theorem mem_low0 : lowRow 0 3 ∈ bitRows :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_singleton_self _)))

theorem mem_low1 : lowRow 1 129 ∈ bitRows := List.mem_append_right _ (List.mem_singleton_self _)

/-- The 254 bits spell `lo + 2¹²⁷·hi`. -/
theorem scalar_eq (σ : TVar → F) (lo hi : ℕ)
    (hlo : lo = ∑ i ∈ Finset.range 127, 2 ^ i * ((limbBit 0 3 i).eval σ).val)
    (hhi : hi = ∑ i ∈ Finset.range 127, 2 ^ i * ((limbBit 1 129 i).eval σ).val) :
    SignedMul.scalar layout σ = lo + 2 ^ 127 * hi := by
  have hn : layout.n = 127 + 127 := rfl
  unfold SignedMul.scalar
  rw [hn, Finset.sum_range_add, hlo, hhi, Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun i hi => by
      rw [show layout.bit i = limbBit 0 3 i from if_pos (Finset.mem_range.mp hi)]
  · exact Finset.sum_congr rfl fun i _ => by
      rw [show layout.bit (127 + i) = limbBit 1 129 i by
        rw [show layout.bit (127 + i) = bitVar (127 + i) from rfl, bitVar, if_neg (by omega),
          Nat.add_sub_cancel_left], pow_add]
      ring

/-! ### Soundness -/

/-- **Soundness.** Any assignment satisfying the exported rows has limbs below `2¹²⁷`,
`P` on Grumpkin, and outputs the affine point `(lo + 2¹²⁷·hi)·P`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  obtain ⟨hon, hbits, hsm⟩ := (sat_iff σ).mp h
  obtain ⟨hlo, elo⟩ := limb_bits hbits 0 3 (fun _ hi => mem_lo hi) mem_low0
  obtain ⟨hhi, ehi⟩ := limb_bits hbits 1 129 (fun _ hi => mem_hi hi) mem_low1
  have hbit : ∀ i < layout.n, IsBit ((layout.bit i).eval σ) := fun i hi => by
    change IsBit ((bitVar i).eval σ)
    rw [bitVar]
    split_ifs with h
    · exact hlo i h
    · exact hhi (i - 127) (by have : layout.n = 254 := rfl; omega)
  obtain ⟨hP, hR, e⟩ := sound layout (by decide) corr254Ns corr254_eq hon hsm hbit
  have hsc := scalar_eq σ _ _ elo ehi
  have wlt := fun p k (hb : ∀ i < 127, IsBit ((limbBit p k i).eval σ)) =>
    Xark.Templates.Add32.word_lt (fun i => ((limbBit p k i).eval σ).val) 127
      fun i hi => Xark.Templates.Add32.isBit_val (hb i hi)
  rw [Spec, scalar, ins_getD σ (show 0 < 4 by norm_num), ins_getD σ (show 1 < 4 by norm_num),
    ins_getD σ (show 2 < 4 by norm_num), ins_getD σ (show 3 < 4 by norm_num), outs_eq, ← hsc,
    elo, ehi]
  exact ⟨wlt 0 3 hlo, wlt 1 129 hhi, hP, hR, e⟩

end Xark.Templates.WideScalarMul
