/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.OneHot8
import Formal.Template
import Formal.Add32

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_bignum::one_hot8`, proven over its exported rows

The fixed-base comb of `ecdsa_verify_packed` selects window `j`'s table entry as
`Σᵥ out[v]·T[v]`, with `out` the one-hot vector of the byte `Σᵢ 2ⁱbᵢ`. `one_hot8` builds
it a bit at a time: after bit `i`, `out[v + 2ⁱ] = old[v]·bᵢ` (one row, a fresh variable)
and `out[v] = old[v] − out[v + 2ⁱ]` (a linear form). Bit 0 needs no row
(`out = [1 − b₀, b₀]`), so bits `1..7` give `2 + 4 + … + 128 = 254` rows.

* `rows_eq`, `outputs_eq`: the export is the model `stage`, by
  `decide +kernel`.
* `soundness`: on bit plugs (the callers' `to_bits` outputs: `formal/coverage-allowlist.txt`),
  every satisfying assignment outputs `out[v] = 1` at `v = Σᵢ 2ⁱbᵢ` and `0` at every other
  `v < 256`.
-/

namespace Xark.Templates.OneHot8

open Xark.Template Xark.R1cs Finset
export Xark.Templates.Add32 (IsBit)

/-- The variable of `out[v + 2^(i+1)]` after bit `i + 1`. -/
def h (i v : ℕ) : ℕ := 2 ^ (i + 1) - 2 + v

/-- `out[v]` after bit `i`, as a linear form. -/
def stage : ℕ → ℕ → LC
  | 0, v => if v = 0 then ⟨1, [(-1, .plug 0)]⟩ else ⟨0, [(1, .plug 0)]⟩
  | i + 1, v =>
    if v < 2 ^ (i + 1) then ⟨(stage i v).const, (stage i v).terms ++ [(-1, .wit (h i v))]⟩
    else LC.var (.wit (h i (v - 2 ^ (i + 1))))

def modelRows : List Row :=
  (List.range 7).flatMap fun i => (List.range (2 ^ (i + 1))).map fun v =>
    ⟨stage i v, LC.var (.plug (i + 1)), LC.var (.wit (h i v))⟩
set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows := by decide +kernel
set_option maxRecDepth 100000 in
theorem outputs_eq : template.outputs = (List.range 256).map (stage 7) := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 8).map fun j => LC.var (.plug j) := by
  decide +kernel

/-- The input assumption: every input is a bit. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The byte the first `i + 1` bits spell. -/
def byte (b : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ range (i + 1), 2 ^ j * b j

/-- `out[v] = 1` at `v = Σᵢ 2ⁱbᵢ`, else `0`, for every `v < 256`. -/
def Spec (ins outs : List F) : Prop :=
  ∀ v < 256, outs.getD v 0 = if v = byte (fun j => (ins.getD j 0).val) 7 then 1 else 0

theorem byte_lt (b : ℕ → ℕ) (hb : ∀ j, b j ≤ 1) (i : ℕ) : byte b i < 2 ^ (i + 1) := by
  induction i with
  | zero => simp only [byte, zero_add, range_one, sum_singleton, pow_zero, one_mul]; have := hb 0; omega
  | succ i ih =>
    rw [byte, sum_range_succ, ← byte, pow_succ 2 (i + 1)]
    have := hb (i + 1)
    have : 2 ^ (i + 1) * b (i + 1) ≤ 2 ^ (i + 1) := by nlinarith
    omega

theorem eval_snoc (c : F) (ts : List (F × TVar)) (w : TVar) (σ : TVar → F) :
    (⟨c, ts ++ [(-1, w)]⟩ : LC).eval σ = (⟨c, ts⟩ : LC).eval σ - σ w := by
  simp only [LC.eval, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

/-- **What each stage holds.** If every row holds and the plugs are bits, `out[v]` after
bit `i` is `1` exactly at `v = byte i`. -/
theorem stage_eval (σ : TVar → F) (bit : ∀ j < 8, σ (.plug j) = 0 ∨ σ (.plug j) = 1)
    (row : ∀ i < 7, ∀ v < 2 ^ (i + 1),
      (stage i v).eval σ * σ (.plug (i + 1)) = σ (.wit (h i v))) :
    ∀ i < 8, ∀ v < 2 ^ (i + 1),
      (stage i v).eval σ = if v = byte (fun j => (σ (.plug j)).val) i then 1 else 0 := by
  set b : ℕ → ℕ := fun j => (σ (.plug j)).val
  have hb : ∀ j < 8, b j ≤ 1 := fun j hj => by
    rcases bit j hj with e | e <;> simp [b, e, ZMod.val_one]
  have hb' : ∀ j < 8, σ (.plug j) = (b j : F) := fun j hj => by
    rcases bit j hj with e | e <;> simp [b, e, ZMod.val_one]
  -- `byte` only reads bits below 8 here.
  have hlt : ∀ i < 8, byte b i < 2 ^ (i + 1) := fun i hi =>
    byte_lt (fun j => if j < 8 then b j else 0) (fun j => by split_ifs with h; exacts [hb j h, by omega]) i
      |>.trans_eq' (by simp only [byte]; refine sum_congr rfl fun j hj => ?_; simp at hj; rw [if_pos (by omega)])
  intro i
  induction i with
  | zero =>
    intro _ v hv
    have e := hb' 0 (by norm_num)
    have := hb 0 (by norm_num)
    simp only [byte, zero_add, range_one, sum_singleton, pow_zero, one_mul]
    interval_cases v <;> simp only [stage, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, if_true, one_ne_zero, if_false, e] <;> interval_cases hb0 : b 0 <;> simp
  | succ i ih =>
    intro hi v hv
    have hold := ih (by omega)
    have hr := row i (by omega)
    have e := hb' (i + 1) hi
    have hbi := hb (i + 1) hi
    have hbyte : byte b (i + 1) = byte b i + 2 ^ (i + 1) * b (i + 1) := by
      rw [byte, sum_range_succ, ← byte]
    have hl := hlt i (by omega)
    rw [hbyte]
    by_cases hv' : v < 2 ^ (i + 1)
    · simp only [stage, if_pos hv']
      rw [eval_snoc, ← hr v hv', hold v hv', e]
      interval_cases hb1 : b (i + 1)
      · simp
      · simp only [Nat.cast_one, mul_one, sub_self]
        rw [if_neg (by omega)]
    · simp only [stage, if_neg hv', LC.var, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, zero_add, one_mul, add_zero]
      have hv2 : v - 2 ^ (i + 1) < 2 ^ (i + 1) := by rw [pow_succ] at hv; omega
      rw [← hr _ hv2, hold _ hv2, e]
      interval_cases hb1 : b (i + 1)
      · simp only [Nat.cast_zero, mul_zero]; rw [if_neg (by omega)]
      · simp only [Nat.cast_one, mul_one]
        by_cases hc : v - 2 ^ (i + 1) = byte b i
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]

theorem getD_ins (σ : TVar → F) (j : ℕ) (hj : j < 8) : (template.ins σ).getD j 0 = σ (.plug j) := by
  rw [Template.ins, inputs_eq, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp [LC.var, LC.eval]

theorem rows_mem {i v : ℕ} (hi : i < 7) (hv : v < 2 ^ (i + 1)) :
    (⟨stage i v, LC.var (.plug (i + 1)), LC.var (.wit (h i v))⟩ : Row) ∈ modelRows :=
  List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩⟩

theorem byte_congr (b b' : ℕ → ℕ) (hb : ∀ j < 8, b j = b' j) : byte b 7 = byte b' 7 :=
  sum_congr rfl fun j hj => by rw [hb j (by simpa using hj)]

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (hs : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  have hlen : (template.ins σ).length = 8 := by rw [Template.ins, inputs_eq]; simp
  have bit : ∀ j < 8, σ (.plug j) = 0 ∨ σ (.plug j) = 1 := fun j hj => by
    rw [← getD_ins σ j hj]
    exact ha _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  rw [Template.Sat, rows_eq] at hs
  have row : ∀ i < 7, ∀ v < 2 ^ (i + 1),
      (stage i v).eval σ * σ (.plug (i + 1)) = σ (.wit (h i v)) := fun i hi v hv => by
    have := hs _ (rows_mem hi hv)
    simpa [Row.Sat, LC.var, LC.eval] using this
  intro v hv
  rw [Template.outs, outputs_eq, List.getD_eq_getElem _ _ (by simpa using hv)]
  simp only [List.getElem_map, List.getElem_range]
  rw [stage_eval σ bit row 7 (by norm_num) v (by norm_num; omega),
    byte_congr (fun j => (σ (.plug j)).val) (fun j => ((template.ins σ).getD j 0).val)
      fun j hj => by simp only [getD_ins σ j hj]]

end Xark.Templates.OneHot8
