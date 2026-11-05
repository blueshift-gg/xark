/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.ToBits
import Formal.Add32

set_option linter.style.header false

/-!
# `Field::to_bits`, proven over its exported rows: the `n`-row range check

`Formal/Templates/ToBits.lean` is the R1CS the frontend emits for one
`Field::to_bits::<8>` on a fresh variable `x` (`cargo xtask lean-export to_bits`).
Every bit decomposition the frontend makes is this shape
(`crates/frontend/src/builder.rs::decompose_bits_gated`), for a width `n = m + 1`:
bits `1..n` are hinted variables `wᵢ` pinned by `wᵢ · wᵢ = wᵢ`, and bit `0` is the
linear form they leave, `b₀ = x − Σᵢ 2ⁱ⁺¹·wᵢ`, pinned by the one row
`b₀ · (b₀ − 1) = 0`. That is `n` rows and `n − 1` variables, where hinting all `n`
bits and adding a recomposition row costs one more of each (zkGolf's T9 range check,
`d9e2018b`, with the computed bit at the bottom so no coefficient is `2^−(n−1)`).

The rows are modelled for every `m` (`modelRows`), and the exported template is the
model at `m = 7` (`rows_eq`).

* `model_sound`: for `n ≤ 253`, so that `2ⁿ < r` (bug checklist 3, 9), every
  assignment satisfying the rows has `x < 2ⁿ` and outputs exactly the `n` canonical
  bits of `x`: the range check holds and the bits have no prover freedom;
`soundness` is the template's instance. It needs no input assumption.
-/

namespace Xark.Templates.ToBits

open Xark.Template Xark.R1cs
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt testBit_word word_testBit
  sum_map_range bit_eq_testBit)

/-! ### The rows for width `m + 1` -/

/-- Bit `0`: what the hinted bits `1..m+1` leave of the input. -/
def lowLC (m : ℕ) : LC :=
  ⟨0, (1, .plug 0) :: (List.range m).map fun i => (-((2 ^ (i + 1) : ℕ) : F), .wit i)⟩

def boolRow (i : ℕ) : Row := ⟨LC.var (.wit i), LC.var (.wit i), LC.var (.wit i)⟩

/-- `b₀ · (b₀ − 1) = 0`. -/
def lowRow (m : ℕ) : Row := ⟨lowLC m, ⟨-1, (lowLC m).terms⟩, ⟨0, []⟩⟩

def modelRows (m : ℕ) : List Row := (List.range m).map boolRow ++ [lowRow m]

def modelOutputs (m : ℕ) : List LC := lowLC m :: (List.range m).map fun i => LC.var (.wit i)

/-- The spec at width `n`: the input is below `2ⁿ` and the outputs are its `n` bits,
little-endian. -/
def SpecAt (n : ℕ) (ins outs : List F) : Prop :=
  (ins.getD 0 0).val < 2 ^ n ∧ outs = (List.range n).map (bitOf (ins.getD 0 0))

/-- The spec of the exported template, at width 8. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 8 ins outs

/-! ### The exported template is the model at width 8 -/

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs 7 := by
  decide +kernel

theorem rows_eq : template.rows = modelRows 7 := by
  decide +kernel

/-! ### The rows' meaning -/

instance : Fact (Nat.Prime r) := bn254_r_prime

theorem eval_lowLC (m : ℕ) (σ : TVar → F) :
    (lowLC m).eval σ =
      σ (.plug 0) - ∑ i ∈ Finset.range m, ((2 ^ (i + 1) : ℕ) : F) * σ (.wit i) := by
  simp only [lowLC, LC.eval, List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
    sum_map_range, neg_mul, Finset.sum_neg_distrib]
  ring

theorem sat_iff (m : ℕ) (σ : TVar → F) : Xark.R1cs.Sat (modelRows m) σ ↔
    (∀ i < m, σ (.wit i) * σ (.wit i) = σ (.wit i)) ∧
      (lowLC m).eval σ * ((lowLC m).eval σ - 1) = 0 := by
  have hB : (⟨-1, (lowLC m).terms⟩ : LC).eval σ = (lowLC m).eval σ - 1 := by
    simp only [LC.eval, lowLC]; ring
  simp only [Xark.R1cs.Sat, modelRows, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa [Row.Sat, boolRow] using h _ (Or.inl ⟨i, hi, rfl⟩)
    · have := h _ (Or.inr rfl)
      simp only [Row.Sat, lowRow, hB] at this
      simpa [LC.eval] using this
  · rintro ⟨hb, hl⟩ row (⟨i, hi, rfl⟩ | rfl)
    · simpa [Row.Sat, boolRow] using hb i hi
    · simp only [Row.Sat, lowRow, hB]
      simpa [LC.eval] using hl

theorem isBit_of_mul_sub_one {x : F} (h : x * (x - 1) = 0) : IsBit x := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

theorem two_pow_lt_r' {n : ℕ} (hn : n ≤ 253) : 2 ^ n < r :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hn) two_pow_lt_r

/-! ### Soundness at every width `n = m + 1 ≤ 253` -/

/-- **Soundness of the model.** Every assignment satisfying the rows of width
`m + 1 ≤ 253` has its input below `2^(m+1)` and outputs that input's bits. -/
theorem model_sound (m : ℕ) (hm : m + 1 ≤ 253) (σ : TVar → F)
    (h : Xark.R1cs.Sat (modelRows m) σ) :
    (σ (.plug 0)).val < 2 ^ (m + 1) ∧
      (modelOutputs m).map (·.eval σ) = (List.range (m + 1)).map (bitOf (σ (.plug 0))) := by
  obtain ⟨hb, hl⟩ := (sat_iff m σ).mp h
  have hw : ∀ i < m, IsBit (σ (.wit i)) := fun i hi => isBit_of_mul_self (hb i hi)
  have hlow : IsBit ((lowLC m).eval σ) := isBit_of_mul_sub_one hl
  let v : ℕ → ℕ := fun i => if i = 0 then ((lowLC m).eval σ).val else (σ (.wit (i - 1))).val
  have hv : ∀ i < m + 1, v i ≤ 1 := fun i hi => by
    by_cases h0 : i = 0
    · simpa [v, h0] using isBit_val hlow
    · simpa [v, h0] using isBit_val (hw (i - 1) (by omega))
  have hW := word_lt v (m + 1) hv
  have hcast : ((∑ i ∈ Finset.range (m + 1), 2 ^ i * v i : ℕ) : F) = σ (.plug 0) := by
    rw [Finset.sum_range_succ']
    push_cast
    simp only [v, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, if_true, one_mul,
      ZMod.natCast_val, ZMod.cast_id', id]
    rw [eval_lowLC]
    push_cast
    ring
  have hx : (σ (.plug 0)).val = ∑ i ∈ Finset.range (m + 1), 2 ^ i * v i := by
    rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hW (two_pow_lt_r' hm))]
  refine ⟨hx ▸ hW, ?_⟩
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [modelOutputs, List.map_cons, List.map_map]
  congr 1
  · rw [bitOf, hx]
    exact bit_eq_testBit hlow (by simpa [v] using testBit_word v (m + 1) hv 0 (by omega))
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [Function.comp_apply, LC.eval_var]
    rw [bitOf, hx]
    exact bit_eq_testBit (hw i hi) (by simpa [v] using testBit_word v (m + 1) hv (i + 1) (by omega))

/-! ### Every exported width

`cargo xtask lean-export to_bits` writes the template at width 8 and, for every
other width a production call uses, `Formal/Templates/ToBits<n>.lean` with its
proof file `Formal/ToBits<n>.lean`, which shows that template is the model at
`m = n − 1` and applies the two theorems below. -/

/-- **Soundness at any width.** A template whose input, outputs and rows are the
model's at `m + 1 ≤ 253` accepts only inputs below `2^(m+1)`, and outputs their bits. -/
theorem soundness_of (t : Template) (m : ℕ) (hm : m + 1 ≤ 253)
    (hi : t.inputs = [LC.var (.plug 0)]) (ho : t.outputs = modelOutputs m)
    (hr : t.rows = modelRows m) (σ : TVar → F) (h : t.Sat σ) :
    SpecAt (m + 1) (t.ins σ) (t.outs σ) := by
  rw [Template.Sat, hr] at h
  obtain ⟨hlt, hout⟩ := model_sound m hm σ h
  refine ⟨by simpa [Template.ins, hi] using hlt, ?_⟩
  simpa [Template.outs, Template.ins, ho, hi] using hout

/-- What `Spec` outputs are bits: a producer of bits for the calls it feeds
(`lean-export --coverage`, "assumptions discharged by producer"). -/
theorem spec_isBit {n : ℕ} {ins outs : List F} (h : SpecAt n ins outs) : ∀ v ∈ outs, IsBit v := by
  rw [h.2]
  intro v hv
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  rw [bitOf]; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Bits of a sum of bits.** For bits `b₀ … b_{n−1}`, `n ≤ 253`, the value
`Σ 2ⁱ·bᵢ` is below `2ⁿ` and its bits are the `bᵢ`: what a `to_bits` call that
emits no row returns when its input is such a sum (`builder.rs`, `bit_sum_shortcut`). -/
theorem spec_of_bits (b : List F) (hb : ∀ v ∈ b, IsBit v) (hn : b.length ≤ 253) :
    SpecAt b.length [∑ i ∈ Finset.range b.length, (2 : F) ^ i * b.getD i 0] b := by
  set n := b.length
  have hbit : ∀ i < n, IsBit (b.getD i 0) := fun i hi =>
    hb _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  let v : ℕ → ℕ := fun i => (b.getD i 0).val
  have hv : ∀ i < n, v i ≤ 1 := fun i hi => isBit_val (hbit i hi)
  have hW := word_lt v n hv
  have hcast : ((∑ i ∈ Finset.range n, 2 ^ i * v i : ℕ) : F) =
      ∑ i ∈ Finset.range n, (2 : F) ^ i * b.getD i 0 := by
    push_cast; simp [v]
  have hx : (∑ i ∈ Finset.range n, (2 : F) ^ i * b.getD i 0).val =
      ∑ i ∈ Finset.range n, 2 ^ i * v i := by
    rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hW (two_pow_lt_r' hn))]
  refine ⟨by rw [List.getD_cons_zero, hx]; exact hW, ?_⟩
  simp only [List.getD_cons_zero]
  apply List.ext_getElem (by simp [n])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [bitOf, hx]
  have hi : i < n := h1
  have := bit_eq_testBit (hbit i hi) (by simpa [v] using testBit_word v n hv i hi)
  rwa [List.getD_eq_getElem _ _ hi] at this

/-! ### The template -/

theorem ins_eq (σ : TVar → F) : template.ins σ = [σ (.plug 0)] := by
  simp [Template.ins, inputs_eq]

/-- **Soundness.** Any assignment satisfying the exported rows has `x < 2⁸` and outputs
exactly the 8 bits of `x`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 7 (by norm_num) inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.ToBits
