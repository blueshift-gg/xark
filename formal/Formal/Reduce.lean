/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.Reduce33
import Formal.Templates.Reduce34
import Formal.Templates.Reduce35
import Formal.Templates.Reduce36
import Formal.ToBits

set_option linter.style.header false

/-!
# `xark_bits::reduce::<N>`, proven over its exported rows

`reduce::<N>(sum)` returns the low 32 bits of `sum` and requires `sum < 2ᴺ`: the
modular reduction of a field sum of words of bits (SHA-256's `e`, `a`, schedule and
output sums, BLAKE's three-word `add3`). For `N = m + 1` its rows are:

* bits `0..m` hinted as variables `wᵢ`, each pinned by `wᵢ · wᵢ = wᵢ`;
* the top carry `t = sum − Σᵢ<m 2ⁱ·wᵢ`, a linear form, pinned by the one row
  `t · (t − 2ᵐ) = 0`, so `t ∈ {0, 2ᵐ}` (zkGolf 650c4497 / 3e1e47a3, "fused carry").

That is `N` rows and `N − 1` variables. The rows are modelled for every `m`
(`modelRows`), and each exported width (33 … 36, `cargo xtask lean-export reduce__<N>`)
is the model at `m = N − 1` (`rows_eq`, by `decide +kernel`).

* `model_sound`: for `32 ≤ m` and `m + 1 ≤ 253` (so `2ᴺ < r`, bug checklist 3 and 9),
  every satisfying assignment has `sum < 2ᴺ` and outputs exactly bits `0..32` of `sum`:
  no input assumption, and no prover freedom in the bits or the carry (checklist 8).

The caller's obligation is only that the field `sum` it passes is the integer it means,
which holds when its terms are bits with nonnegative weights whose total is below `r`
(each production `N` is the tight bound of its sum; `Formal/Legacy/Sha256.lean` shows the
SHA-256 sums').
-/

namespace Xark.Reduce

open Xark.Template Xark.R1cs
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt testBit_word word_testBit
  bit_eq_testBit)
open Xark.Templates.ToBits (boolRow two_pow_lt_r')

instance : Fact (Nat.Prime r) := bn254_r_prime

/-! ### The rows for width `m + 1` -/

/-- The top carry: what the hinted bits `0..m` leave of the input. -/
def topLC (m : ℕ) : LC :=
  ⟨0, (1, .plug 0) :: (List.range m).map fun i => (-((2 ^ i : ℕ) : F), .wit i)⟩

/-- `t · (t − 2ᵐ) = 0`. -/
def topRow (m : ℕ) : Row := ⟨topLC m, ⟨-((2 ^ m : ℕ) : F), (topLC m).terms⟩, ⟨0, []⟩⟩

def modelRows (m : ℕ) : List Row := (List.range m).map boolRow ++ [topRow m]

def modelOutputs : List LC := (List.range 32).map fun i => LC.var (.wit i)

/-- The spec at width `n`: the input is below `2ⁿ` and the outputs are its low 32 bits,
little-endian. -/
def SpecAt (n : ℕ) (ins outs : List F) : Prop :=
  (ins.getD 0 0).val < 2 ^ n ∧ outs = (List.range 32).map (bitOf (ins.getD 0 0))

theorem eval_topLC (m : ℕ) (σ : TVar → F) :
    (topLC m).eval σ = σ (.plug 0) - ∑ i ∈ Finset.range m, ((2 ^ i : ℕ) : F) * σ (.wit i) := by
  simp only [topLC, LC.eval, List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
    Xark.Templates.Add32.sum_map_range, neg_mul, Finset.sum_neg_distrib]
  ring

theorem sat_iff (m : ℕ) (σ : TVar → F) : Xark.R1cs.Sat (modelRows m) σ ↔
    (∀ i < m, σ (.wit i) * σ (.wit i) = σ (.wit i)) ∧
      (topLC m).eval σ * ((topLC m).eval σ - ((2 ^ m : ℕ) : F)) = 0 := by
  have hB : (⟨-((2 ^ m : ℕ) : F), (topLC m).terms⟩ : LC).eval σ =
      (topLC m).eval σ - ((2 ^ m : ℕ) : F) := by
    simp only [LC.eval, topLC]; ring
  simp only [Xark.R1cs.Sat, modelRows, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa [Row.Sat, boolRow] using h _ (Or.inl ⟨i, hi, rfl⟩)
    · have := h _ (Or.inr rfl)
      simp only [Row.Sat, topRow, hB] at this
      simpa [LC.eval] using this
  · rintro ⟨hb, hl⟩ row (⟨i, hi, rfl⟩ | rfl)
    · simpa [Row.Sat, boolRow] using hb i hi
    · simp only [Row.Sat, topRow, hB]
      simpa [LC.eval] using hl

/-! ### Soundness at every width `m + 1 ≤ 253`, `m ≥ 32` -/

/-- **Soundness of the model.** Every assignment satisfying the rows of width
`m + 1 ≤ 253` has its input below `2^(m+1)`, and outputs its low 32 bits. -/
theorem model_sound (m : ℕ) (hm : m + 1 ≤ 253) (h32 : 32 ≤ m) (σ : TVar → F)
    (h : Xark.R1cs.Sat (modelRows m) σ) :
    (σ (.plug 0)).val < 2 ^ (m + 1) ∧
      modelOutputs.map (·.eval σ) = (List.range 32).map (bitOf (σ (.plug 0))) := by
  obtain ⟨hb, ht⟩ := (sat_iff m σ).mp h
  have hw : ∀ i < m, IsBit (σ (.wit i)) := fun i hi => isBit_of_mul_self (hb i hi)
  -- The top carry is `2ᵐ · c` for a bit `c`.
  obtain ⟨c, hc, htop⟩ : ∃ c : F, IsBit c ∧ (topLC m).eval σ = ((2 ^ m : ℕ) : F) * c := by
    rcases mul_eq_zero.mp ht with h0 | h1
    · exact ⟨0, Or.inl rfl, by rw [h0, mul_zero]⟩
    · exact ⟨1, Or.inr rfl, by rw [mul_one]; linear_combination h1⟩
  let v : ℕ → ℕ := fun i => if i < m then (σ (.wit i)).val else c.val
  have hv : ∀ i < m + 1, v i ≤ 1 := fun i hi => by
    by_cases h' : i < m
    · simpa [v, h'] using isBit_val (hw i h')
    · simpa [v, h'] using isBit_val hc
  have hW := word_lt v (m + 1) hv
  have hcast : ((∑ i ∈ Finset.range (m + 1), 2 ^ i * v i : ℕ) : F) = σ (.plug 0) := by
    rw [Finset.sum_range_succ]
    push_cast
    have hs : ∑ i ∈ Finset.range m, (2 : F) ^ i * ((v i : ℕ) : F) =
        ∑ i ∈ Finset.range m, ((2 ^ i : ℕ) : F) * σ (.wit i) :=
      Finset.sum_congr rfl fun i hi => by
        simp [v, Finset.mem_range.mp hi]
    have htop' := htop
    rw [eval_topLC] at htop'
    simp only [v, lt_irrefl, if_false, ZMod.natCast_val, ZMod.cast_id', id] at hs ⊢
    rw [hs]
    push_cast at htop' ⊢
    linear_combination -htop'
  have hx : (σ (.plug 0)).val = ∑ i ∈ Finset.range (m + 1), 2 ^ i * v i := by
    rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hW (two_pow_lt_r' hm))]
  refine ⟨hx ▸ hW, ?_⟩
  simp only [modelOutputs, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [Function.comp_apply, LC.eval_var]
  rw [bitOf, hx]
  exact bit_eq_testBit (hw i (by omega))
    (by simpa [v, show i < m by omega] using testBit_word v (m + 1) hv i (by omega))

/-! ### Any exported width -/

/-- **Soundness at any width.** A template whose input, outputs and rows are the
model's at `m + 1 ≤ 253`, `m ≥ 32`, accepts only inputs below `2^(m+1)`, and outputs
their low 32 bits. -/
theorem soundness_of (t : Template) (m : ℕ) (hm : m + 1 ≤ 253) (h32 : 32 ≤ m)
    (hi : t.inputs = [LC.var (.plug 0)]) (ho : t.outputs = modelOutputs)
    (hr : t.rows = modelRows m) (σ : TVar → F) (h : t.Sat σ) :
    SpecAt (m + 1) (t.ins σ) (t.outs σ) := by
  rw [Template.Sat, hr] at h
  obtain ⟨hlt, hout⟩ := model_sound m hm h32 σ h
  refine ⟨by simpa [Template.ins, hi] using hlt, ?_⟩
  simpa [Template.outs, Template.ins, ho, hi] using hout

/-- What `SpecAt` outputs are bits: a producer of bits for the calls it feeds
(`lean-export --coverage`, "assumptions discharged by producers"). -/
theorem spec_isBit {n : ℕ} {ins outs : List F} (h : SpecAt n ins outs) : ∀ v ∈ outs, IsBit v := by
  rw [h.2]
  intro v hv
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  rw [bitOf]; split
  · exact Or.inr rfl
  · exact Or.inl rfl

end Xark.Reduce

namespace Xark.Templates.Reduce33

open Xark.Template Xark.R1cs Xark.Reduce

/-- The spec at width 33. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 33 ins outs

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs := by
  decide +kernel

theorem rows_eq : template.rows = modelRows 32 := by
  decide +kernel

/-- **Soundness.** Any assignment satisfying the exported rows has `sum < 2^33` and
outputs exactly the low 32 bits of `sum`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 32 (by norm_num) (by norm_num) inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.Reduce33

namespace Xark.Templates.Reduce34

open Xark.Template Xark.R1cs Xark.Reduce

/-- The spec at width 34. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 34 ins outs

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs := by
  decide +kernel

theorem rows_eq : template.rows = modelRows 33 := by
  decide +kernel

/-- **Soundness.** Any assignment satisfying the exported rows has `sum < 2^34` and
outputs exactly the low 32 bits of `sum`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 33 (by norm_num) (by norm_num) inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.Reduce34

namespace Xark.Templates.Reduce35

open Xark.Template Xark.R1cs Xark.Reduce

/-- The spec at width 35. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 35 ins outs

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs := by
  decide +kernel

theorem rows_eq : template.rows = modelRows 34 := by
  decide +kernel

/-- **Soundness.** Any assignment satisfying the exported rows has `sum < 2^35` and
outputs exactly the low 32 bits of `sum`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 34 (by norm_num) (by norm_num) inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.Reduce35

namespace Xark.Templates.Reduce36

open Xark.Template Xark.R1cs Xark.Reduce

/-- The spec at width 36. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 36 ins outs

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs := by
  decide +kernel

theorem rows_eq : template.rows = modelRows 35 := by
  decide +kernel

/-- **Soundness.** Any assignment satisfying the exported rows has `sum < 2^36` and
outputs exactly the low 32 bits of `sum`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 35 (by norm_num) (by norm_num) inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.Reduce36
