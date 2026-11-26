/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.ToBits
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `range_derived::<W>`, and rows made of it

`range_derived::<W>(v)` witnesses `W - 1` bits `bᵢ` of `v`, pins each by
`bᵢ · bᵢ = bᵢ`, and derives the top bit affinely: `top = v - Σᵢ 2ⁱ bᵢ`, pinned by
`top · (top - 2^(W-1)) = 0`. So `top ∈ {0, 2^(W-1)}` and `v = Σᵢ 2ⁱ bᵢ + top` is
below `2^W`; unlike `range_check_limbs` the last bit is never a variable, which is
the row-count tie at `W + 1` rows.

The frontend allocates two variables per witnessed bit (the second unused), so the
block of a value whose first bit variable is `base` occupies `2W - 1` variables:
the bits are `wit (base + 2i)`, and `wit (base + 2i + 1)` and `wit (base + 2W - 2)`
carry nothing. A `Block` is one call `(v, base, W)`; `rows bs` are the calls of a
list of blocks, one after another.

`sound`: for `1 ≤ W ≤ 253`, every assignment satisfying a block's rows has
`v < 2^W`. `RangeCheckQ` and `RangeCheckR` are 25 such blocks each, and each
exported template is shown to be these rows by `decide +kernel` in its own file.
-/

namespace Xark.Templates.RangeDerived

open Xark.Template Xark.R1cs
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt sum_map_range cast_sum)

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- One range check: the checked combination, its first bit variable, its width. -/
abbrev Block := LC × ℕ × ℕ

/-- The variable holding bit `i` of a block whose first bit variable is `base`. -/
def bitVar (base i : ℕ) : TVar := .wit (base + 2 * i)

/-- `bᵢ · bᵢ = bᵢ`. -/
def boolRow (base i : ℕ) : Row :=
  ⟨LC.var (bitVar base i), LC.var (bitVar base i), LC.var (bitVar base i)⟩

/-- `Σᵢ 2ⁱ·bᵢ` over the block's `W - 1` low bits. -/
def accLC (base W : ℕ) : LC :=
  ⟨0, (List.range (W - 1)).map fun i => (((2 ^ i : ℕ) : F), bitVar base i)⟩

def negTerms (l : List (F × TVar)) : List (F × TVar) := l.map fun t => (-t.1, t.2)

/-- `top = v − Σᵢ 2ⁱ·bᵢ`. -/
def topA (b : Block) : LC := ⟨b.1.const, b.1.terms ++ negTerms (accLC b.2.1 b.2.2).terms⟩

/-- `top − 2^(W−1)`. -/
def topB (b : Block) : LC :=
  ⟨(topA b).const - ((2 ^ (b.2.2 - 1) : ℕ) : F), (topA b).terms⟩

/-- The block's rows: one booleanity row per low bit, then `top · (top − 2^(W−1)) = 0`. -/
def blockRows (b : Block) : List Row :=
  (List.range (b.2.2 - 1)).map (boolRow b.2.1) ++ [⟨topA b, topB b, ⟨0, []⟩⟩]

def rows (bs : List Block) : List Row := bs.flatMap blockRows

/-- The plugs a `range_check_q`-style list of blocks reads. -/
def modelInputs (L : ℕ) : List LC := (List.range L).map fun j => LC.var (.plug j)

theorem eval_var (x : TVar) (σ : TVar → F) : (LC.var x).eval σ = σ x := by
  simp [LC.var, LC.eval]

/-- **Soundness of one block.** A satisfied block's value is below `2^W`. -/
theorem block_sound (b : Block) (hW : b.2.2 ≤ 253) (hW1 : 1 ≤ b.2.2) (σ : TVar → F)
    (h : Xark.R1cs.Sat (blockRows b) σ) : (b.1.eval σ).val < 2 ^ b.2.2 := by
  obtain ⟨v, base, W⟩ := b
  have hW' : W ≤ 253 := hW
  have hW1' : 1 ≤ W := hW1
  have hbits : ∀ i, i < W - 1 → IsBit (σ (bitVar base i)) := by
    intro i hi
    have hmem : boolRow base i ∈ blockRows (v, base, W) :=
      List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hrow := h _ hmem
    refine isBit_of_mul_self ?_
    simpa [Row.Sat, boolRow, eval_var] using hrow
  have hrow : (topA (v, base, W)).eval σ * (topB (v, base, W)).eval σ = 0 := by
    have hmem : (⟨topA (v, base, W), topB (v, base, W), ⟨0, []⟩⟩ : Row) ∈
        blockRows (v, base, W) := List.mem_append_right _ (List.mem_singleton_self _)
    have := h _ hmem
    simpa only [Row.Sat, LC.eval, List.map_nil, List.sum_nil, add_zero] using this
  have hB : (topB (v, base, W)).eval σ =
      (topA (v, base, W)).eval σ - ((2 ^ (W - 1) : ℕ) : F) := by
    simp only [topB, LC.eval]
    ring
  rw [hB] at hrow
  have htop : (topA (v, base, W)).eval σ = 0 ∨
      (topA (v, base, W)).eval σ = ((2 ^ (W - 1) : ℕ) : F) := by
    rcases mul_eq_zero.mp hrow with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linear_combination h')
  let w : ℕ → ℕ := fun i => (σ (bitVar base i)).val
  have hwb : ∀ i < W - 1, w i ≤ 1 := fun i hi => isBit_val (hbits i hi)
  have hWlt := word_lt w (W - 1) hwb
  have hcast : ((∑ i ∈ Finset.range (W - 1), 2 ^ i * w i : ℕ) : F) =
      (accLC base W).eval σ := by
    simp only [accLC, LC.eval, List.map_map, Function.comp_def, sum_map_range]
    push_cast
    simp only [w, bitVar, ZMod.natCast_val, ZMod.cast_id', id]
    ring
  have hlt : ((accLC base W).eval σ).val < 2 ^ (W - 1) := by
    rw [← hcast,
      ZMod.val_natCast_of_lt
        (lt_trans hWlt (Xark.Templates.ToBits.two_pow_lt_r' (by omega)))]
    exact hWlt
  have hneg :
      (List.map (fun t => t.1 * σ t.2) (negTerms (accLC base W).terms)).sum =
        - (List.map (fun t => t.1 * σ t.2) (accLC base W).terms).sum := by
    induction (accLC base W).terms with
    | nil => simp [negTerms]
    | cons t ts ih => simp [negTerms] at ih ⊢; rw [ih]; ring
  have hvLC : v.eval σ = (accLC base W).eval σ + (topA (v, base, W)).eval σ := by
    simp only [topA, negTerms, LC.eval, List.map_append, List.sum_append]
    simp only [negTerms] at hneg
    rw [hneg]
    simp [accLC]
    ring
  have hpow : 2 ^ (W - 1) + 2 ^ (W - 1) = 2 ^ W := by
    have h : W = (W - 1) + 1 := by omega
    calc 2 ^ (W - 1) + 2 ^ (W - 1) = 2 ^ (W - 1) * 2 := by ring
      _ = 2 ^ ((W - 1) + 1) := (pow_succ 2 (W - 1)).symm
      _ = 2 ^ W := by rw [← h]
  rw [hvLC, ZMod.val_add]
  have h2 : ((accLC base W).eval σ).val + ((topA (v, base, W)).eval σ).val < 2 ^ W := by
    rcases htop with h0 | h1
    · rw [h0, ZMod.val_zero, add_zero]
      exact lt_trans hlt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    · rw [h1, ZMod.val_natCast_of_lt (Xark.Templates.ToBits.two_pow_lt_r' (by omega))]
      omega
  rw [Nat.mod_eq_of_lt (lt_trans h2 (Xark.Templates.ToBits.two_pow_lt_r' hW'))]
  exact h2

/-- **Soundness.** Every block of satisfied rows of width `≤ 253` is in range. -/
theorem sound (bs : List Block) (hW : ∀ b ∈ bs, b.2.2 ≤ 253) (hW1 : ∀ b ∈ bs, 1 ≤ b.2.2)
    (σ : TVar → F) (h : Xark.R1cs.Sat (rows bs) σ) :
    ∀ b ∈ bs, (b.1.eval σ).val < 2 ^ b.2.2 := fun b hb =>
  block_sound b (hW b hb) (hW1 b hb) σ fun r hr => h r (List.mem_flatMap.mpr ⟨b, hb, hr⟩)

/-! ### A `range_check_q`-shaped list of blocks: 24 limbs and a top one -/

/-- Block `j < L - 1` checks plug `j` at width `B`; the last block checks plug
`L - 1` at width `Wtop`. Each block occupies `2B - 1` variables, so block `j`
starts at `(2B - 1) * j`. -/
def limbs (L B Wtop : ℕ) : List Block :=
  (List.range (L - 1)).map (fun j => (LC.var (.plug j), (2 * B - 1) * j, B)) ++
    [(LC.var (.plug (L - 1)), (2 * B - 1) * (L - 1), Wtop)]

/-- Every limb below `2^B`, the top one below `2^Wtop`; there are no outputs. -/
def SpecAt (L B Wtop : ℕ) (ins _outs : List F) : Prop :=
  (∀ j < L - 1, (ins.getD j 0).val < 2 ^ B) ∧ (ins.getD (L - 1) 0).val < 2 ^ Wtop

theorem mem_limbs {L B Wtop : ℕ} {b : Block} (h : b ∈ limbs L B Wtop) :
    (∃ j < L - 1, b = (LC.var (.plug j), (2 * B - 1) * j, B)) ∨
      b = (LC.var (.plug (L - 1)), (2 * B - 1) * (L - 1), Wtop) := by
  simp only [limbs, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨j, hj, rfl⟩ | rfl
  · exact Or.inl ⟨j, hj, rfl⟩
  · exact Or.inr rfl

theorem getD_ins (t : Template) {L : ℕ} (hi : t.inputs = modelInputs L) (σ : TVar → F) {j : ℕ}
    (hj : j < L) : (t.ins σ).getD j 0 = σ (.plug j) := by
  simp [Template.ins, hi, modelInputs, List.getD_eq_getElem?_getD, hj]

/-- **Soundness transfer.** A template whose inputs are the model's plugs and whose
rows are `limbs L B Wtop` puts every limb in range, with no input assumption. -/
theorem soundness_of (t : Template) (L B Wtop : ℕ) (hL : 1 ≤ L) (hB1 : 1 ≤ B) (hB : B ≤ 253)
    (hW1 : 1 ≤ Wtop) (hWtop : Wtop ≤ 253) (hi : t.inputs = modelInputs L)
    (hr : t.rows = rows (limbs L B Wtop)) (σ : TVar → F) (h : t.Sat σ) :
    SpecAt L B Wtop (t.ins σ) (t.outs σ) := by
  rw [Template.Sat, hr] at h
  have hs := sound _ (fun b hb => by
      rcases mem_limbs hb with ⟨_, _, rfl⟩ | rfl <;> simp [hB, hWtop]) (fun b hb => by
      rcases mem_limbs hb with ⟨_, _, rfl⟩ | rfl <;> simp [hB1, hW1]) σ h
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [getD_ins t hi σ (by omega)]
    simpa [eval_var] using hs _ (List.mem_append_left _
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  · rw [getD_ins t hi σ (by omega)]
    simpa [eval_var] using hs _ (List.mem_append_right _ (List.mem_singleton_self _))

end Xark.Templates.RangeDerived
