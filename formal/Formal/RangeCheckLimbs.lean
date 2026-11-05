/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Template
import Formal.ToBits

set_option linter.style.header false

/-!
# Hinted-bit range checks: `range_check_limbs`, and the same rows in `unpack`, `unpack8`,
# `scalar_to_bits`

`xark_bignum::range_bits::<B>(v)` emits `B` hinted bits `wᵢ` (bit `i` of `v`) pinned by
`w · w = w`, then the one row `(Σᵢ 2ⁱ·wᵢ − v) · 1 = 0`. The frontend allocates two
variables per bit, the second unused, so bit `i` of a block whose first bit is variable
`base` is `wit (base + 2i)`. A `Block` is one such check `(v, base, B)`; `rows bs` are the
checks of a list of blocks, one after another.

`range_check_limbs::<L, B>` is `L` blocks over its plugs (`limbs L B`); `unpack`, `unpack4`
and `unpack8` contain one over the limbs their `divRem` hints write; `scalar_to_bits` is three
over its plugs, of widths 86, 86 and 84. Each exported template is shown to be these rows by
`decide +kernel` in its own file.

`sound`: for `B ≤ 253`, every assignment satisfying a block's rows has `v < 2^B` and the bit
variables are `v`'s bits.
-/

namespace Xark.Templates.RangeCheckLimbs

open Xark.Template Xark.R1cs
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt testBit_word bit_eq_testBit
  sum_map_range cast_sum)

/-- One range check: the checked variable, its first bit variable, its width. -/
abbrev Block := TVar × ℕ × ℕ

def boolRow (v : ℕ) : Row := ⟨LC.var (.wit v), LC.var (.wit v), LC.var (.wit v)⟩

/-- `Σᵢ 2ⁱ·wᵢ − v`. -/
def recompLC (b : Block) : LC :=
  ⟨0, (-1, b.1) :: (List.range b.2.2).map fun i => (((2 ^ i : ℕ) : F), .wit (b.2.1 + 2 * i))⟩

def blockRows (b : Block) : List Row :=
  (List.range b.2.2).map (fun i => boolRow (b.2.1 + 2 * i)) ++ [⟨recompLC b, ⟨1, []⟩, ⟨0, []⟩⟩]

def rows (bs : List Block) : List Row := bs.flatMap blockRows

/-- `range_check_limbs::<L, B>`'s blocks: limb `j` is plug `j`, its bits from `2B·j`. -/
def limbs (L B : ℕ) : List Block := (List.range L).map fun j => (.plug j, 2 * B * j, B)

def modelInputs (L : ℕ) : List LC := (List.range L).map fun b => LC.var (.plug b)

/-- What a satisfied block says: `v < 2^B` and the bit variables are its bits. -/
def Holds (σ : TVar → F) (b : Block) : Prop :=
  (σ b.1).val < 2 ^ b.2.2 ∧ ∀ i < b.2.2, σ (.wit (b.2.1 + 2 * i)) = bitOf (σ b.1) i

theorem sat_recomp (b : Block) (σ : TVar → F) :
    Row.Sat ⟨recompLC b, ⟨1, []⟩, ⟨0, []⟩⟩ σ ↔
      σ b.1 = ∑ i ∈ Finset.range b.2.2, ((2 ^ i : ℕ) : F) * σ (.wit (b.2.1 + 2 * i)) := by
  simp only [Row.Sat, recompLC, LC.eval, List.map_cons, List.map_map, Function.comp_def,
    List.sum_cons, sum_map_range, List.map_nil, List.sum_nil, add_zero, mul_one]
  constructor <;> intro h <;> linear_combination -h

theorem block_sound (b : Block) (hB : b.2.2 ≤ 253) (σ : TVar → F)
    (h : Xark.R1cs.Sat (blockRows b) σ) : Holds σ b := by
  obtain ⟨v, base, B⟩ := b
  have hw : ∀ i < B, IsBit (σ (.wit (base + 2 * i))) := fun i hi => by
    have := h _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    exact isBit_of_mul_self (by simpa [Row.Sat, boolRow] using this)
  have hr := (sat_recomp (v, base, B) σ).mp
    (h _ (List.mem_append_right _ (List.mem_singleton_self _)))
  let w : ℕ → ℕ := fun i => (σ (.wit (base + 2 * i))).val
  have hwb : ∀ i < B, w i ≤ 1 := fun i hi => isBit_val (hw i hi)
  have hW := word_lt w B hwb
  have hx : (σ v).val = ∑ i ∈ Finset.range B, 2 ^ i * w i := by
    rw [hr, cast_sum (fun i => 2 ^ i),
      ZMod.val_natCast_of_lt (lt_trans hW (ToBits.two_pow_lt_r' hB))]
  refine ⟨hx ▸ hW, fun i hi => ?_⟩
  rw [bitOf, hx]
  exact (bit_eq_testBit (hw i hi) (by simpa [w] using testBit_word w B hwb i hi)).symm ▸ rfl

/-- **Soundness.** Every block of satisfied rows of width `≤ 253` holds. -/
theorem sound (bs : List Block) (hB : ∀ b ∈ bs, b.2.2 ≤ 253) (σ : TVar → F)
    (h : Xark.R1cs.Sat (rows bs) σ) : ∀ b ∈ bs, Holds σ b := fun b hb =>
  block_sound b (hB b hb) σ fun r hr => h r (List.mem_flatMap.mpr ⟨b, hb, hr⟩)

/-! ### `range_check_limbs::<L, B>` -/

/-- Every one of the `L` limbs is below `2^B`; there are no outputs. -/
def SpecAt (L B : ℕ) (ins _outs : List F) : Prop := ∀ j < L, (ins.getD j 0).val < 2 ^ B

theorem mem_limbs {L B : ℕ} {b : Block} (h : b ∈ limbs L B) :
    ∃ j < L, b = (.plug j, 2 * B * j, B) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  exact ⟨j, List.mem_range.mp hj, rfl⟩

theorem getD_ins (t : Template) {L : ℕ} (hi : t.inputs = modelInputs L) (σ : TVar → F) {j : ℕ}
    (hj : j < L) : (t.ins σ).getD j 0 = σ (.plug j) := by
  simp [Template.ins, hi, modelInputs, List.getD_eq_getElem?_getD, hj]

theorem soundness_of (t : Template) (L B : ℕ) (hB : B ≤ 253) (hi : t.inputs = modelInputs L)
    (hr : t.rows = rows (limbs L B)) (σ : TVar → F) (h : t.Sat σ) :
    SpecAt L B (t.ins σ) (t.outs σ) := by
  intro j hj
  rw [Template.Sat, hr] at h
  rw [getD_ins t hi σ hj]
  exact (sound _ (fun b hb => by obtain ⟨_, _, rfl⟩ := mem_limbs hb; exact hB) σ h _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)).1

end Xark.Templates.RangeCheckLimbs
