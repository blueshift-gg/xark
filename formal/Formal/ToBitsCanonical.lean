/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.ToBitsCanonical
import Formal.ToBits
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false

/-!
# `Field::to_bits_canonical`, proven over its exported rows

`Formal/Templates/ToBitsCanonical.lean` (`cargo xtask lean-export to_bits_canonical`) is
the R1CS the frontend emits for one `Field::to_bits_canonical` on a fresh variable `x`:
all 254 bits of `x`'s representative in `[0, r)`, where `to_bits` stops at 253 (bug
checklist 3, 9: 254 bits can spell `x + r`). Bits `1..253` are hinted variables, bit `0`
is what they leave of `x` (`ToBits.lowLC 253`), and the bits are compared with those of
`c = r − 1` from the top (bellman `into_bits_le_strict`; ACL2 `bits-lt-prime` @ 95d4195):
`all` is the AND of the bits at `c`'s one-bits so far. At a one-bit the bit gets
`b · b = b` and `all` becomes `all · b` (a product row, except at the top one-bit, where
`all` is `b`); at a zero-bit the one row `(1 − all − b) · b = 0` makes `b` a bit, and `0`
where `all = 1`, an equal prefix. 254 + 99 rows.

* `soundness`: with no input assumption, every satisfying assignment outputs exactly the
  254 bits of `x.val`, the canonical representative: the rows force `Σ 2ⁱ·bᵢ ≤ r − 1`, so
  the sum, which is `x` mod `r`, is `x.val`.

The proof is about a model `go` of the compare rows for any `c` with its top bit set
(`rows_eq`, by `decide +kernel`); the invariant at each position is `all = 1` and the
bits above equal `c`'s, or `all = 0` and they spell less.
-/

namespace Xark.Templates.ToBitsCanonical

open Xark.Template Xark.R1cs
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_testBit bit_eq_testBit)
open Xark.Templates.ToBits (lowLC eval_lowLC)

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- The largest canonical value. -/
abbrev c : ℕ := r - 1

/-! ### The rows -/

/-- Bit `i`: `wit (i − 1)` for `i ≥ 1`; bit `0` is what the others leave of `x`. -/
def bitLC (i : ℕ) : LC := if i = 0 then lowLC 253 else LC.var (.wit (i - 1))

def boolRow (i : ℕ) : Row := ⟨bitLC i, bitLC i, bitLC i⟩

/-- `all · b = o`. -/
def prodRow (a i o : ℕ) : Row := ⟨LC.var (.wit a), bitLC i, LC.var (.wit o)⟩

/-- `(1 − all − b) · b = 0`. -/
def condRow (a i : ℕ) : Row :=
  ⟨⟨1, (bitLC i).terms.map (fun t => (-t.1, t.2)) ++ [(-1, .wit a)]⟩, bitLC i, ⟨0, []⟩⟩

/-- The rows and product hints for positions `m − 1, …, 0`, from the top: `k` is the
next variable the frontend allocates (each position allocates one for the product its
row folds in, and a one-bit's AND one more), `all` the variable holding the AND so far,
`none` while it is still the constant `1`. -/
def go : ℕ → ℕ → Option ℕ → List Row × List Hint
  | 0, _, _ => ([], [])
  | m + 1, k, all =>
    if c.testBit m then
      match all with
      | none => ((boolRow m) :: (go m (k + 1) (some (m - 1))).1, (go m (k + 1) (some (m - 1))).2)
      | some a =>
        (boolRow m :: prodRow a m (k + 1) :: (go m (k + 2) (some (k + 1))).1,
          .product (k + 1) (LC.var (.wit a)) (bitLC m) :: (go m (k + 2) (some (k + 1))).2)
    else (condRow (all.getD 0) m :: (go m (k + 1) all).1, (go m (k + 1) all).2)

def modelRows : List Row := (go 254 253 none).1

/-- The outputs: bit `0`, then the hinted bits `1..253`. -/
def modelOutputs : List LC := ToBits.modelOutputs 253

/-! ### The exported template is the model -/

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs := by
  decide +kernel

theorem rows_eq : template.rows = modelRows := by
  decide +kernel

/-! ### The invariant -/

/-- Bit `i`'s value. -/
def β (σ : TVar → F) (i : ℕ) : F := (bitLC i).eval σ

/-- The value of `all`. -/
def allVal (σ : TVar → F) : Option ℕ → F
  | none => 1
  | some a => σ (.wit a)

@[simp] theorem allVal_none (σ : TVar → F) : allVal σ none = 1 := rfl
@[simp] theorem allVal_some (σ : TVar → F) (a : ℕ) : allVal σ (some a) = σ (.wit a) := rfl

theorem go_top {m k : ℕ} (h : c.testBit m = true) : go (m + 1) k none =
    (boolRow m :: (go m (k + 1) (some (m - 1))).1, (go m (k + 1) (some (m - 1))).2) := by
  simp only [go, h, if_true]

theorem go_one {m k a : ℕ} (h : c.testBit m = true) : go (m + 1) k (some a) =
    (boolRow m :: prodRow a m (k + 1) :: (go m (k + 2) (some (k + 1))).1,
      .product (k + 1) (LC.var (.wit a)) (bitLC m) :: (go m (k + 2) (some (k + 1))).2) := by
  simp only [go, h, if_true]

theorem go_zero {m k a : ℕ} (h : c.testBit m = false) : go (m + 1) k (some a) =
    (condRow a m :: (go m (k + 1) (some a)).1, (go m (k + 1) (some a)).2) := by
  simp only [go, h, Bool.false_eq_true, if_false, Option.getD_some]

/-- The number the bits `m..253` spell. -/
def hb (σ : TVar → F) (m : ℕ) : ℕ := ∑ j ∈ Finset.range (254 - m), 2 ^ j * (β σ (m + j)).val

/-- The number `c`'s bits `m..253` spell. -/
def hc (m : ℕ) : ℕ := c / 2 ^ m

/-- After the positions `m..253`: `all = 1` and those bits are `c`'s, or `all = 0` and
they spell less. -/
def Inv (σ : TVar → F) (m : ℕ) (all : Option ℕ) : Prop :=
  (allVal σ all = 1 ∧ hb σ m = hc m) ∨ (allVal σ all = 0 ∧ hb σ m < hc m)

theorem hb_succ (σ : TVar → F) {m : ℕ} (hm : m < 254) :
    hb σ m = (β σ m).val + 2 * hb σ (m + 1) := by
  unfold hb
  rw [show 254 - m = 254 - (m + 1) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.add_zero, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show m + (j + 1) = m + 1 + j by omega]
  ring

theorem hc_succ (m : ℕ) : hc m = (if c.testBit m then 1 else 0) + 2 * hc (m + 1) := by
  unfold hc
  have h2 : c / 2 ^ (m + 1) = c / 2 ^ m / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [h2, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_add_div (c / 2 ^ m) 2
  have hlt := Nat.mod_lt (c / 2 ^ m) (show 2 > 0 by norm_num)
  split <;> rename_i h <;> simp at h <;> omega

theorem hb_top (σ : TVar → F) : hb σ 254 = 0 := by simp [hb]

theorem hc_top : hc 254 = 0 := by
  unfold hc; rw [Nat.div_eq_of_lt]; unfold c; rw [r]; norm_num

theorem c_top : c.testBit 253 = true := by
  unfold c; rw [r]; decide

theorem isBit_of_sq_zero {x : F} (h : x * x = 0) : x = 0 := mul_self_eq_zero.mp h

theorem bitLC_const (i : ℕ) : (bitLC i).const = 0 := by
  unfold bitLC; split <;> rfl

theorem eval_condRow_a (σ : TVar → F) (a i : ℕ) :
    (condRow a i).a.eval σ = 1 - σ (.wit a) - β σ i := by
  have hb : β σ i = ((bitLC i).terms.map fun t => t.1 * σ t.2).sum := by
    rw [β, LC.eval, bitLC_const, zero_add]
  simp only [condRow, LC.eval, List.map_append, List.map_map, Function.comp_def,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hb]
  have hneg : ((bitLC i).terms.map fun t => -t.1 * σ t.2).sum =
      -((bitLC i).terms.map fun t => t.1 * σ t.2).sum := by
    rw [List.sum_neg, List.map_map]
    exact congrArg _ (List.map_congr_left fun t _ => by simp [neg_mul])
  rw [hneg]
  ring

/-- One position, from the invariant above it: a one-bit with `all` a variable. -/
theorem step_one (σ : TVar → F) {m a o : ℕ} (hm : m < 254) (hcm : c.testBit m = true)
    (hi : Inv σ (m + 1) (some a)) (hbool : β σ m * β σ m = β σ m)
    (hprod : σ (.wit a) * β σ m = σ (.wit o)) : IsBit (β σ m) ∧ Inv σ m (some o) := by
  have hbit := isBit_of_mul_self hbool
  refine ⟨hbit, ?_⟩
  have hB := hb_succ σ hm
  have hC := hc_succ m
  rw [hcm, if_pos rfl] at hC
  simp only [Inv, allVal_some] at hi ⊢
  rcases hi with ⟨ha, he⟩ | ⟨ha, hl⟩
  · rw [ha, one_mul] at hprod
    rcases hbit with h0 | h1
    · right; refine ⟨by rw [← hprod, h0], ?_⟩; rw [hB, h0, ZMod.val_zero]; omega
    · left; refine ⟨by rw [← hprod, h1], ?_⟩; rw [hB, h1, ZMod.val_one]; omega
  · rw [ha, zero_mul] at hprod
    right; refine ⟨hprod.symm, ?_⟩
    have := isBit_val hbit; omega

/-- A zero-bit: `all` stays. -/
theorem step_zero (σ : TVar → F) {m a : ℕ} (hm : m < 254) (hcm : c.testBit m = false)
    (hi : Inv σ (m + 1) (some a)) (hrow : (1 - σ (.wit a) - β σ m) * β σ m = 0) :
    IsBit (β σ m) ∧ Inv σ m (some a) := by
  have hB := hb_succ σ hm
  have hC := hc_succ m
  rw [hcm] at hC
  simp only [Bool.false_eq_true, if_false, zero_add] at hC
  simp only [Inv, allVal_some] at hi ⊢
  rcases hi with ⟨ha, he⟩ | ⟨ha, hl⟩
  · rw [ha, sub_self, zero_sub, neg_mul] at hrow
    have h0 := isBit_of_sq_zero (neg_eq_zero.mp hrow)
    refine ⟨Or.inl h0, Or.inl ⟨ha, ?_⟩⟩
    rw [hB, h0, ZMod.val_zero]; omega
  · rw [ha, sub_zero] at hrow
    have hbit : IsBit (β σ m) := by
      rcases mul_eq_zero.mp hrow with h | h
      · exact Or.inr (by linear_combination -h)
      · exact Or.inl h
    refine ⟨hbit, Or.inr ⟨ha, ?_⟩⟩
    have := isBit_val hbit; omega

/-- The top one-bit: `all` becomes that bit. -/
theorem step_top (σ : TVar → F) (hbool : β σ 253 * β σ 253 = β σ 253) :
    IsBit (β σ 253) ∧ Inv σ 253 (some 252) := by
  have hbit := isBit_of_mul_self hbool
  refine ⟨hbit, ?_⟩
  have hB := hb_succ σ (m := 253) (by norm_num)
  have hC := hc_succ 253
  rw [c_top, if_pos rfl, hc_top] at hC
  rw [hb_top] at hB
  have hw : σ (.wit 252) = β σ 253 := by simp [β, bitLC]
  simp only [Inv, allVal_some]
  rw [hw]
  rcases hbit with h0 | h1
  · right; rw [hB, h0, ZMod.val_zero]; exact ⟨rfl, by omega⟩
  · left; rw [hB, h1, ZMod.val_one]; exact ⟨rfl, by omega⟩

/-! ### Soundness -/

theorem go_sound (σ : TVar → F) : ∀ m k all, m ≤ 254 → (all = none → m = 254) →
    Xark.R1cs.Sat (go m k all).1 σ → Inv σ m all →
    (∀ i < m, IsBit (β σ i)) ∧ hb σ 0 ≤ hc 0 := by
  intro m
  induction m with
  | zero =>
    intro k all _ _ _ hi
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    rcases hi with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  | succ m ih =>
    intro k all hm hnone hs hi
    have extend : ∀ i, IsBit (β σ m) → (∀ j < m, IsBit (β σ j)) → i < m + 1 →
        IsBit (β σ i) := fun i hbit hbits hi => by
      by_cases h : i < m
      · exact hbits i h
      · rw [show i = m by omega]; exact hbit
    by_cases hcm : c.testBit m = true
    · cases all with
      | none =>
        have hm' : m = 253 := by have := hnone rfl; omega
        rw [go_top hcm] at hs
        have h := hs _ List.mem_cons_self
        rw [hm'] at h
        obtain ⟨hbit, hi'⟩ := step_top σ (by simpa [Row.Sat, boolRow, β] using h)
        rw [hm'] at ih hs
        obtain ⟨hbits, hle⟩ := ih (k + 1) (some 252) (by omega) (by simp)
          (fun r hr => hs r (List.mem_cons_of_mem _ hr)) hi'
        exact ⟨fun i hi => extend i (hm' ▸ hbit) (hm' ▸ hbits) hi, hle⟩
      | some a =>
        rw [go_one hcm] at hs
        have hb := hs _ List.mem_cons_self
        have hp := hs _ (List.mem_cons_of_mem _ List.mem_cons_self)
        obtain ⟨hbit, hi'⟩ := step_one σ (o := k + 1) (by omega) hcm hi
          (by simpa [Row.Sat, boolRow, β] using hb) (by simpa [Row.Sat, prodRow, β] using hp)
        obtain ⟨hbits, hle⟩ := ih (k + 2) (some (k + 1)) (by omega) (by simp)
          (fun r hr => hs r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) hi'
        exact ⟨fun i hi => extend i hbit hbits hi, hle⟩
    · have hcm : c.testBit m = false := by simpa using hcm
      cases all with
      | none =>
        have hm' : m = 253 := by have := hnone rfl; omega
        rw [hm', c_top] at hcm; exact absurd hcm (by decide)
      | some a =>
        rw [go_zero hcm] at hs
        have h := hs _ List.mem_cons_self
        obtain ⟨hbit, hi'⟩ := step_zero σ (by omega) hcm hi (by
          have h : (condRow a m).a.eval σ * (condRow a m).b.eval σ = (condRow a m).c.eval σ := h
          rw [eval_condRow_a] at h
          simpa [condRow, β, LC.eval] using h)
        obtain ⟨hbits, hle⟩ := ih (k + 1) (some a) (by omega) (by simp)
          (fun r hr => hs r (List.mem_cons_of_mem _ hr)) hi'
        exact ⟨fun i hi => extend i hbit hbits hi, hle⟩

theorem inv_top (σ : TVar → F) : Inv σ 254 none := Or.inl ⟨rfl, by rw [hb_top, hc_top]⟩

/-- The bits spell `x` in the field. -/
theorem sum_eq (σ : TVar → F) :
    ∑ i ∈ Finset.range 254, (2 : F) ^ i * β σ i = σ (.plug 0) := by
  rw [Finset.sum_range_succ']
  have h0 : β σ 0 = (lowLC 253).eval σ := by simp [β, bitLC]
  have hs : ∀ i ∈ Finset.range 253, (2 : F) ^ (i + 1) * β σ (i + 1) =
      ((2 ^ (i + 1) : ℕ) : F) * σ (.wit i) := fun i _ => by simp [β, bitLC]
  rw [Finset.sum_congr rfl hs, pow_zero, one_mul, h0, eval_lowLC]
  ring

theorem hb_cast (σ : TVar → F) :
    ((hb σ 0 : ℕ) : F) = ∑ i ∈ Finset.range 254, (2 : F) ^ i * β σ i := by
  rw [hb, Nat.sub_zero, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zero_add]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id]

/-- The outputs are the bits. -/
theorem outs_eq (σ : TVar → F) :
    modelOutputs.map (·.eval σ) = (List.range 254).map (β σ) := by
  rw [List.range_succ_eq_map]
  simp only [modelOutputs, ToBits.modelOutputs, List.map_cons, List.map_map]
  refine congrArg₂ _ (by simp [β, bitLC]) (List.map_congr_left fun i _ => ?_)
  simp [β, bitLC]

/-- **Soundness of the model.** Every assignment satisfying the rows outputs the 254
bits of `x`'s canonical representative. -/
theorem model_sound (σ : TVar → F) (h : Xark.R1cs.Sat modelRows σ) :
    modelOutputs.map (·.eval σ) = (List.range 254).map (bitOf (σ (.plug 0))) := by
  obtain ⟨hbits, hle⟩ := go_sound σ 254 253 none le_rfl (fun _ => rfl) h (inv_top σ)
  have hcr : hc 0 < r := by unfold hc c; rw [pow_zero, Nat.div_one]; unfold r; norm_num
  have hx : (σ (.plug 0)).val = hb σ 0 := by
    rw [← sum_eq σ, ← hb_cast σ, ZMod.val_natCast_of_lt (by omega)]
  have hv : ∀ i < 254, (β σ i).val ≤ 1 := fun i hi => isBit_val (hbits i hi)
  rw [outs_eq]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [bitOf, hx]
  refine bit_eq_testBit (hbits i hi) ?_
  have := Add32.testBit_word (fun j => (β σ j).val) 254 hv i hi
  simpa [hb] using this

/-! ### The template -/

/-- The spec: the outputs are the 254 bits of the input's canonical representative,
little-endian. -/
def Spec (ins outs : List F) : Prop := outs = (List.range 254).map (bitOf (ins.getD 0 0))

/-- What `Spec` outputs are bits: a producer of bits for the calls it feeds, whatever
its input (`lean-export --coverage`, "assumptions discharged by producers"). -/
theorem spec_isBit {ins outs : List F} (h : Spec ins outs) : ∀ v ∈ outs, IsBit v := by
  rw [h]
  intro v hv
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  rw [bitOf]; split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem ins_eq (σ : TVar → F) : template.ins σ = [σ (.plug 0)] := by
  simp [Template.ins, inputs_eq]

/-- **Soundness.** With no input assumption, any assignment satisfying the exported rows
outputs exactly the 254 bits of `x.val`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [Template.Sat, rows_eq] at h
  rw [Spec, ins_eq]
  simpa [Template.outs, outputs_eq] using model_sound σ h

end Xark.Templates.ToBitsCanonical
