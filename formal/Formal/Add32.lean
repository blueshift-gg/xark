/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.Add32
import Formal.GrumpkinGroup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

set_option linter.style.header false

/-!
# `xark_bits::add32`, proven over its exported rows

`Formal/Templates/Add32.lean` is the R1CS the frontend emits for one call of
`xark_bits::add32` (`cargo xtask lean-export add32`): 33 booleanity rows `wᵢ · wᵢ = wᵢ`
and the recomposition `(Σᵢ<33 2ⁱ·wᵢ − Σᵢ<32 2ⁱ·aᵢ − Σᵢ<32 2ⁱ·bᵢ) · 1 = 0`, with a bit
hint per `wᵢ`. On input words of bits it is **sound** (`soundness`): every assignment
satisfying the rows outputs exactly the 32 bits of `(a + b) mod 2³²`, so the result has no
prover freedom.

The input assumption, that both words are bits, is the caller's to enforce (`to_bits`
outputs, or an earlier word gadget's result, which `soundness` shows is bits).
-/

namespace Xark.Templates.Add32

open Xark.Template Xark.R1cs

/-- `Σᵢ<n 2ⁱ · xᵢ` over the naturals, of the canonical values of `x`. -/
def word (x : ℕ → F) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 2 ^ i * (x i).val

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The input assumption: both words are bits. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The spec: the result is the 32 bits of `(a + b) mod 2³²`, little-endian, where `a`
and `b` are the two input words. -/
def Spec (ins outs : List F) : Prop :=
  let a := word (fun i => ins.getD i 0) 32
  let b := word (fun i => ins.getD (32 + i) 0) 32
  outs = (List.range 32).map fun i => if ((a + b) % 2 ^ 32).testBit i then 1 else 0

/-! ### The exported template, read structurally -/

/-- Input `j` contributes `2^(j mod 32)` to its word. -/
def inSum : LC := ⟨0, (List.range 64).map fun j => (((2 ^ (j % 32) : ℕ) : F), .plug j)⟩

def boolRow (i : ℕ) : Row := ⟨⟨0, [(1, .wit i)]⟩, ⟨0, [(1, .wit i)]⟩, ⟨0, [(1, .wit i)]⟩⟩

def recompRow : Row :=
  ⟨⟨0, (List.range 64).map (fun j => (-((2 ^ (j % 32) : ℕ) : F), .plug j)) ++
      (List.range 33).map fun i => (((2 ^ i : ℕ) : F), .wit i)⟩, ⟨1, []⟩, ⟨0, []⟩⟩

theorem inputs_eq :
    template.inputs = (List.range 64).map fun j => ⟨0, [(1, .plug j)]⟩ := by
  decide +kernel

theorem outputs_eq :
    template.outputs = (List.range 32).map fun i => ⟨0, [(1, .wit i)]⟩ := by
  decide +kernel

theorem rows_eq : template.rows = (List.range 33).map boolRow ++ [recompRow] := by
  decide +kernel

/-! ### Binary words over the naturals -/

theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- A word of bits is below `2ⁿ`. -/
theorem word_lt (v : ℕ → ℕ) (n : ℕ) (hv : ∀ i < n, v i ≤ 1) :
    ∑ i ∈ Finset.range n, 2 ^ i * v i < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := ih fun i hi => hv i (by omega)
    have : 2 ^ n * v n ≤ 2 ^ n := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hv n (by omega)) with h | h <;> simp [h]
    omega

/-- The bits of a word of bits are its bits. -/
theorem testBit_word (v : ℕ → ℕ) (n : ℕ) (hv : ∀ i < n, v i ≤ 1) (i : ℕ) (hi : i < n) :
    (∑ j ∈ Finset.range n, 2 ^ j * v j).testBit i = true ↔ v i = 1 := by
  induction n generalizing v i with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have e : ∑ j ∈ Finset.range n, 2 ^ (j + 1) * v (j + 1) =
        2 * ∑ j ∈ Finset.range n, 2 ^ j * v (j + 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have h0 := hv 0 (by omega)
    cases i with
    | zero =>
      rw [Nat.testBit_zero, decide_eq_true_iff]
      omega
    | succ i =>
      rw [Nat.testBit_succ, show (2 * ∑ j ∈ Finset.range n, 2 ^ j * v (j + 1) + 2 ^ 0 * v 0) / 2
          = ∑ j ∈ Finset.range n, 2 ^ j * v (j + 1) by omega]
      exact ih (fun j => v (j + 1)) (fun j hj => hv (j + 1) (by omega)) i (by omega)

/-- A number below `2ⁿ` is the word of its bits. -/
theorem word_testBit (m n : ℕ) (h : m < 2 ^ n) :
    ∑ i ∈ Finset.range n, 2 ^ i * (if m.testBit i then 1 else 0) = m := by
  induction n generalizing m with
  | zero => simp at h; simp [h]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have e : ∑ i ∈ Finset.range n, 2 ^ (i + 1) * (if m.testBit (i + 1) then 1 else 0) =
        2 * ∑ i ∈ Finset.range n, 2 ^ i * (if (m / 2).testBit i then 1 else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Nat.testBit_succ]; ring
    have hm : m / 2 < 2 ^ n := by rw [pow_succ] at h; omega
    rw [e, ih (m / 2) hm, Nat.testBit_zero]
    by_cases hb : m % 2 = 1 <;> simp [hb] <;> omega

/-! ### Field ↔ naturals -/

instance : Fact (Nat.Prime r) := bn254_r_prime

theorem isBit_val {x : F} (h : IsBit x) : x.val ≤ 1 := by
  rcases h with rfl | rfl <;> simp [ZMod.val_one]

/-- A field sum `Σ cᵢ · xᵢ` with natural coefficients is the cast of the natural sum
of canonical values. -/
theorem cast_sum (c : ℕ → ℕ) (x : ℕ → F) (s : Finset ℕ) :
    ∑ i ∈ s, ((c i : ℕ) : F) * x i = ((∑ i ∈ s, c i * (x i).val : ℕ) : F) := by
  push_cast; simp

/-- Two naturals below `r` equal as field elements are equal. -/
theorem nat_eq_of_cast {a b : ℕ} (ha : a < r) (hb : b < r) (h : (a : F) = b) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this

theorem two_pow_34_lt_r : 2 ^ 34 < r := by unfold r; norm_num

/-! ### The rows' meaning -/

theorem eval_inSum (σ : TVar → F) :
    inSum.eval σ = ∑ j ∈ Finset.range 64, ((2 ^ (j % 32) : ℕ) : F) * σ (.plug j) := by
  simp [inSum, LC.eval, List.map_map, Function.comp_def, sum_map_range]

/-- The rows hold iff every `wᵢ` is boolean and `Σ 2ⁱ·wᵢ` is the inputs' sum. -/
theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    (∀ i < 33, σ (.wit i) * σ (.wit i) = σ (.wit i)) ∧
      ∑ i ∈ Finset.range 33, ((2 ^ i : ℕ) : F) * σ (.wit i) = inSum.eval σ := by
  rw [eval_inSum]
  simp only [Template.Sat, rows_eq, Xark.R1cs.Sat, List.mem_append, List.mem_map,
    List.mem_range, List.mem_singleton]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa [Row.Sat, boolRow, LC.eval] using h _ (Or.inl ⟨i, hi, rfl⟩)
    · have := h _ (Or.inr rfl)
      simp only [Row.Sat, recompRow, LC.eval, List.map_append, List.map_map, List.sum_append,
        Function.comp_def, sum_map_range, List.map_nil, List.sum_nil, add_zero, zero_add,
        mul_one] at this
      simp only [neg_mul, Finset.sum_neg_distrib] at this
      linear_combination this
  · rintro ⟨hb, hs⟩ row (⟨i, hi, rfl⟩ | rfl)
    · simpa [Row.Sat, boolRow, LC.eval] using hb i hi
    · simp only [Row.Sat, recompRow, LC.eval, List.map_append, List.map_map, List.sum_append,
        Function.comp_def, sum_map_range, List.map_nil, List.sum_nil, add_zero, zero_add,
        mul_one, neg_mul, Finset.sum_neg_distrib]
      linear_combination hs

theorem ins_eq (σ : TVar → F) :
    template.ins σ = (List.range 64).map fun j => σ (.plug j) := by
  simp [Template.ins, inputs_eq, List.map_map, Function.comp_def, LC.eval]

theorem outs_eq (σ : TVar → F) :
    template.outs σ = (List.range 32).map fun i => σ (.wit i) := by
  simp [Template.outs, outputs_eq, List.map_map, Function.comp_def, LC.eval]

theorem isBit_of_mul_self {x : F} (h : x * x = x) : IsBit x := by
  have : x * (x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

/-- On bits, the inputs' sum is the cast of `a + b`, the two words as naturals. -/
theorem eval_inSum_word (x : ℕ → F) (σ : TVar → F) (hσ : ∀ j, σ (.plug j) = x j) :
    inSum.eval σ = ((word x 32 + word (fun j => x (32 + j)) 32 : ℕ) : F) := by
  have h1 : ∑ j ∈ Finset.range 32, 2 ^ (j % 32) * (σ (.plug j)).val = word x 32 :=
    Finset.sum_congr rfl fun j hj => by rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hj), hσ]
  have h2 : ∑ j ∈ Finset.range 32, 2 ^ ((32 + j) % 32) * (σ (.plug (32 + j))).val =
      word (fun j => x (32 + j)) 32 :=
    Finset.sum_congr rfl fun j hj => by
      rw [show (32 + j) % 32 = j by have := Finset.mem_range.mp hj; omega, hσ]
  rw [eval_inSum, show 64 = 32 + 32 from rfl, Finset.sum_range_add]
  simp only [cast_sum]
  rw [h1, h2, Nat.cast_add]

/-- `wᵢ`, a bit, is bit `i` of the word it is part of. -/
theorem bit_eq_testBit {w : F} (hw : IsBit w) {m i : ℕ} (h : m.testBit i = true ↔ w.val = 1) :
    w = if m.testBit i then 1 else 0 := by
  rcases hw with rfl | rfl
  · have : m.testBit i = false := by simpa using h
    simp [this]
  · simp [ZMod.val_one] at h; simp [h]

/-! ### Soundness -/

/-- **Soundness.** On words of bits, any assignment satisfying the exported rows
outputs exactly the bits of `(a + b) mod 2³²`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ))
    (h : template.Sat σ) : Spec (template.ins σ) (template.outs σ) := by
  rw [ins_eq] at ha ⊢
  rw [outs_eq]
  obtain ⟨hb, hs⟩ := (sat_iff σ).mp h
  have hx : ∀ j < 64, IsBit (σ (.plug j)) := fun j hj =>
    ha _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have hw : ∀ i < 33, IsBit (σ (.wit i)) := fun i hi => isBit_of_mul_self (hb i hi)
  let x := fun j => σ (.plug j)
  have hA := word_lt (fun j => (x j).val) 32 fun j hj => isBit_val (hx j (by omega))
  have hB := word_lt (fun j => (x (32 + j)).val) 32 fun j hj => isBit_val (hx _ (by omega))
  have hW := word_lt (fun i => (σ (.wit i)).val) 33 fun i hi => isBit_val (hw i hi)
  have hsum : word (fun i => σ (.wit i)) 33 = word x 32 + word (fun j => x (32 + j)) 32 := by
    refine nat_eq_of_cast (lt_trans hW (by have := two_pow_34_lt_r; omega))
      (by have := two_pow_34_lt_r; simp only [word] at *; omega) ?_
    rw [← eval_inSum_word x σ fun _ => rfl, ← hs, word, ← cast_sum]
  have hget : ∀ k, k < 64 → ((List.range 64).map x).getD k 0 = x k := fun k hk => by
    simp [List.getD_eq_getElem?_getD, hk]
  simp only [Spec]
  rw [show word (fun i => ((List.range 64).map x).getD i 0) 32 = word x 32 from
      Finset.sum_congr rfl fun i hi => by dsimp only; rw [hget i (by simp at hi; omega)],
    show word (fun i => ((List.range 64).map x).getD (32 + i) 0) 32 =
        word (fun j => x (32 + j)) 32 from
      Finset.sum_congr rfl fun i hi => by dsimp only; rw [hget _ (by simp at hi; omega)],
    ← hsum]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]
  exact bit_eq_testBit (hw i (by omega))
    (testBit_word _ 33 (fun j hj => isBit_val (hw j hj)) i (by omega))

/-! ### Calls with constant plugs -/

/-- **Soundness with constant plugs** `c`: a call passing constants for some inputs
(`cargo xtask lean-export --coverage` checks its rows are `template.inst (consts c)`). -/
theorem soundness_consts (c : List (ℕ × F)) (σ : TVar → F)
    (ha : Assumptions ((template.inst (Template.consts c)).ins σ))
    (h : (template.inst (Template.consts c)).Sat σ) :
    Spec ((template.inst (Template.consts c)).ins σ)
      ((template.inst (Template.consts c)).outs σ) :=
  Template.soundness_inst template soundness _ σ ha h

theorem env_consts_plug (c : List (ℕ × F)) (σ : TVar → F) (j : ℕ) :
    (j ∉ c.map Prod.fst ∧ Template.env (Template.consts c) σ (.plug j) = σ (.plug j)) ∨
      Template.env (Template.consts c) σ (.plug j) ∈ c.map Prod.snd := by
  induction c with
  | nil => simp [Template.env, Template.consts]
  | cons p c ih =>
    simp only [Template.consts, Template.env, List.map_cons, List.foldr_cons] at ih ⊢
    by_cases hj : j = p.1
    · subst hj; simp
    · simp only [Function.update, TVar.plug.injEq, hj, dite_false, List.mem_cons,
        false_or]
      rcases ih with h | h
      · exact .inl ⟨h.1, h.2⟩
      · exact .inr (.inr h)

/-- The assumptions of a call with constant plugs `c`: the constants are bits
(`Formal/Templates/Consts/Add32.lean`, per vector) and so are the other inputs. -/
theorem assumptions_consts (c : List (ℕ × F)) (σ : TVar → F)
    (hc : Assumptions (c.map Prod.snd)) (hx : ∀ j ∉ c.map Prod.fst, IsBit (σ (.plug j))) :
    Assumptions ((template.inst (Template.consts c)).ins σ) := by
  rw [Template.ins_inst, ins_eq]
  intro v hv
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
  rcases env_consts_plug c σ j with ⟨hj, h⟩ | h
  · rw [h]; exact hx j hj
  · exact hc _ h

/-- **Its outputs are bits** (on input bits): a producer of bits for the calls it feeds
(`lean-export --coverage`, "assumptions discharged by producer"). -/
theorem outs_isBit (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    ∀ v ∈ template.outs σ, IsBit v := by
  have hs := soundness σ ha h
  rw [Spec] at hs
  rw [hs]
  intro v hv
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- `1 − b` of a bit `b` is a bit: a producer's output negated (`!x` on a bit) is
still one. -/
theorem isBit_one_sub {x : F} (h : IsBit x) : IsBit (1 - x) := by
  rcases h with rfl | rfl
  · exact Or.inr (by ring)
  · exact Or.inl (by ring)

/-- A product of bits is a bit: a row `a · b = v` with `a` and `b` proven bits
pins `v` (`lean-export --coverage`, "booleanity rows"; the other two shapes it
reads are `isBit_of_mul_self` and `ToBits.isBit_of_mul_sub_one`). -/
theorem isBit_mul {x y : F} (hx : IsBit x) (hy : IsBit y) : IsBit (x * y) := by
  rcases hx with rfl | rfl
  · exact Or.inl (zero_mul y)
  · simpa using hy

end Xark.Templates.Add32
