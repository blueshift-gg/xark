/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.GroupedColumns
import Formal.Templates.GroupedColumnStep
import Formal.GroupedColumns
import Formal.GroupedCarry
import Formal.Shadow
import Formal.Norm
import Formal.Circuit
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_rsa::grouped_columns`, proven over its exported rows

`Formal/Templates/GroupedColumns.lean` is the recorded template of one call on fresh
inputs: 125 plugs (`a`, `b`, `m`, `q`, `rhs` limbs) and 5,546 witnesses. Its 3,435 rows
are

* 1,250 product rows `a i · b k = wit (2(i·25+k))` and `q i · m k = wit (2(i·25+k)+1)`,
  interleaved as the frontend's CSE emitted them;
* 24 inlined `grouped_column_step` instances, 91 rows each: the step template's rows with
  its five plugs bound to the two column combinations and the previous carry;
* the top row `d 48 + k 23 − 2^88 = 0`.

The model below spells those rows out (`modelRows`) and `rows_eq` (`decide +kernel`)
checks the template against it. The exported rows hold the frontend's normalized
combinations (sorted by variable, merged), while `LC.bind` is a raw `flatMap`, so every
bound row is passed through `Xark.Template.norm`; `Formal/Norm.lean` proves that this
preserves the row's value.

The proof then reads the rows as integers. The product rows make each column's shadow
the convolution `conv`, the step instances' rows give each carry `k_j = num_j / 2^164`
(`GroupedCarry.carry_of_sat_shadow`), `GroupedColumns.carry_spec_of_steps` assembles
the 24 equations plus the top row into `CarrySpec`, and `GroupedColumns.soundness` and
`mul_eq` turn the telescope into the integer identity
`val a · val b = val q · val m + val rhs`.
-/

namespace Xark.Templates.GroupedColumns

open Xark.Template Xark.R1cs

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- The witness holding `a i · b k`, and `q i · m k` at `+ 1`. -/
def prodVar (i k : ℕ) : ℕ := 2 * (i * 25 + k)

/-- Column `c` of `a·b`: the products whose indices add to `c`. -/
def lhsTerms (c : ℕ) : List (ℤ × TVar) :=
  (List.range 25).flatMap fun i =>
    ((List.range 25).filter fun k => i + k = c).map fun k => (1, TVar.wit (prodVar i k))

/-- Column `c` of `a·b` over the integers. -/
def lhsZ (c : ℕ) : Xark.R1cs.LC ℤ TVar := ⟨0, lhsTerms c⟩

/-- Column `c` of `q·m`, plus the right-hand side's limb `c` for `c < 25`. -/
def rhsTerms (c : ℕ) : List (ℤ × TVar) :=
  ((List.range 25).flatMap fun i =>
    ((List.range 25).filter fun k => i + k = c).map fun k =>
      (1, TVar.wit (prodVar i k + 1)))
  ++ (if c < 25 then [((1 : ℤ), TVar.plug (100 + c))] else [])

/-- Column `c` of `q·m` over the integers, plus the right-hand side's limb `c`. -/
def rhsZ (c : ℕ) : Xark.R1cs.LC ℤ TVar := ⟨0, rhsTerms c⟩

/-- Column `c` as the exported combination reads it. -/
def lhs (c : ℕ) : LC := Xark.Circuit.toField (lhsZ c)

/-- Column `c` of `q·m` as the exported combination reads it. -/
def rhs (c : ℕ) : LC := Xark.Circuit.toField (rhsZ c)

/-- The first variable of step instance `j` (`wit 0` is its carry). -/
def stepBase (j : ℕ) : ℕ := 1250 + 179 * j

/-- The first row of step instance `j` (91 rows per instance). -/
def stepRow0 (j : ℕ) : ℕ := 1250 + 91 * j

/-- The five plugs of step instance `j`: the two columns' products, then the carry. -/
def stepPlug (j : ℕ) : List LC :=
  [lhs (2 * j), lhs (2 * j + 1), rhs (2 * j), rhs (2 * j + 1),
   if j = 0 then LC.cst ((2 ^ 88 : ℕ) : F) else LC.var (.wit (1250 + 179 * (j - 1)))]

/-- Step instance `j`'s view of the parent's variables. -/
def stepEnv (j : ℕ) : TVar → LC
  | .plug i => (stepPlug j).getD i (LC.cst 0)
  | .wit t => LC.var (.wit (stepBase j + t))

/-- A step template row, its plugs substituted and the result normalized. -/
def bindNorm (e : TVar → LC) (r : Row) : Row :=
  ⟨norm (r.a.bind e), norm (r.b.bind e), norm (r.c.bind e)⟩

/-- Step instance `j`'s 91 rows. -/
def stepRows (j : ℕ) : List Row :=
  Xark.Templates.GroupedColumnStep.template.rows.map (bindNorm (stepEnv j))

/-- The left product row `a i · b k`. -/
def prodRowA (i k : ℕ) : Row :=
  ⟨LC.var (.plug i), LC.var (.plug (25 + k)), LC.var (.wit (prodVar i k))⟩

/-- The quotient product row `q i · m k`. -/
def prodRowQ (i k : ℕ) : Row :=
  ⟨LC.var (.plug (75 + i)), LC.var (.plug (50 + k)),
   LC.var (.wit (prodVar i k + 1))⟩

/-- The 1,250 product rows, interleaved as the CSE emitted them. -/
def productRows : List Row :=
  (List.range 25).flatMap fun i =>
    (List.range 25).flatMap fun k => [prodRowA i k, prodRowQ i k]

/-- The top row: `d 48 + k 23 − 2^88 = 0`. -/
def topRow : Row :=
  ⟨norm ⟨-((2 ^ 88 : ℕ) : F), [(1, .wit 1248), (-1, .wit 1249), (1, .wit 5367)]⟩,
   ⟨1, []⟩, ⟨0, []⟩⟩

/-- The template's rows: products, the 24 step instances, the top row. -/
def modelRows : List Row :=
  productRows ++ (List.range 24).flatMap stepRows ++ [topRow]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The exported rows are the model.** -/
theorem rows_eq : template.rows = modelRows := by
  decide +kernel

/-! ### The gadget's contract

The call's 125 inputs are the five limb vectors, in the order `a`, `b`, `m`, `q`, `rhs`.
`Spec` is the integer product identity `val a · val b = val q · val m + val rhs`;
`Assumptions` is the limb bound the caller supplies (the `range_check_q`/`range_check_r`
contracts, or the input reader's). The gadget neither range-checks its inputs nor has
outputs. -/

/-- The integer value of the call's `i`-th input limb. -/
def inLimb (ins : List F) (i : ℕ) : ℤ := ((ins.getD i 0).val : ℤ)

/-- The gadget's contract: the product identity over the integers. -/
def Spec (ins _outs : List F) : Prop :=
  Xark.Rsa.GroupedColumns.val (fun i => inLimb ins i)
    * Xark.Rsa.GroupedColumns.val (fun i => inLimb ins (25 + i))
  = Xark.Rsa.GroupedColumns.val (fun i => inLimb ins (75 + i))
    * Xark.Rsa.GroupedColumns.val (fun i => inLimb ins (50 + i))
    + Xark.Rsa.GroupedColumns.val (fun i => inLimb ins (100 + i))

/-- The 125 input limbs are below `2^82`. -/
def Assumptions (ins : List F) : Prop :=
  ∀ i < 125, (ins.getD i 0).val < 2 ^ 82

/-- The template's inputs are its 125 plugs, in order. -/
theorem inputs_eq :
    template.inputs = (List.range 125).map fun i => (LC.var (TVar.plug i) : LC) := by
  decide +kernel

theorem ins_eq (σ : TVar → F) :
    template.ins σ = (List.range 125).map fun i => σ (.plug i) := by
  rw [Template.ins, inputs_eq, List.map_map]
  congr 1
  funext i
  simp

theorem ins_getD (σ : TVar → F) {i : ℕ} (hi : i < 125) :
    (template.ins σ).getD i 0 = σ (.plug i) := by
  rw [ins_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-! ### Column shadows

The rows talk about witnesses; the model talks about convolutions. These lemmas push a
sum over the column's term list into the double sum `conv` uses. -/

theorem sum_range_map (g : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sum_flatMap {α : Type*} (l : List α) (g : α → List ℤ) :
    (l.flatMap g).sum = (l.map fun a => (g a).sum).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, ih, List.sum_append]

theorem sum_filter_map (l : List ℕ) (p : ℕ → Prop) [DecidablePred p] (g : ℕ → ℤ) :
    ((l.filter p).map g).sum = (l.map fun k => if p k then g k else 0).sum := by
  induction l with
  | nil => simp
  | cons k ks ih =>
    rw [List.filter_cons]
    by_cases h : p k
    · simp [h, ih]
    · simp [h, ih]

/-- The product columns' term sums are the convolution's double sums. -/
theorem sum_convTerms (c shift : ℕ) (f : TVar → ℤ) :
    (((List.range 25).flatMap fun i =>
        ((List.range 25).filter fun k => i + k = c).map fun k =>
          ((1 : ℤ), TVar.wit (prodVar i k + shift))).map fun t => f t.2).sum
      = ∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25,
          if i + k = c then f (.wit (prodVar i k + shift)) else 0 := by
  rw [List.map_flatMap]
  rw [sum_flatMap]
  rw [sum_range_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.map_map]
  rw [sum_filter_map]
  rw [sum_range_map]
  simp

theorem sum_lhsTerms (c : ℕ) (f : TVar → ℤ) :
    ((lhsTerms c).map fun t => f t.2).sum
      = ∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25,
          if i + k = c then f (.wit (prodVar i k)) else 0 := by
  rw [lhsTerms]
  exact sum_convTerms c 0 f

theorem sum_rhsTerms (c : ℕ) (f : TVar → ℤ) :
    ((rhsTerms c).map fun t => f t.2).sum
      = (∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25,
          if i + k = c then f (.wit (prodVar i k + 1)) else 0)
        + (if c < 25 then f (.plug (100 + c)) else 0) := by
  rw [rhsTerms, List.map_append, List.sum_append]
  congr 1
  · rw [List.map_flatMap]
    rw [sum_flatMap]
    rw [sum_range_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [List.map_map]
    rw [sum_filter_map]
    rw [sum_range_map]
    simp
  · by_cases h : c < 25 <;> simp [h]

/-! ### The product rows

Each product row is a plain `x · y = z`: under any satisfying assignment its witness is
the field product of the two limbs, and since both limbs are canonical below `2^82` the
product is below `2^164 < r`, so the witness's representative is that product. -/

theorem prodRowA_mem {i k : ℕ} (hi : i < 25) (hk : k < 25) : prodRowA i k ∈ modelRows := by
  have h1 : prodRowA i k ∈ productRows := by
    rw [productRows]
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
    refine List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩
    simp [prodRowA]
  rw [modelRows]
  exact List.mem_append_left _ (List.mem_append_left _ h1)

theorem prodRowQ_mem {i k : ℕ} (hi : i < 25) (hk : k < 25) : prodRowQ i k ∈ modelRows := by
  have h1 : prodRowQ i k ∈ productRows := by
    rw [productRows]
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
    refine List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩
    simp [prodRowQ]
  rw [modelRows]
  exact List.mem_append_left _ (List.mem_append_left _ h1)

theorem two_pow_164_lt_r : (2 ^ 164 : ℕ) < r :=
  Xark.Templates.ToBits.two_pow_lt_r' (by norm_num)

/-- The `a i · b k` product row's witness is the integer product. -/
theorem prodRowA_val (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 125, (σ (.plug i)).val < 2 ^ 82) {i k : ℕ} (hi : i < 25) (hk : k < 25) :
    (σ (.wit (prodVar i k))).val = (σ (.plug i)).val * (σ (.plug (25 + k))).val := by
  have hsat : Xark.R1cs.Sat modelRows σ := by
    simpa only [Template.Sat, rows_eq] using h
  have hrow := hsat _ (prodRowA_mem hi hk)
  have heq : σ (.wit (prodVar i k)) = σ (.plug i) * σ (.plug (25 + k)) := by
    simpa [Xark.R1cs.Row.Sat, prodRowA, Xark.R1cs.LC.eval, Xark.R1cs.LC.var] using hrow.symm
  have hcast : σ (.wit (prodVar i k))
      = (((σ (.plug i)).val * (σ (.plug (25 + k))).val : ℕ) : F) := by
    have h1 : σ (.wit (prodVar i k))
        = (((σ (.plug i)).val : F) * ((σ (.plug (25 + k))).val : F)) := by
      rw [heq]
      congr 1 <;> exact (ZMod.natCast_zmod_val _).symm
    rw [h1, Nat.cast_mul]
  have hprod : (σ (.plug i)).val * (σ (.plug (25 + k))).val < r := by
    have h1 : (σ (.plug i)).val ≤ 2 ^ 82 - 1 := by
      have := hb i (by omega); omega
    have h2 : (σ (.plug (25 + k))).val ≤ 2 ^ 82 - 1 := by
      have := hb (25 + k) (by omega); omega
    have h3 : (σ (.plug i)).val * (σ (.plug (25 + k))).val ≤ (2 ^ 82 - 1) * (2 ^ 82 - 1) :=
      Nat.mul_le_mul h1 h2
    have h4 : (2 ^ 82 - 1) * (2 ^ 82 - 1) < 2 ^ 164 := by norm_num
    exact lt_of_le_of_lt h3 (lt_trans h4 two_pow_164_lt_r)
  rw [hcast, ZMod.val_natCast_of_lt hprod]

/-- The `q i · m k` product row's witness is the integer product. -/
theorem prodRowQ_val (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 125, (σ (.plug i)).val < 2 ^ 82) {i k : ℕ} (hi : i < 25) (hk : k < 25) :
    (σ (.wit (prodVar i k + 1))).val = (σ (.plug (75 + i))).val * (σ (.plug (50 + k))).val := by
  have hsat : Xark.R1cs.Sat modelRows σ := by
    simpa only [Template.Sat, rows_eq] using h
  have hrow := hsat _ (prodRowQ_mem hi hk)
  have heq : σ (.wit (prodVar i k + 1)) = σ (.plug (75 + i)) * σ (.plug (50 + k)) := by
    simpa [Xark.R1cs.Row.Sat, prodRowQ, Xark.R1cs.LC.eval, Xark.R1cs.LC.var] using hrow.symm
  have hcast : σ (.wit (prodVar i k + 1))
      = (((σ (.plug (75 + i))).val * (σ (.plug (50 + k))).val : ℕ) : F) := by
    have h1 : σ (.wit (prodVar i k + 1))
        = (((σ (.plug (75 + i))).val : F) * ((σ (.plug (50 + k))).val : F)) := by
      rw [heq]
      congr 1 <;> exact (ZMod.natCast_zmod_val _).symm
    rw [h1, Nat.cast_mul]
  have hprod : (σ (.plug (75 + i))).val * (σ (.plug (50 + k))).val < r := by
    have h1 : (σ (.plug (75 + i))).val ≤ 2 ^ 82 - 1 := by
      have := hb (75 + i) (by omega); omega
    have h2 : (σ (.plug (50 + k))).val ≤ 2 ^ 82 - 1 := by
      have := hb (50 + k) (by omega); omega
    have h3 : (σ (.plug (75 + i))).val * (σ (.plug (50 + k))).val
        ≤ (2 ^ 82 - 1) * (2 ^ 82 - 1) := Nat.mul_le_mul h1 h2
    have h4 : (2 ^ 82 - 1) * (2 ^ 82 - 1) < 2 ^ 164 := by norm_num
    exact lt_of_le_of_lt h3 (lt_trans h4 two_pow_164_lt_r)
  rw [hcast, ZMod.val_natCast_of_lt hprod]

end Xark.Templates.GroupedColumns
