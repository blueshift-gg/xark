/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.GroupedColumnsSquare
import Formal.GroupedColumnsGadget
import Mathlib.Tactic

set_option linter.style.header false
set_option maxRecDepth 100000
set_option linter.style.longLine false

/-!
# `xark_rsa::grouped_columns_square`, proven over its exported rows

`square_lazy` calls the chain with the same limb vector on both sides, so the frontend's
CSE merges the product `a i · a k` with `a k · a i`: 300 of the 625 left products
disappear, the call is 3,135 rows, and its witnesses are numbered differently from the
general gadget. This file models the merged layout

* 950 product rows: for `t = i·25 + k` in loop order, `a i · a k = wit (aProd t)` when
  `i ≤ k`, then always `q i · m k = wit (qProd t)`;
* 24 inlined step instances from row 950, witness 950 + 179j;
* the top row,

and proves `val a · val a = val q · val m + val rhs`. The arithmetic is the general
gadget's (`Formal/GroupedColumnsGadget`); only the product layout differs.
-/

namespace Xark.Templates.GroupedColumnsSquare

open Xark.Template Xark.R1cs
open Xark.Rsa.GroupedColumns (Q W BI OFF)
open Xark.Templates.GroupedColumns (conv_nonneg conv_lt cols_bounds inner_conv conv48
  sum_range_map sum_flatMap sum_filter_map two_pow_164_lt_r two_pow_169_lt_r)

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- The number of witness rows emitted before iteration `t = i·25 + k`. -/
def sqCnt : ℕ → ℕ
  | 0 => 0
  | t + 1 => sqCnt t + (if t / 25 ≤ t % 25 then 2 else 1)

/-- The witness holding `a i · a k` for the CSE'd pair. -/
def aProd (t : ℕ) : ℕ :=
  if t / 25 ≤ t % 25 then sqCnt t else sqCnt ((t % 25) * 25 + t / 25)

/-- The witness holding `q i · m k`. -/
def qProd (t : ℕ) : ℕ := sqCnt t + (if t / 25 ≤ t % 25 then 1 else 0)

/-- Column `c` of `a·a`, over the CSE'd left products. -/
def lhsTerms (c : ℕ) : List (ℤ × TVar) :=
  (List.range 25).flatMap fun i =>
    ((List.range 25).filter fun k => i + k = c).map fun k =>
      ((1 : ℤ), TVar.wit (aProd (i * 25 + k)))

/-- Column `c` of `q·m`, plus the right-hand side's limb `c` for `c < 25`. -/
def rhsTerms (c : ℕ) : List (ℤ × TVar) :=
  ((List.range 25).flatMap fun i =>
    ((List.range 25).filter fun k => i + k = c).map fun k =>
      ((1 : ℤ), TVar.wit (qProd (i * 25 + k))))
  ++ (if c < 25 then [((1 : ℤ), TVar.plug (75 + c))] else [])

def lhsZ (c : ℕ) : Xark.R1cs.LC ℤ TVar := ⟨0, lhsTerms c⟩
def rhsZ (c : ℕ) : Xark.R1cs.LC ℤ TVar := ⟨0, rhsTerms c⟩
def lhs (c : ℕ) : LC := Xark.Circuit.toField (lhsZ c)
def rhs (c : ℕ) : LC := Xark.Circuit.toField (rhsZ c)

def stepBase (j : ℕ) : ℕ := 950 + 179 * j
def stepRow0 (j : ℕ) : ℕ := 950 + 91 * j

def stepPlug (j : ℕ) : List LC :=
  [lhs (2 * j), lhs (2 * j + 1), rhs (2 * j), rhs (2 * j + 1),
   if j = 0 then LC.cst ((2 ^ 88 : ℕ) : F) else LC.var (.wit (950 + 179 * (j - 1)))]

def stepEnv (j : ℕ) : TVar → LC
  | .plug i => (stepPlug j).getD i (LC.cst 0)
  | .wit t => LC.var (.wit (stepBase j + t))

def bindNorm (e : TVar → LC) (r : Row) : Row :=
  ⟨norm (r.a.bind e), norm (r.b.bind e), norm (r.c.bind e)⟩

def stepRows (j : ℕ) : List Row :=
  Xark.Templates.GroupedColumnStep.template.rows.map (bindNorm (stepEnv j))

def prodRowA (t : ℕ) : Row :=
  ⟨LC.var (.plug (t / 25)), LC.var (.plug (t % 25)), LC.var (.wit (aProd t))⟩

def prodRowQ (t : ℕ) : Row :=
  ⟨LC.var (.plug (50 + t / 25)), LC.var (.plug (25 + t % 25)),
   LC.var (.wit (qProd t))⟩

def productRows : List Row :=
  (List.range 625).flatMap fun t =>
    (if t / 25 ≤ t % 25 then [prodRowA t] else []) ++ [prodRowQ t]

def topRow : Row :=
  ⟨norm ⟨-((2 ^ 88 : ℕ) : F), [(1, .wit 948), (-1, .wit 949), (1, .wit 5067)]⟩,
   ⟨1, []⟩, ⟨0, []⟩⟩

def modelRows : List Row :=
  productRows ++ (List.range 24).flatMap stepRows ++ [topRow]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The exported rows are the model.** -/
theorem rows_eq : template.rows = modelRows := by
  decide +kernel

/-! ### Product rows -/

theorem prodRowA_mem {t : ℕ} (ht : t < 625) (h : t / 25 ≤ t % 25) :
    prodRowA t ∈ modelRows := by
  have h1 : prodRowA t ∈ productRows := by
    rw [productRows]
    refine List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
    rw [if_pos h]
    exact List.mem_append_left _ (List.mem_singleton.mpr rfl)
  rw [modelRows]
  exact List.mem_append_left [topRow] (List.mem_append_left _ h1)

theorem prodRowQ_mem {t : ℕ} (ht : t < 625) : prodRowQ t ∈ modelRows := by
  have h1 : prodRowQ t ∈ productRows := by
    rw [productRows]
    refine List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
    by_cases h : t / 25 ≤ t % 25
    · rw [if_pos h]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · rw [if_neg h]; exact List.mem_singleton.mpr rfl
  rw [modelRows]
  exact List.mem_append_left [topRow] (List.mem_append_left _ h1)

/-- The left product's witness is the integer product, for a pair already merged by
the CSE (`i ≤ k`). -/
theorem prodRowA_val (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) {t : ℕ} (ht : t < 625)
    (hk : t / 25 ≤ t % 25) :
    (σ (.wit (aProd t))).val = (σ (.plug (t / 25))).val * (σ (.plug (t % 25))).val := by
  have hsat : Xark.R1cs.Sat modelRows σ := by
    simpa only [Template.Sat, rows_eq] using h
  have hrow := hsat _ (prodRowA_mem ht hk)
  have heq : σ (.wit (aProd t))
      = σ (.plug (t / 25)) * σ (.plug (t % 25)) := by
    simpa [Xark.R1cs.Row.Sat, prodRowA, Xark.R1cs.LC.eval, Xark.R1cs.LC.var] using hrow.symm
  have hcast : σ (.wit (aProd t))
      = (((σ (.plug (t / 25))).val * (σ (.plug (t % 25))).val : ℕ) : F) := by
    have h1 : σ (.wit (aProd t))
        = (((σ (.plug (t / 25))).val : F) * ((σ (.plug (t % 25))).val : F)) := by
      rw [heq]
      congr 1 <;> exact (ZMod.natCast_zmod_val _).symm
    rw [h1, Nat.cast_mul]
  have hprod : (σ (.plug (t / 25))).val * (σ (.plug (t % 25))).val < r := by
    have ht' : t / 25 < 25 := by omega
    have hm' : t % 25 < 25 := by omega
    have h1 : (σ (.plug (t / 25))).val ≤ 2 ^ 82 - 1 := by
      have := hb (t / 25) (by omega); omega
    have h2 : (σ (.plug (t % 25))).val ≤ 2 ^ 82 - 1 := by
      have := hb (t % 25) (by omega); omega
    have h3 : (σ (.plug (t / 25))).val * (σ (.plug (t % 25))).val
        ≤ (2 ^ 82 - 1) * (2 ^ 82 - 1) := Nat.mul_le_mul h1 h2
    have h4 : (2 ^ 82 - 1) * (2 ^ 82 - 1) < 2 ^ 164 := by norm_num
    exact lt_of_le_of_lt h3 (lt_trans h4 Xark.Templates.GroupedColumns.two_pow_164_lt_r)
  rw [hcast, ZMod.val_natCast_of_lt hprod]

/-- The quotients' product witness is the integer product. -/
theorem prodRowQ_val (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) {t : ℕ} (ht : t < 625) :
    (σ (.wit (qProd t))).val = (σ (.plug (50 + t / 25))).val * (σ (.plug (25 + t % 25))).val := by
  have hsat : Xark.R1cs.Sat modelRows σ := by
    simpa only [Template.Sat, rows_eq] using h
  have hrow := hsat _ (prodRowQ_mem ht)
  have heq : σ (.wit (qProd t))
      = σ (.plug (50 + t / 25)) * σ (.plug (25 + t % 25)) := by
    simpa [Xark.R1cs.Row.Sat, prodRowQ, Xark.R1cs.LC.eval, Xark.R1cs.LC.var] using hrow.symm
  have hcast : σ (.wit (qProd t))
      = (((σ (.plug (50 + t / 25))).val * (σ (.plug (25 + t % 25))).val : ℕ) : F) := by
    have h1 : σ (.wit (qProd t))
        = (((σ (.plug (50 + t / 25))).val : F) * ((σ (.plug (25 + t % 25))).val : F)) := by
      rw [heq]
      congr 1 <;> exact (ZMod.natCast_zmod_val _).symm
    rw [h1, Nat.cast_mul]
  have hprod : (σ (.plug (50 + t / 25))).val * (σ (.plug (25 + t % 25))).val < r := by
    have h1 : (σ (.plug (50 + t / 25))).val ≤ 2 ^ 82 - 1 := by
      have := hb (50 + t / 25) (by omega); omega
    have h2 : (σ (.plug (25 + t % 25))).val ≤ 2 ^ 82 - 1 := by
      have := hb (25 + t % 25) (by omega); omega
    have h3 : (σ (.plug (50 + t / 25))).val * (σ (.plug (25 + t % 25))).val
        ≤ (2 ^ 82 - 1) * (2 ^ 82 - 1) := Nat.mul_le_mul h1 h2
    have h4 : (2 ^ 82 - 1) * (2 ^ 82 - 1) < 2 ^ 164 := by norm_num
    exact lt_of_le_of_lt h3 (lt_trans h4 Xark.Templates.GroupedColumns.two_pow_164_lt_r)
  rw [hcast, ZMod.val_natCast_of_lt hprod]

theorem aProd_swap {i k : ℕ} (hi : i < 25) (hk : k < 25) (h : k < i) :
    aProd (i * 25 + k) = aProd (k * 25 + i) := by
  have hdiv : (i * 25 + k) / 25 = i := by omega
  have hmod : (i * 25 + k) % 25 = k := by omega
  have hdiv2 : (k * 25 + i) / 25 = k := by omega
  have hmod2 : (k * 25 + i) % 25 = i := by omega
  have hle : k ≤ i := by omega
  have hnle : ¬ i ≤ k := by omega
  unfold aProd
  rw [hdiv, hmod, hdiv2, hmod2]
  simp [hle, hnle]

/-- The left product's witness is the integer product, for every ordered pair. -/
theorem aProd_val (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) {i k : ℕ} (hi : i < 25) (hk : k < 25) :
    (σ (.wit (aProd (i * 25 + k)))).val = (σ (.plug i)).val * (σ (.plug k)).val := by
  by_cases hik : i ≤ k
  · have ht : i * 25 + k < 625 := by omega
    have hdiv : (i * 25 + k) / 25 = i := by omega
    have hmod : (i * 25 + k) % 25 = k := by omega
    rw [prodRowA_val σ h hb ht (by omega), hdiv, hmod]
  · have hki : k < i := by omega
    have ht : k * 25 + i < 625 := by omega
    rw [aProd_swap hi hk hki]
    have hval := prodRowA_val σ h hb (t := k * 25 + i) ht (by omega)
    have hdiv2 : (k * 25 + i) / 25 = k := by omega
    have hmod2 : (k * 25 + i) % 25 = i := by omega
    rw [hval, hdiv2, hmod2]
    exact Nat.mul_comm _ _

theorem qProd_val (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) {i k : ℕ} (hi : i < 25) (hk : k < 25) :
    (σ (.wit (qProd (i * 25 + k)))).val
      = (σ (.plug (50 + i))).val * (σ (.plug (25 + k))).val := by
  have ht : i * 25 + k < 625 := by omega
  have hdiv : (i * 25 + k) / 25 = i := by omega
  have hmod : (i * 25 + k) % 25 = k := by omega
  rw [prodRowQ_val σ h hb ht, hdiv, hmod]

/-! ### Limbs and column shadows -/

def plugA (σ : TVar → F) : ℕ → ℤ := fun i => ((σ (.plug i)).val : ℤ)
def plugB (σ : TVar → F) : ℕ → ℤ := plugA σ
def plugM (σ : TVar → F) : ℕ → ℤ := fun i => ((σ (.plug (25 + i))).val : ℤ)
def plugQ (σ : TVar → F) : ℕ → ℤ := fun i => ((σ (.plug (50 + i))).val : ℤ)
def plugR (σ : TVar → F) : ℕ → ℤ := fun i => ((σ (.plug (75 + i))).val : ℤ)

theorem shadow_terms (σ : TVar → F) (ts : List (ℤ × TVar)) :
    Xark.Circuit.shadow σ ⟨0, ts⟩ = (ts.map fun t => t.1 * ((σ t.2).val : ℤ)).sum := by
  simp [Xark.Circuit.shadow]

theorem lhsTerms_coeff {c : ℕ} {t : ℤ × TVar} (ht : t ∈ lhsTerms c) : t.1 = 1 := by
  rw [lhsTerms] at ht
  obtain ⟨i, _, hti⟩ := List.mem_flatMap.mp ht
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hti
  rfl

theorem rhsTerms_coeff {c : ℕ} {t : ℤ × TVar} (ht : t ∈ rhsTerms c) : t.1 = 1 := by
  rw [rhsTerms] at ht
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨i, _, hti⟩ := List.mem_flatMap.mp h
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hti
    rfl
  · by_cases hc : c < 25
    · rw [if_pos hc] at h
      obtain rfl := List.mem_singleton.mp h
      rfl
    · rw [if_neg hc] at h
      exact absurd h (by simp)

theorem shadow_lhs (σ : TVar → F) (c : ℕ) :
    Xark.Circuit.shadow σ (lhsZ c) = ((lhsTerms c).map fun t => ((σ t.2).val : ℤ)).sum := by
  rw [lhsZ, shadow_terms]
  have hmap : (lhsTerms c).map (fun t => t.1 * ((σ t.2).val : ℤ))
      = (lhsTerms c).map fun t => ((σ t.2).val : ℤ) := by
    refine List.map_congr_left fun t ht => ?_
    rw [lhsTerms_coeff ht, one_mul]
  rw [hmap]

theorem shadow_rhs (σ : TVar → F) (c : ℕ) :
    Xark.Circuit.shadow σ (rhsZ c) = ((rhsTerms c).map fun t => ((σ t.2).val : ℤ)).sum := by
  rw [rhsZ, shadow_terms]
  have hmap : (rhsTerms c).map (fun t => t.1 * ((σ t.2).val : ℤ))
      = (rhsTerms c).map fun t => ((σ t.2).val : ℤ) := by
    refine List.map_congr_left fun t ht => ?_
    rw [rhsTerms_coeff ht, one_mul]
  rw [hmap]

theorem sum_lhsTerms (c : ℕ) (f : TVar → ℤ) :
    ((lhsTerms c).map fun t => f t.2).sum
      = ∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25,
          if i + k = c then f (.wit (aProd (i * 25 + k))) else 0 := by
  rw [lhsTerms, List.map_flatMap, sum_flatMap, sum_range_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [List.map_map, sum_filter_map, sum_range_map]
  simp

theorem sum_rhsTerms (c : ℕ) (f : TVar → ℤ) :
    ((rhsTerms c).map fun t => f t.2).sum
      = (∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25,
          if i + k = c then f (.wit (qProd (i * 25 + k))) else 0)
        + (if c < 25 then f (.plug (75 + c)) else 0) := by
  rw [rhsTerms, List.map_append, List.sum_append]
  congr 1
  · rw [List.map_flatMap, sum_flatMap, sum_range_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [List.map_map, sum_filter_map, sum_range_map]
    simp
  · by_cases h : c < 25 <;> simp [h]

theorem shadow_lhs_conv (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) (c : ℕ) :
    Xark.Circuit.shadow σ (lhsZ c) = Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c := by
  rw [shadow_lhs, sum_lhsTerms c (fun v => ((σ v).val : ℤ))]
  rw [Xark.Rsa.GroupedColumns.conv]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => ?_
  have hi' := Finset.mem_range.mp hi
  have hk' := Finset.mem_range.mp hk
  by_cases hc : i + k = c
  · rw [if_pos hc, if_pos hc]
    rw [aProd_val σ h hb hi' hk', Nat.cast_mul]
    rfl
  · rw [if_neg hc, if_neg hc]

theorem shadow_rhs_conv (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) (c : ℕ) :
    Xark.Circuit.shadow σ (rhsZ c)
      = Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
        + (if c < 25 then plugR σ c else 0) := by
  rw [shadow_rhs, sum_rhsTerms c (fun v => ((σ v).val : ℤ))]
  rw [Xark.Rsa.GroupedColumns.conv]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => ?_
    have hi' := Finset.mem_range.mp hi
    have hk' := Finset.mem_range.mp hk
    by_cases hc : i + k = c
    · rw [if_pos hc, if_pos hc]
      rw [qProd_val σ h hb hi' hk', Nat.cast_mul]
      rfl
    · rw [if_neg hc, if_neg hc]

theorem eval_lhs_eq (σ : TVar → F) (c : ℕ) :
    (lhs c).eval σ = ((Xark.Circuit.shadow σ (lhsZ c) : ℤ) : F) :=
  Xark.Circuit.shadow_toF σ (lhsZ c)

theorem eval_rhs_eq (σ : TVar → F) (c : ℕ) :
    (rhs c).eval σ = ((Xark.Circuit.shadow σ (rhsZ c) : ℤ) : F) :=
  Xark.Circuit.shadow_toF σ (rhsZ c)

theorem plugA_bounds (σ : TVar → F) (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) :
    ∀ i < 25, 0 ≤ plugA σ i ∧ plugA σ i < 2 ^ 82 := by
  intro i hi
  refine ⟨?_, ?_⟩
  · change (0 : ℤ) ≤ ((σ (.plug i)).val : ℤ); exact Int.natCast_nonneg _
  · change ((σ (.plug i)).val : ℤ) < (2 ^ 82 : ℤ); exact_mod_cast hb i (by omega)

theorem plugB_bounds (σ : TVar → F) (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) :
    ∀ i < 25, 0 ≤ plugB σ i ∧ plugB σ i < 2 ^ 82 := by
  simpa [plugB] using plugA_bounds σ hb

theorem plugM_bounds (σ : TVar → F) (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) :
    ∀ i < 25, 0 ≤ plugM σ i ∧ plugM σ i < 2 ^ 82 := by
  intro i hi
  refine ⟨?_, ?_⟩
  · change (0 : ℤ) ≤ ((σ (.plug (25 + i))).val : ℤ); exact Int.natCast_nonneg _
  · change ((σ (.plug (25 + i))).val : ℤ) < (2 ^ 82 : ℤ)
    exact_mod_cast hb (25 + i) (by omega)

theorem plugQ_bounds (σ : TVar → F) (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) :
    ∀ i < 25, 0 ≤ plugQ σ i ∧ plugQ σ i < 2 ^ 82 := by
  intro i hi
  refine ⟨?_, ?_⟩
  · change (0 : ℤ) ≤ ((σ (.plug (50 + i))).val : ℤ); exact Int.natCast_nonneg _
  · change ((σ (.plug (50 + i))).val : ℤ) < (2 ^ 82 : ℤ)
    exact_mod_cast hb (50 + i) (by omega)

theorem plugR_bounds (σ : TVar → F) (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) :
    ∀ i < 25, 0 ≤ plugR σ i ∧ plugR σ i < 2 ^ 82 := by
  intro i hi
  refine ⟨?_, ?_⟩
  · change (0 : ℤ) ≤ ((σ (.plug (75 + i))).val : ℤ); exact Int.natCast_nonneg _
  · change ((σ (.plug (75 + i))).val : ℤ) < (2 ^ 82 : ℤ)
    exact_mod_cast hb (75 + i) (by omega)

theorem eval_lhs_val (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) (c : ℕ) :
    (((lhs c).eval σ).val : ℤ) = Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c := by
  have h169 : (2 : ℤ) ^ 169 < (r : ℤ) := by
    exact_mod_cast Xark.Templates.GroupedColumns.two_pow_169_lt_r
  have h0 : 0 ≤ Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c :=
    Xark.Templates.GroupedColumns.conv_nonneg _ _
      (fun i _ => by change (0 : ℤ) ≤ ((σ (.plug i)).val : ℤ); exact Int.natCast_nonneg _)
      (fun i _ => by change (0 : ℤ) ≤ ((σ (.plug i)).val : ℤ); exact Int.natCast_nonneg _) c
  have hlt : Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c < 2 ^ 169 :=
    Xark.Templates.GroupedColumns.conv_lt _ _ (plugA_bounds σ hb) (plugA_bounds σ hb) c
  have hltN : (Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c).toNat < r := by
    have hz : ((Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c).toNat : ℤ)
        = Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c := Int.toNat_of_nonneg h0
    have : ((Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c).toNat : ℤ) < (r : ℤ) := by
      rw [hz]; exact lt_trans hlt h169
    exact_mod_cast this
  have hcast : ((Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c : ℤ) : F)
      = ((Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) c).toNat : ℕ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [eval_lhs_eq, shadow_lhs_conv σ h hb c, hcast, ZMod.val_natCast_of_lt hltN]
  exact Int.toNat_of_nonneg h0

theorem eval_rhs_val (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) (c : ℕ) :
    (((rhs c).eval σ).val : ℤ)
      = Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
        + (if c < 25 then plugR σ c else 0) := by
  have h170 : (2 : ℤ) ^ 170 < (r : ℤ) := by
    exact_mod_cast Xark.Templates.ToBits.two_pow_lt_r' (by norm_num : 170 ≤ 253)
  have h1 : 0 ≤ Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c :=
    Xark.Templates.GroupedColumns.conv_nonneg _ _
      (fun i _ => by change (0 : ℤ) ≤ ((σ (.plug (50 + i))).val : ℤ); exact Int.natCast_nonneg _)
      (fun i _ => by change (0 : ℤ) ≤ ((σ (.plug (25 + i))).val : ℤ); exact Int.natCast_nonneg _) c
  have hlt1 : Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c < 2 ^ 169 :=
    Xark.Templates.GroupedColumns.conv_lt _ _ (plugQ_bounds σ hb) (plugM_bounds σ hb) c
  have h2 : 0 ≤ (if c < 25 then plugR σ c else 0) := by
    by_cases hc : c < 25
    · rw [if_pos hc]; change (0 : ℤ) ≤ ((σ (.plug (75 + c))).val : ℤ)
      exact Int.natCast_nonneg _
    · rw [if_neg hc]
  have hr : (if c < 25 then plugR σ c else 0) < 2 ^ 82 := by
    by_cases hc : c < 25
    · rw [if_pos hc]
      change ((σ (.plug (75 + c))).val : ℤ) < (2 ^ 82 : ℤ)
      exact_mod_cast hb (75 + c) (by omega)
    · rw [if_neg hc]; norm_num
  have h0 : 0 ≤ Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
      + (if c < 25 then plugR σ c else 0) := by linarith
  have hlt : Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
      + (if c < 25 then plugR σ c else 0) < 2 ^ 170 := by linarith
  have hltN : (Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
      + (if c < 25 then plugR σ c else 0)).toNat < r := by
    have hz : ((Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
        + (if c < 25 then plugR σ c else 0)).toNat : ℤ)
        = Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
          + (if c < 25 then plugR σ c else 0) := Int.toNat_of_nonneg h0
    have : ((Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
        + (if c < 25 then plugR σ c else 0)).toNat : ℤ) < (r : ℤ) := by
      rw [hz]; exact lt_trans hlt h170
    exact_mod_cast this
  have hcast : ((Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
        + (if c < 25 then plugR σ c else 0) : ℤ) : F)
      = ((Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) c
        + (if c < 25 then plugR σ c else 0)).toNat : ℕ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [eval_rhs_eq, shadow_rhs_conv σ h hb c, hcast, ZMod.val_natCast_of_lt hltN]
  exact Int.toNat_of_nonneg h0

/-! ### The step instances

Instance `j` starts at row `1250 + 91j` and witness `1250 + 179j`; its five plugs are the
two columns of each product and the previous carry (`2^88` for the first). These lemmas
read the instance's plugs and hand its rows the step template's assignment. -/

/-- Step instance `j`'s assignment: its plugs' and witnesses' values in the parent. -/
def stepLift (j : ℕ) (σ : TVar → F) : TVar → F := fun v => (stepEnv j v).eval σ

theorem stepPlug_getD0 (j : ℕ) : (stepPlug j).getD 0 (LC.cst 0) = lhs (2 * j) := by
  simp [stepPlug]

theorem stepPlug_getD1 (j : ℕ) : (stepPlug j).getD 1 (LC.cst 0) = lhs (2 * j + 1) := by
  simp [stepPlug]

theorem stepPlug_getD2 (j : ℕ) : (stepPlug j).getD 2 (LC.cst 0) = rhs (2 * j) := by
  simp [stepPlug]

theorem stepPlug_getD3 (j : ℕ) : (stepPlug j).getD 3 (LC.cst 0) = rhs (2 * j + 1) := by
  simp [stepPlug]

theorem stepPlug_getD4 (j : ℕ) :
    (stepPlug j).getD 4 (LC.cst 0)
      = (if j = 0 then LC.cst ((2 ^ 88 : ℕ) : F) else LC.var (.wit (950 + 179 * (j - 1)))) := by
  simp [stepPlug]

theorem stepEnv_plug0 (j : ℕ) : stepEnv j (.plug 0) = lhs (2 * j) := by
  simp [stepEnv, stepPlug]

theorem stepEnv_plug1 (j : ℕ) : stepEnv j (.plug 1) = lhs (2 * j + 1) := by
  simp [stepEnv, stepPlug]

theorem stepEnv_plug2 (j : ℕ) : stepEnv j (.plug 2) = rhs (2 * j) := by
  simp [stepEnv, stepPlug]

theorem stepEnv_plug3 (j : ℕ) : stepEnv j (.plug 3) = rhs (2 * j + 1) := by
  simp [stepEnv, stepPlug]

theorem stepEnv_plug4 (j : ℕ) :
    stepEnv j (.plug 4)
      = (if j = 0 then LC.cst ((2 ^ 88 : ℕ) : F) else LC.var (.wit (950 + 179 * (j - 1)))) := by
  simp [stepEnv, stepPlug]

theorem stepLift_plug0 (j : ℕ) (σ : TVar → F) :
    stepLift j σ (.plug 0) = (lhs (2 * j)).eval σ := by
  rw [stepLift, stepEnv_plug0]

theorem stepLift_plug1 (j : ℕ) (σ : TVar → F) :
    stepLift j σ (.plug 1) = (lhs (2 * j + 1)).eval σ := by
  rw [stepLift, stepEnv_plug1]

theorem stepLift_plug2 (j : ℕ) (σ : TVar → F) :
    stepLift j σ (.plug 2) = (rhs (2 * j)).eval σ := by
  rw [stepLift, stepEnv_plug2]

theorem stepLift_plug3 (j : ℕ) (σ : TVar → F) :
    stepLift j σ (.plug 3) = (rhs (2 * j + 1)).eval σ := by
  rw [stepLift, stepEnv_plug3]

theorem stepLift_plug4 (j : ℕ) (σ : TVar → F) :
    stepLift j σ (.plug 4)
      = (if j = 0 then ((2 ^ 88 : ℕ) : F) else σ (.wit (950 + 179 * (j - 1)))) := by
  rw [stepLift, stepEnv_plug4]
  by_cases h : j = 0
  · rw [if_pos h, if_pos h]
    simp [Xark.R1cs.LC.cst, Xark.R1cs.LC.eval]
  · rw [if_neg h, if_neg h]
    simp [Xark.R1cs.LC.var, Xark.R1cs.LC.eval]

theorem stepLift_wit (j : ℕ) (σ : TVar → F) (t : ℕ) :
    stepLift j σ (.wit t) = σ (.wit (stepBase j + t)) := by
  simp [stepLift, stepEnv, LC.eval_var]

/-- A step instance's rows satisfy the step template's assignment. -/
theorem stepLift_sat (σ : TVar → F) (h : template.Sat σ) (j : ℕ) (hj : j < 24) :
    Xark.Templates.GroupedColumnStep.template.Sat (stepLift j σ) := by
  have hsat : Xark.R1cs.Sat modelRows σ := by
    simpa only [Template.Sat, rows_eq] using h
  intro r hr
  have hmem0 : bindNorm (stepEnv j) r ∈ (List.range 24).flatMap stepRows := by
    rw [List.mem_flatMap]
    exact ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  have hmem : bindNorm (stepEnv j) r ∈ modelRows := by
    simp only [modelRows]
    simp [hmem0]
  have hrow := hsat _ hmem
  have h' := hrow
  simp only [bindNorm, Xark.R1cs.Row.Sat, eval_norm, Xark.R1cs.LC.eval_bind] at h'
  exact h'

/-! ### The carries

The column difference `dcol` is `conv a b − conv q m − rhs`; `carry` is instance `j`'s
output. The step's pin row gives `OFF − BI + dcol (2j) + W·dcol (2j+1) + cb = Q·carry`,
which is `GroupedColumns.CarrySpec`'s per-step equation with `cb` the previous carry. -/

/-- The column difference of the call's limbs. -/
def dcol (σ : TVar → F) (c : ℕ) : ℤ :=
  Xark.Rsa.GroupedColumns.cols (plugA σ) (plugA σ) (plugQ σ) (plugM σ) (plugR σ) c

/-- Instance `j`'s carry, as the integer its witness denotes. -/
def carry (σ : TVar → F) (j : ℕ) : ℤ := ((stepLift j σ (.wit 0)).val : ℤ)

/-- The carry instance `j` reads: the bias for the first, else `k_{j−1}`. -/
def cb (σ : TVar → F) (j : ℕ) : ℤ := ((stepLift j σ (.plug 4)).val : ℤ)

theorem dcol_bounds (σ : TVar → F)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) (c : ℕ) :
    -(2 ^ 169 + 2 ^ 82) < dcol σ c ∧ dcol σ c < 2 ^ 169 :=
  cols_bounds _ _ _ _ _ (plugA_bounds σ hb) (plugB_bounds σ hb) (plugM_bounds σ hb)
    (plugQ_bounds σ hb) (plugR_bounds σ hb) c

theorem shadow_numZ_eq (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) (j : ℕ) :
    Xark.Circuit.shadow (stepLift j σ) Xark.Rsa.GroupedCarry.numZ
      = (OFF - BI) + dcol σ (2 * j) + W * dcol σ (2 * j + 1) + cb σ j := by
  rw [Xark.Rsa.GroupedCarry.shadow_numZ]
  have h0 : ((stepLift j σ (.plug 0)).val : ℤ)
      = Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) (2 * j) := by
    rw [stepLift_plug0]; exact eval_lhs_val σ h hb (2 * j)
  have h1 : ((stepLift j σ (.plug 1)).val : ℤ)
      = Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) (2 * j + 1) := by
    rw [stepLift_plug1]; exact eval_lhs_val σ h hb (2 * j + 1)
  have h2 : ((stepLift j σ (.plug 2)).val : ℤ)
      = Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) (2 * j)
        + (if 2 * j < 25 then plugR σ (2 * j) else 0) := by
    rw [stepLift_plug2]; exact eval_rhs_val σ h hb (2 * j)
  have h3 : ((stepLift j σ (.plug 3)).val : ℤ)
      = Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) (2 * j + 1)
        + (if 2 * j + 1 < 25 then plugR σ (2 * j + 1) else 0) := by
    rw [stepLift_plug3]; exact eval_rhs_val σ h hb (2 * j + 1)
  rw [h0, h1, h2, h3]
  simp only [dcol, cb, Xark.Rsa.GroupedColumns.cols, W, BI, OFF]
  ring

/-- Instance `j`'s carry is the step template's output, so the step's range check bounds
it by `2^89`. -/
theorem carry_bounds (σ : TVar → F) (h : template.Sat σ) (j : ℕ) (hj : j < 24) :
    0 ≤ carry σ j ∧ carry σ j < 2 ^ 89 := by
  have hsat := stepLift_sat σ h j hj
  have hspec := Xark.Templates.GroupedColumnStep.soundness (stepLift j σ) hsat
  have hout : Xark.Templates.GroupedColumnStep.template.outputs
      = [Xark.Templates.GroupedColumnStep.vLC] := by decide +kernel
  have := hspec
  simp only [Xark.Templates.GroupedColumnStep.Spec, Template.outs, hout, List.map_cons,
    List.map_nil, List.getD_cons_zero, Xark.Templates.GroupedColumnStep.vLC_eq,
    Xark.R1cs.LC.eval_var] at this
  refine ⟨?_, ?_⟩
  · show (0 : ℤ) ≤ carry σ j
    unfold carry
    exact Int.natCast_nonneg _
  · show carry σ j < (2 ^ 89 : ℤ)
    unfold carry
    exact_mod_cast this

theorem cb_eq (σ : TVar → F) (j : ℕ) :
    cb σ j = if j = 0 then BI else carry σ (j - 1) := by
  rw [cb, stepLift_plug4]
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj]
    have h : (((2 ^ 88 : ℕ) : F)).val = 2 ^ 88 :=
      ZMod.val_natCast_of_lt (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num))
    rw [h]
    show ((2 ^ 88 : ℕ) : ℤ) = BI
    norm_num [BI]
  · rw [if_neg hj, if_neg hj]
    rw [carry, stepLift_wit]
    simp [stepBase]

theorem cb_bounds (σ : TVar → F) (h : template.Sat σ) (j : ℕ) (hj : j < 24) :
    0 ≤ cb σ j ∧ cb σ j < 2 ^ 89 := by
  rw [cb_eq]
  by_cases hj0 : j = 0
  · rw [if_pos hj0]
    refine ⟨?_, ?_⟩
    · show (0 : ℤ) ≤ BI; norm_num [BI]
    · show BI < (2 ^ 89 : ℤ); norm_num [BI]
  · rw [if_neg hj0]
    exact carry_bounds σ h (j - 1) (by omega)

theorem shadow_numZ_bounds (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) (j : ℕ) (hj : j < 24) :
    0 ≤ Xark.Circuit.shadow (stepLift j σ) Xark.Rsa.GroupedCarry.numZ
      ∧ Xark.Circuit.shadow (stepLift j σ) Xark.Rsa.GroupedCarry.numZ < (r : ℤ) := by
  rw [shadow_numZ_eq σ h hb j]
  have hd0 := dcol_bounds σ hb (2 * j)
  have hd1 := dcol_bounds σ hb (2 * j + 1)
  have hcb := cb_bounds σ h j hj
  have hW : (0 : ℤ) < W := by norm_num [W]
  have hlowS : -(2 ^ 251 + 2 ^ 170) < dcol σ (2 * j) + W * dcol σ (2 * j + 1) := by
    have hm : W * (-(2 ^ 169 + 2 ^ 82)) < W * dcol σ (2 * j + 1) :=
      mul_lt_mul_of_pos_left hd1.1 hW
    have hbound : (2 ^ 169 + 2 ^ 82) * (1 + W) < 2 ^ 251 + 2 ^ 170 := by
      rw [W]; norm_num
    nlinarith [hd0.1, hm, hbound]
  have hupS : dcol σ (2 * j) + W * dcol σ (2 * j + 1) < 2 ^ 169 + W * 2 ^ 169 := by
    have hm : W * dcol σ (2 * j + 1) < W * 2 ^ 169 := mul_lt_mul_of_pos_left hd1.2 hW
    linarith [hd0.2]
  constructor
  · have hpos : 0 < OFF - BI - (2 ^ 251 + 2 ^ 170) := by norm_num [OFF, BI]
    linarith [hcb.1]
  · have hlt : OFF - BI + (2 ^ 169 + W * 2 ^ 169) + 2 ^ 89 < (r : ℤ) := by
      norm_num [OFF, BI, W, r]
    linarith [hcb.2]

/-- The per-step equation `GroupedColumns.CarrySpec` consumes. -/
theorem step_row (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) (j : ℕ) (hj : j < 24) :
    dcol σ (2 * j) + W * dcol σ (2 * j + 1) + (if j = 0 then BI else carry σ (j - 1))
        - BI + OFF = Q * carry σ j := by
  have hbnds := shadow_numZ_bounds σ h hb j hj
  have hc := Xark.Rsa.GroupedCarry.carry_of_sat_shadow (stepLift j σ) (stepLift_sat σ h j hj)
    hbnds.1 hbnds.2
  rw [shadow_numZ_eq σ h hb j] at hc
  rw [show Xark.Templates.GroupedColumnStep.vLC.eval (stepLift j σ)
      = stepLift j σ (.wit 0) from by
    rw [Xark.Templates.GroupedColumnStep.vLC_eq]; exact Xark.R1cs.LC.eval_var _ _] at hc
  change (OFF - BI) + dcol σ (2 * j) + W * dcol σ (2 * j + 1) + cb σ j
      = Q * carry σ j at hc
  rw [cb_eq σ j] at hc
  linarith


/-! ### The top row and the contract -/

theorem topRow_eval (σ : TVar → F) :
    topRow.a.eval σ
      = σ (.wit 948) - σ (.wit 949) + σ (.wit 5067) - ((2 ^ 88 : ℕ) : F) := by
  unfold topRow
  rw [Xark.Template.eval_norm]
  simp only [Xark.R1cs.LC.eval, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
    add_zero]
  ring

/-- The top row's integer equation: `d 48 + k 23 = 2^88`. -/
theorem top_row (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) :
    dcol σ 48 + carry σ 23 - BI = 0 := by
  have hsat : Xark.R1cs.Sat modelRows σ := by
    simpa only [Template.Sat, rows_eq] using h
  have hrow := hsat topRow (by simp [modelRows])
  have hz : (σ (.wit 948) - σ (.wit 949) + σ (.wit 5067) - ((2 ^ 88 : ℕ) : F)) = 0 := by
    have hrow' : topRow.a.eval σ = 0 := by
      have hb1 : topRow.b.eval σ = 1 := by
        unfold topRow
        simp [Xark.R1cs.LC.eval]
      have hc0 : topRow.c.eval σ = 0 := by
        unfold topRow
        simp [Xark.R1cs.LC.eval]
      have := hrow
      rw [Xark.R1cs.Row.Sat, hb1, hc0, mul_one] at this
      exact this
    rwa [topRow_eval] at hrow'
  have hcomp : σ (.wit 5067) = ((carry σ 23 : ℤ) : F) := by
    have hw : stepLift 23 σ (.wit 0) = σ (.wit 5067) := by
      rw [stepLift_wit]
      norm_num [stepBase]
    rw [← hw]
    show stepLift 23 σ (.wit 0) = ((carry σ 23 : ℤ) : F)
    unfold carry
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hp : σ (.wit 948) = (((σ (.plug 24)).val * (σ (.plug 24)).val : ℕ) : F) := by
    have hv := prodRowA_val σ h hb (t := 624) (by norm_num) (by norm_num)
    have hw : aProd 624 = 948 := by decide
    rw [hw] at hv
    rw [show 624 / 25 = 24 by norm_num, show 624 % 25 = 24 by norm_num] at hv
    rw [← ZMod.natCast_zmod_val (σ (.wit 948)), hv]
  have hq : σ (.wit 949) = (((σ (.plug 74)).val * (σ (.plug 49)).val : ℕ) : F) := by
    have hv := prodRowQ_val σ h hb (t := 624) (by norm_num)
    have hw : qProd 624 = 949 := by decide
    rw [hw] at hv
    rw [show 624 / 25 = 24 by norm_num, show 624 % 25 = 24 by norm_num] at hv
    rw [← ZMod.natCast_zmod_val (σ (.wit 949)), hv]
  rw [hp, hq, hcomp] at hz
  have hz' : ((Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) 48
      - Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) 48 + carry σ 23
      - ((2 ^ 88 : ℕ) : ℤ) : ℤ) : F) = 0 := by
    push_cast at hz
    rw [conv48 (plugA σ) (plugA σ), conv48 (plugQ σ) (plugM σ)]
    push_cast
    exact hz
  have hdvd : ((r : ℤ)) ∣ (Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) 48
      - Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) 48 + carry σ 23
      - ((2 ^ 88 : ℕ) : ℤ)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mp hz'
  have hc48 := dcol_bounds σ hb 48
  have hcarry := carry_bounds σ h 23 (by norm_num)
  have hd48 : dcol σ 48 = Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) 48
      - Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) 48 := by
    rw [dcol, Xark.Rsa.GroupedColumns.cols]
    have h : (if 48 < 25 then plugR σ 48 else 0) = 0 := by norm_num
    rw [h]
    ring
  have hlo : -(2 ^ 170 : ℤ) < Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) 48
      - Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) 48 + carry σ 23
      - ((2 ^ 88 : ℕ) : ℤ) := by
    rw [← hd48]
    rw [show ((2 ^ 88 : ℕ) : ℤ) = (2 ^ 88 : ℤ) by norm_num]
    have hnum : -(2 ^ 170 : ℤ) < -(2 ^ 169 + 2 ^ 82) - 2 ^ 88 := by norm_num
    linarith [hc48.1, hcarry.1, hnum]
  have hhi : Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) 48
      - Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) 48 + carry σ 23
      - ((2 ^ 88 : ℕ) : ℤ) < 2 ^ 170 := by
    rw [← hd48]
    rw [show ((2 ^ 88 : ℕ) : ℤ) = (2 ^ 88 : ℤ) by norm_num]
    have hnum : (2 ^ 169 : ℤ) + 2 ^ 89 - 2 ^ 88 < 2 ^ 170 := by norm_num
    linarith [hc48.2, hcarry.2, hnum]
  have h170r : (2 ^ 170 : ℤ) < (r : ℤ) := by
    exact_mod_cast Xark.Templates.ToBits.two_pow_lt_r' (by norm_num : 170 ≤ 253)
  have hz0 : Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) 48
      - Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) 48 + carry σ 23
      - ((2 ^ 88 : ℕ) : ℤ) = 0 := by
    rcases lt_trichotomy (Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) 48
      - Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) 48 + carry σ 23
      - ((2 ^ 88 : ℕ) : ℤ)) 0 with hneg | hzero | hpos
    · have hdvd' : ((r : ℤ)) ∣ -((Xark.Rsa.GroupedColumns.conv (plugA σ) (plugA σ) 48
          - Xark.Rsa.GroupedColumns.conv (plugQ σ) (plugM σ) 48 + carry σ 23
          - ((2 ^ 88 : ℕ) : ℤ))) := dvd_neg.mpr hdvd
      have h := Int.eq_zero_of_dvd_of_nonneg_of_lt (by linarith)
        (by linarith [hlo, h170r]) hdvd'
      linarith
    · exact hzero
    · have h := Int.eq_zero_of_dvd_of_nonneg_of_lt (by linarith)
        (by linarith [hhi, h170r]) hdvd
      linarith
  rw [hd48, show BI = ((2 ^ 88 : ℕ) : ℤ) by norm_num [BI]]
  exact hz0


/-! ### The contract -/

def inLimb (ins : List F) (i : ℕ) : ℤ := ((ins.getD i 0).val : ℤ)

def Assumptions (ins : List F) : Prop :=
  ∀ i < 100, (ins.getD i 0).val < 2 ^ 82

def Spec (ins _outs : List F) : Prop :=
  Assumptions ins →
    Xark.Rsa.GroupedColumns.val (fun i => inLimb ins i)
      * Xark.Rsa.GroupedColumns.val (fun i => inLimb ins i)
    = Xark.Rsa.GroupedColumns.val (fun i => inLimb ins (50 + i))
      * Xark.Rsa.GroupedColumns.val (fun i => inLimb ins (25 + i))
      + Xark.Rsa.GroupedColumns.val (fun i => inLimb ins (75 + i))

theorem inputs_eq :
    template.inputs = (List.range 100).map fun p => (LC.var (TVar.plug p) : LC) := by
  decide +kernel

theorem ins_eq (σ : TVar → F) :
    template.ins σ = (List.range 100).map fun p => σ (.plug p) := by
  rw [Template.ins, inputs_eq, List.map_map]
  congr 1
  funext p
  simp

theorem ins_getD (σ : TVar → F) {p : ℕ} (hp : p < 100) :
    (template.ins σ).getD p 0 = σ (.plug p) := by
  rw [ins_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp]
  rfl

theorem carry_spec (σ : TVar → F) (h : template.Sat σ)
    (hb : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82) :
    Xark.Rsa.GroupedColumns.CarrySpec (dcol σ) (carry σ) :=
  Xark.Rsa.GroupedColumns.carry_spec_of_steps (dcol σ) (carry σ)
    (fun j hj => step_row σ h hb j hj) (top_row σ h hb)

theorem val_a_eq (σ : TVar → F) :
    Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) i)
      = Xark.Rsa.GroupedColumns.val (plugA σ) := by
  rw [Xark.Rsa.GroupedColumns.val, Xark.Rsa.GroupedColumns.val]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi25 := Finset.mem_range.mp hi
  rw [inLimb, ins_getD σ (by omega)]
  rfl

theorem val_limb_eq (σ : TVar → F) (off : ℕ) (hoff : off + 25 ≤ 100) :
    Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) (off + i))
      = Xark.Rsa.GroupedColumns.val (fun i => ((σ (.plug (off + i))).val : ℤ)) := by
  rw [Xark.Rsa.GroupedColumns.val, Xark.Rsa.GroupedColumns.val]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi25 := Finset.mem_range.mp hi
  rw [inLimb, ins_getD σ (by omega)]

/-- **Soundness.** Under a satisfying assignment, the 100 input limbs (when below
`2^82`) satisfy `val a · val a = val q · val m + val rhs` over the integers. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  intro hbins
  have hbσ : ∀ i < 100, (σ (.plug i)).val < 2 ^ 82 := by
    intro i hi
    have h := hbins i hi
    rwa [ins_getD σ hi] at h
  have hcarry := carry_spec σ h hbσ
  have hspec := Xark.Rsa.GroupedColumns.soundness (dcol σ) (carry σ) hcarry
  have hmul := Xark.Rsa.GroupedColumns.mul_eq (plugA σ) (plugA σ) (plugM σ) (plugQ σ)
    (plugR σ) hspec
  have hB : Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) (25 + i))
      = Xark.Rsa.GroupedColumns.val (plugM σ) := by
    rw [val_limb_eq σ 25 (by norm_num)]
    rfl
  have hQ : Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) (50 + i))
      = Xark.Rsa.GroupedColumns.val (plugQ σ) := by
    rw [val_limb_eq σ 50 (by norm_num)]
    rfl
  have hR : Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) (75 + i))
      = Xark.Rsa.GroupedColumns.val (plugR σ) := by
    rw [val_limb_eq σ 75 (by norm_num)]
    rfl
  show Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) i)
      * Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) i)
    = Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) (50 + i))
      * Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) (25 + i))
      + Xark.Rsa.GroupedColumns.val (fun i => inLimb (template.ins σ) (75 + i))
  rw [val_a_eq σ, hB, hQ, hR]
  exact hmul

end Xark.Templates.GroupedColumnsSquare
