/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.ConvertValue

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# The `n_top` row's pieces

Row 9812 pins the top limb's affine expression `limb_24 − Σ bits` to `2^79`. These are
the verified ingredients for that lift: the row's shape, its evaluation as a
`Finset.sum`, the top block's boolean bits, and the cast of the bit sum to the field.
The final `limb_24 = 2^79 + Σ bits ≥ 2^79` assembly is the next step.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt sum_map_range cast_sum)

/-- The `n_top` row's `a`: `(limb_24 − Σ bits) − 2^79`. -/
def topNLC : GLC :=
  ⟨-((2 ^ 79 : ℕ) : F),
    (1, 26347) :: (List.range 79).map (fun i => ((-((2 ^ i : ℕ) : F)), 26348 + 2 * i))⟩

theorem topN_row : growAt 9812 = ⟨topNLC, ⟨1, []⟩, ⟨0, []⟩⟩ := by
  decide +kernel

/-- The row reads `−2^79 + limb_24 − Σ_i 2^i·bit_i`. -/
theorem topN_eval (σ : ℕ → F) :
    topNLC.eval σ =
      -((2 ^ 79 : ℕ) : F) + σ 26347
        - ∑ i ∈ Finset.range 79, ((2 ^ i : ℕ) : F) * σ (26348 + 2 * i) := by
  simp only [topNLC, Xark.R1cs.LC.eval, List.map_cons, List.sum_cons, sum_map_range,
    Function.comp_def, List.map_map]
  simp only [neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- The top block's 79 bits are boolean. -/
theorem topN_bits (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ i < 79, IsBit (σ (26348 + 2 * i)) := by
  have hblock : Sat (gblockRows 26347 26348 80) σ :=
    gblock_sat (s36_sat h) (k := 4826) (by decide +kernel)
  intro i hi
  have hmem : gboolRow 26348 i ∈ gblockRows 26347 26348 80 := by
    rw [gblockRows]
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega : i < 80 - 1), rfl⟩)
  have hrow := hblock _ hmem
  refine isBit_of_mul_self ?_
  simpa [Xark.R1cs.Row.Sat, gboolRow, LC.var, LC.eval, gbit] using hrow

/-- The bit sum, as a natural number, casts to the same field sum the row carries. -/
theorem topN_hcast (σ : ℕ → F) :
    ((∑ i ∈ Finset.range 79, 2 ^ i * (σ (26348 + 2 * i)).val : ℕ) : F) =
      (gacc 26348 80).eval σ := by
  simp only [gacc, Xark.R1cs.LC.eval, List.map_map, Function.comp_def, sum_map_range]
  push_cast
  simp only [ZMod.natCast_zmod_val, gbit, zero_add]

theorem n_top_eq (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (σ 26347).val =
      2 ^ 79 + ∑ i ∈ Finset.range 79, 2 ^ i * (σ (26348 + 2 * i)).val := by
  have hr := growAt_sat (s36_sat h) 9812 (by decide)
  rw [topN_row] at hr
  have ha : topNLC.eval σ = 0 := by
    simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr
  rw [topN_eval] at ha
  have hbits := topN_bits σ h
  let w : ℕ → ℕ := fun i => (σ (26348 + 2 * i)).val
  have hwb : ∀ i < 79, w i ≤ 1 := fun i hi => isBit_val (hbits i hi)
  have hWlt := word_lt w 79 hwb
  set S : ℕ := ∑ i ∈ Finset.range 79, 2 ^ i * w i
  have hSlt : S < 2 ^ 79 := hWlt
  have hcast' : (S : F) =
      ∑ i ∈ Finset.range 79, ((2 ^ i : ℕ) : F) * σ (26348 + 2 * i) := by
    rw [show S = ∑ i ∈ Finset.range 79, 2 ^ i * w i from rfl]
    rw [topN_hcast σ]
    simp only [gacc, Xark.R1cs.LC.eval, List.map_map, Function.comp_def, sum_map_range]
    simp only [gbit, zero_add]
  have h1 : (σ 26347 : F) = ((2 ^ 79 : ℕ) : F) + (S : F) := by
    rw [hcast']
    linear_combination ha
  have h2 : (((2 ^ 79 + S : ℕ)) : F) = ((2 ^ 79 : ℕ) : F) + (S : F) := by
    push_cast
    ring
  have h1' : (σ 26347 : F) = (((2 ^ 79 + S : ℕ)) : F) := by
    rw [h2]
    exact h1
  have h80r : (2 ^ 80 : ℕ) < r := Xark.Templates.ToBits.two_pow_lt_r' (n := 80) (by norm_num)
  have hval : (σ 26347).val = 2 ^ 79 + S := by
    rw [h1', ZMod.val_natCast_of_lt (by omega : 2 ^ 79 + S < r)]
  rw [hval]

/-- The modulus's top limb is at least `2^79`, i.e. `n ≥ 2^2047`. -/
theorem n_top_ge (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    2 ^ 79 ≤ (σ 26347).val := by
  rw [n_top_eq σ h]
  exact Nat.le_add_right _ _

theorem n_val_ge (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    2 ^ 2047 ≤ ∑ j ∈ Finset.range 25, yN σ j * (W : ℤ) ^ j := by
  have htop := n_top_ge σ h
  have hy24 : (2 ^ 79 : ℤ) ≤ yN σ 24 := by
    rw [show yN σ 24 = ((σ (nLimb.getD 24 0)).val : ℤ) from rfl]
    have hget : nLimb.getD 24 0 = 26347 := by decide
    rw [hget]
    exact_mod_cast htop
  have hW24 : (0 : ℤ) ≤ (W : ℤ) ^ 24 := by positivity
  have hterm : (2 : ℤ) ^ 79 * (W : ℤ) ^ 24 ≤ yN σ 24 * (W : ℤ) ^ 24 :=
    mul_le_mul_of_nonneg_right hy24 hW24
  have h2047 : (2 : ℤ) ^ 2047 = 2 ^ 79 * (W : ℤ) ^ 24 := by
    rw [show (W : ℤ) = 2 ^ 82 from rfl]
    ring_nf
  have hsplit : (∑ j ∈ Finset.range 25, yN σ j * (W : ℤ) ^ j)
      = (∑ j ∈ Finset.range 24, yN σ j * (W : ℤ) ^ j) + yN σ 24 * (W : ℤ) ^ 24 :=
    Finset.sum_range_succ (fun j => yN σ j * (W : ℤ) ^ j) 24
  have hW0 : (0 : ℤ) ≤ W := by
    rw [show (W : ℤ) = 2 ^ 82 from rfl]
    positivity
  have hsum0 : (0 : ℤ) ≤ ∑ j ∈ Finset.range 24, yN σ j * (W : ℤ) ^ j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by unfold yN; exact Int.natCast_nonneg _) (pow_nonneg hW0 j)
  calc (2 : ℤ) ^ 2047 = 2 ^ 79 * (W : ℤ) ^ 24 := h2047
    _ ≤ yN σ 24 * (W : ℤ) ^ 24 := hterm
    _ ≤ yN σ 24 * (W : ℤ) ^ 24 + (∑ j ∈ Finset.range 24, yN σ j * (W : ℤ) ^ j) :=
        le_add_of_nonneg_right hsum0
    _ = (∑ j ∈ Finset.range 24, yN σ j * (W : ℤ) ^ j) + yN σ 24 * (W : ℤ) ^ 24 := by ring
    _ = ∑ j ∈ Finset.range 25, yN σ j * (W : ℤ) ^ j := hsplit.symm

end Xark.Circuits.Rsa2048
