/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.GroupedColumns
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `convert_wide`: the 17×121 → 25×82 carry chain

`xark_rsa::convert_wide` scatters the 17 limbs of a 2048-bit number into 25 columns
(`x_i` at weight `2^(121 i % 82)` in column `121 i / 82`), then reads each column
with a hinted `div_rem` by `2^82`:

`cols_j + c_{j-1} = 2^82 · c_j + y_j`, with `c_{-1} = 0`, and the top
quotient `c_24 = 0`.

The per-row equations are `require_eq(num, two_b * c + limb)` after the no-wrap
argument (a column term is below `2^199`, the carry below `2^118`, so each
`num < Fr` lifts to the integers). This file is what those rows give:

* `cols_sum`: the columns are the input, `Σ_j cols_j·W^j = Σ_i x_i·2^(121 i)`;
* `partial_sum`: after `k` limbs the outputs' value is the columns' value minus the
  running carry at weight `W^k` — the induction that avoids reindexing a sum;
* `telescoping`: at `k = 25` and `c_24 = 0`, the outputs' value is the input's,
  `Σ_j y_j·2^(82 j) = Σ_i x_i·2^(121 i)` — the re-limbing proves the value
  unchanged.
-/

namespace Xark.Rsa.Convert

/-- `2^82`, the output limb width. -/
def W : ℤ := 2 ^ 82

/-- Column `c` of the re-limbing: `x_i` lands at weight `2^(121 i % 82)` in column
`121 i / 82`. -/
def cols (x : ℕ → ℤ) (c : ℕ) : ℤ :=
  ∑ i ∈ Finset.range 17, if 121 * i / 82 = c then x i * 2 ^ (121 * i % 82) else 0

/-- **The columns are the input.** Scattering the limbs into columns and adding each
column's terms at its own weight recovers `Σ_i x_i·2^(121 i)`. -/
theorem cols_sum (x : ℕ → ℤ) :
    ∑ j ∈ Finset.range 25, cols x j * W ^ j
      = ∑ i ∈ Finset.range 17, x i * 2 ^ (121 * i) := by
  have hexp : ∀ j, cols x j * W ^ j =
      ∑ i ∈ Finset.range 17,
        (if 121 * i / 82 = j then x i * 2 ^ (121 * i % 82) else 0) * W ^ j := by
    intro j
    rw [cols, Finset.sum_mul]
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi17 : i < 17 := Finset.mem_range.mp hi
  have hq : 121 * i / 82 < 25 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  rw [Finset.sum_eq_single (121 * i / 82)]
  · rw [if_pos rfl, show W = 2 ^ 82 from rfl, mul_assoc, ← pow_mul, ← pow_add,
      Nat.mod_add_div]
  · intro b _ hb
    rw [if_neg (fun (h : 121 * i / 82 = b) => hb h.symm), zero_mul]
  · intro hnot
    exact absurd (Finset.mem_range.mpr hq) hnot

/-- **The carry telescopes.** After `k` limbs the outputs' value is the columns' value
minus the running carry at weight `W^k`; the row equations are the induction step. -/
theorem partial_sum (x y c : ℕ → ℤ)
    (hrow : ∀ j < 25, cols x j + (if j = 0 then 0 else c (j - 1)) = W * c j + y j) :
    ∀ k ≤ 25, (∑ j ∈ Finset.range k, y j * W ^ j)
      = (∑ j ∈ Finset.range k, cols x j * W ^ j)
        - (if k = 0 then 0 else c (k - 1)) * W ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ 25 := by omega
    have hklt : k < 25 := by omega
    have hrowk := hrow k hklt
    rw [Finset.sum_range_succ, ih hk', Finset.sum_range_succ,
      if_neg (by omega : ¬ (k + 1 = 0))]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [if_pos rfl, pow_zero, mul_one, zero_add] at hrowk ⊢
      rw [pow_one]
      linear_combination -hrowk
    · simp only [if_neg hk0] at hrowk ⊢
      rw [pow_succ, Nat.add_sub_cancel]
      linear_combination -hrowk * W ^ k

/-- **`convert_wide` proves the value unchanged.** The 25 carry rows (`W · c_j + y_j`)
with the top quotient zero telescope to
`Σ_j y_j·2^(82 j) = Σ_i x_i·2^(121 i)`. -/
theorem telescoping (x y c : ℕ → ℤ)
    (hrow : ∀ j < 25, cols x j + (if j = 0 then 0 else c (j - 1)) = W * c j + y j)
    (hc24 : c 24 = 0) :
    (∑ j ∈ Finset.range 25, y j * W ^ j)
      = ∑ i ∈ Finset.range 17, x i * 2 ^ (121 * i) := by
  have h := partial_sum x y c hrow 25 (le_refl 25)
  rw [if_neg (by norm_num : ¬ (25 = 0)), hc24, zero_mul, sub_zero] at h
  rw [h, cols_sum]

end Xark.Rsa.Convert
