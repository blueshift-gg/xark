/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `grouped_columns`: the 25×82 carry/telescope model

This is the row-independent arithmetic model of `xark_rsa::grouped_columns`.
It does not depend on the generated R1CS template. The carry rows are the
exported `grouped_column_step` calls (their 89-bit range check is
`Formal/GroupedColumnStep.lean`), but this file takes them as integers: the
bridge from the step's field elements to `CarrySpec`'s `k : ℕ → ℤ` is a separate
obligation. The 130 MB raw `#[gadget]` export of `grouped_columns` is not used
(the nested calls' outputs are used as plugs, so substituting them every time
blows the rows up quadratically).

`d c` is the xark column `lhs c − rhs c`; `s j` groups the pair
`d (2j), d (2j+1)` with `W = 2^82`, so `Q = W^2 = 2^164`. The carry chain is
`S_j + k_{j−1} − BI + OFF = Q * k_j` with `k_{−1} = BI`, and the top column is
`d 48 + k 23 − BI = 0`. Each row is multiplied by `Q^j`, summed, and the
telescoping leaves the column identity.
-/

namespace Xark.Rsa.GroupedColumns

open scoped BigOperators

/-- `2^164`, the width of a paired column. -/
def Q : ℤ := 2 ^ 164

/-- `2^82`, the limb width. -/
def W : ℤ := 2 ^ 82

/-- `2^88`, the bias that keeps the carry non-negative. -/
def BI : ℤ := 2 ^ 88

/-- `2^252`, the offset, with `OFF = BI * Q`. -/
def OFF : ℤ := 2 ^ 252

/-- The 49-column identity `Σ_c d_c · W^c = 0`. -/
def Spec (d : ℕ → ℤ) : Prop :=
  ∑ c ∈ Finset.range 49, d c * W ^ c = 0

/-- The 24 paired carry rows and the top row. The first row is separate so the
`k (−1) = BI` case is not an `if` in the middle of the telescope. -/
def CarrySpec (d : ℕ → ℤ) (k : ℕ → ℤ) : Prop :=
  (d 0 + W * d 1 + BI - BI + OFF = Q * k 0)
  ∧ (∀ j, 0 < j → j < 24 →
      d (2 * j) + W * d (2 * j + 1) + k (j - 1) - BI + OFF = Q * k j)
  ∧ d 48 + k 23 - BI = 0

/-- The carry chain implies the column identity. -/
theorem soundness (d : ℕ → ℤ) (k : ℕ → ℤ)
    (h : CarrySpec d k) : Spec d := by
  rcases h with ⟨h0, hnum, htop⟩
  have hOFF : OFF = BI * Q := by norm_num [OFF, BI, Q]
  -- Group the 48 low columns into 24 pairs, then add the top column.
  have hpair : ∑ c ∈ Finset.range 49, d c * W ^ c
      = (∑ j ∈ Finset.range 24, (d (2 * j) + W * d (2 * j + 1)) * Q ^ j)
        + d 48 * Q ^ 24 := by
    repeat rw [Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add]
    rw [show Q = W ^ 2 by norm_num [Q, W]]
    ring
  have hgeom : (Q - 1) * (∑ j ∈ Finset.range 23, Q ^ (j + 1)) = Q ^ 24 - Q := by
    repeat rw [Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add]
    ring
  -- Multiply each carry row by `Q^j` and telescope. The induction makes the
  -- h0/h1..h23 BI/OFF boundary explicit; only the final geometric sum remains.
  have htel_aux : ∀ n ≤ 23,
      ∑ j ∈ Finset.range (n + 1), (d (2 * j) + W * d (2 * j + 1)) * Q ^ j
        = Q ^ (n + 1) * k n - OFF
            + (BI - OFF) * ∑ j ∈ Finset.range n, Q ^ (j + 1) := by
    intro n hn
    induction n with
    | zero =>
        have h := h0
        simp only [Finset.sum_range_one, Finset.sum_range_zero, Nat.zero_add,
          mul_zero, add_zero] at h ⊢
        linarith
    | succ n ih =>
        have h := hnum (n + 1) (by omega) (by omega)
        have hk : n + 1 - 1 = n := by omega
        rw [hk] at h
        have hn' : n ≤ 23 := by omega
        calc
          ∑ j ∈ Finset.range (n + 1 + 1), (d (2 * j) + W * d (2 * j + 1)) * Q ^ j
              = (∑ j ∈ Finset.range (n + 1), (d (2 * j) + W * d (2 * j + 1)) * Q ^ j)
                  + (d (2 * (n + 1)) + W * d (2 * (n + 1) + 1)) * Q ^ (n + 1) := by
                rw [Finset.sum_range_succ]
          _ = (Q ^ (n + 1) * k n - OFF
                  + (BI - OFF) * ∑ j ∈ Finset.range n, Q ^ (j + 1))
                + (d (2 * (n + 1)) + W * d (2 * (n + 1) + 1)) * Q ^ (n + 1) := by
                rw [ih hn']
          _ = Q ^ (n + 1 + 1) * k (n + 1) - OFF
                + (BI - OFF) * ∑ j ∈ Finset.range (n + 1), Q ^ (j + 1) := by
                rw [Finset.sum_range_succ]
                linear_combination (Q ^ (n + 1)) * h
  have h23 := htel_aux 23 (by norm_num)
  have htel : ∑ j ∈ Finset.range 24, (d (2 * j) + W * d (2 * j + 1)) * Q ^ j
      = -(BI - k 23) * Q ^ 24 := by
    rw [h23, hOFF]
    linear_combination (-BI) * hgeom
  have htop' : d 48 = -(k 23 - BI) := by linarith
  rw [Spec, hpair, htel, htop']
  ring

/-! ### The limbs behind the columns

The telescope above takes the columns `d c` as integers. This section reads them out of
the limb vectors the Rust builds: `d c` of a product `a·b` is the convolution of the two
limbs at column `c`, and `val` is the number the limbs denote. Then the column identity is
the integer identity `a² = q·m + r` that `square_lazy` exists to prove. -/

/-- The number a 25×82 limb vector denotes, `Σ xᵢ·W^i`. -/
def val (x : ℕ → ℤ) : ℤ := ∑ i ∈ Finset.range 25, x i * W ^ i

/-- Column `c` of the product `a·b`: the convolution of the limbs whose indices add to `c`. -/
def conv (a b : ℕ → ℤ) (c : ℕ) : ℤ :=
  ∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25, if i + k = c then a i * b k else 0

/-- `grouped_columns`' column: `a·b`'s convolution minus `q·m`'s, minus the right-hand
side's limb `c` (the remainder, or the encoded message). -/
def cols (a b q m rhs : ℕ → ℤ) (c : ℕ) : ℤ :=
  conv a b c - conv q m c - (if c < 25 then rhs c else 0)

/-- **The product's columns.** Multiplying two limb vectors multiplies their columns'
polynomials: `val a · val b = Σ_c conv a b c · W^c`. -/
theorem val_mul (a b : ℕ → ℤ) :
    val a * val b = ∑ c ∈ Finset.range 49, conv a b c * W ^ c := by
  rw [val, val, Finset.sum_mul_sum]
  have hstep : ∀ i ∈ Finset.range 25, ∀ k ∈ Finset.range 25,
      (a i * W ^ i) * (b k * W ^ k) = a i * b k * W ^ (i + k) := by
    intro i _ k _
    rw [pow_add]
    ring
  have hstep' : (∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25,
        (a i * W ^ i) * (b k * W ^ k))
      = ∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25, a i * b k * W ^ (i + k) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => hstep i hi k hk
  rw [hstep']
  have hprod : (∑ i ∈ Finset.range 25, ∑ k ∈ Finset.range 25, a i * b k * W ^ (i + k))
      = ∑ p ∈ Finset.range 25 ×ˢ Finset.range 25,
          a p.1 * b p.2 * W ^ (p.1 + p.2) := by
    rw [Finset.sum_product]
  rw [hprod]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range 25 ×ˢ Finset.range 25)
    (t := Finset.range 49) (g := fun p : ℕ × ℕ => p.1 + p.2)
    (f := fun p : ℕ × ℕ => a p.1 * b p.2 * W ^ (p.1 + p.2)) ?_]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [conv]
    simp only [Finset.sum_mul]
    rw [Finset.sum_filter, Finset.sum_product]
    dsimp only
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases h : i + k = c
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, zero_mul]
  · intro p hp
    obtain ⟨hi, hk⟩ := Finset.mem_product.mp hp
    exact Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hk
      omega)

/-- **The product identity.** With the columns `cols a b q m r` (a product `a·b`, a
quotient, a modulus and a right-hand side) satisfying the carry telescope, the limbs
satisfy `a·b = q·m + r` over the integers. -/
theorem mul_eq (a b m q r : ℕ → ℤ) (h : Spec (cols a b q m r)) :
    val a * val b = val q * val m + val r := by
  have hexp : ∀ c, cols a b q m r c * W ^ c =
      conv a b c * W ^ c - conv q m c * W ^ c
        - (if c < 25 then r c else 0) * W ^ c := by
    intro c
    unfold cols
    ring
  have h' : (∑ c ∈ Finset.range 49, (conv a b c * W ^ c - conv q m c * W ^ c
      - (if c < 25 then r c else 0) * W ^ c)) = 0 :=
    (Finset.sum_congr rfl fun c _ => (hexp c).symm).trans h
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h'
  have hsum49 : (∑ c ∈ Finset.range 49, (if c < 25 then r c else 0) * W ^ c)
      = ∑ c ∈ Finset.range 25, r c * W ^ c := by
    have hf : (∑ c ∈ Finset.range 25, (if c < 25 then r c else 0) * W ^ c)
        = ∑ c ∈ Finset.range 25, r c * W ^ c :=
      Finset.sum_congr rfl fun c hc => by rw [if_pos (Finset.mem_range.mp hc)]
    rw [← hf]
    refine (Finset.sum_subset (s₁ := Finset.range 25) (s₂ := Finset.range 49) ?_ ?_).symm
    · intro x hx
      exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hx) (by norm_num))
    · intro x _ hx
      have hx' : ¬ x < 25 := by
        intro hlt
        exact hx (Finset.mem_range.mpr hlt)
      rw [if_neg hx', zero_mul]
  rw [hsum49, ← val_mul a b, ← val_mul q m, ← val] at h'
  linarith

/-- **`square_lazy`, at the model level.** The 24 carry rows and the top row of
`grouped_columns` prove `a² = q·m + r` over the integers; the range checks bound `q` and
`r` separately (`GroupedColumns.soundness` is the telescope). -/
theorem square_lazy (a m q r : ℕ → ℤ) (k : ℕ → ℤ) (h : CarrySpec (cols a a q m r) k) :
    val a * val a = val q * val m + val r :=
  mul_eq a a m q r (soundness _ _ h)

/-- **`fused_final`, at the model level.** The terminal multiply: the same rows with the
right-hand side the public encoded message `em` rather than a hinted remainder, so the
claim is `a·b = q·m + em` over the integers (the remainder pins are what make `em` the
right-hand side). -/
theorem fused_final (a b m em q : ℕ → ℤ) (k : ℕ → ℤ)
    (h : CarrySpec (cols a b q m em) k) :
    val a * val b = val q * val m + val em :=
  mul_eq a b m q em (soundness _ _ h)

end Xark.Rsa.GroupedColumns
