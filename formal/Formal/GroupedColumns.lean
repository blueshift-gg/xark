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
It does not depend on the generated R1CS template. The bridge from the xark
rows to this model is a separate obligation; the 130 MB raw `#[gadget]` export
is not used.

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

end Xark.Rsa.GroupedColumns
