/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.GroupedColumns
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `verify_wide`'s statement: the chain's congruence and the modulus width

`xark_rsa::verify_wide` does three things at the top:

* `require_eq(n_top, 2^79)` pins the modulus's top bit, so a modulus whose limbs are
  below `2^82` and whose top limb is `2^79 + t` (`t < 2^79`) is exactly 2048 bits
  (`n_bits`);
* 16 calls of `square_lazy` keep `acc ≡ sig^(2^k) (mod n)` (`squarings`; each call's
  model theorem is `GroupedColumns.square_lazy`, whose statement is `a·a = q·n + r`
  over the integers);
* the terminal `fused_final` gives `acc·sig = q·n + em` (`GroupedColumns.fused_final`),
  so the whole chain proves `em ≡ sig^(2^16+1) (mod n)` (`chain`) — RSA verification
  with `e = 65537`.

The rows that instantiate these hypotheses are what remains hand-proved; the statements
here are the chain's contract.
-/

namespace Xark.Rsa.Chain

open Xark.Rsa.GroupedColumns (val W)

/-- `Σ_{i<n} (X-1)·X^i = X^n - 1`, the geometric sum bounding a limb vector's low part. -/
theorem geom_sum (X : ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (X - 1) * X ^ i = X ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

set_option maxRecDepth 100000 in
/-- **A 2048-bit modulus.** If the low 24 limbs are below `2^82` and the top limb is
`2^79 + t` with `0 ≤ t < 2^79`, the number is in `[2^2047, 2^2048)` — the bound every
product and quotient estimate in the chain uses, and what `n_top = 2^79` pins. -/
theorem n_bits (x : ℕ → ℤ) (t : ℤ) (hlo : ∀ j < 24, 0 ≤ x j ∧ x j < 2 ^ 82)
    (h24 : x 24 = 2 ^ 79 + t) (ht0 : 0 ≤ t) (ht : t < 2 ^ 79) :
    2 ^ 2047 ≤ val x ∧ val x < 2 ^ 2048 := by
  have hW : W = 2 ^ 82 := rfl
  have hWpos : 0 < W := by rw [hW]; norm_num
  have hW24 : W ^ 24 = 2 ^ 1968 := by rw [hW, ← pow_mul]
  have hsplit : val x = (∑ i ∈ Finset.range 24, x i * W ^ i) + x 24 * W ^ 24 := by
    rw [val, Finset.sum_range_succ]
  have hterm : ∀ i ∈ Finset.range 24, x i * W ^ i ≤ (W - 1) * W ^ i := by
    intro i hi
    have hmem := Finset.mem_range.mp hi
    have hx := hlo i hmem
    have hle : x i ≤ W - 1 := by
      rw [hW]
      omega
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hlow : ∑ i ∈ Finset.range 24, x i * W ^ i ≤ W ^ 24 - 1 := by
    calc ∑ i ∈ Finset.range 24, x i * W ^ i
        ≤ ∑ i ∈ Finset.range 24, (W - 1) * W ^ i := Finset.sum_le_sum hterm
      _ = W ^ 24 - 1 := geom_sum W 24
  have hnonneg : 0 ≤ ∑ i ∈ Finset.range 24, x i * W ^ i :=
    Finset.sum_nonneg fun i hi => by
      have hx := hlo i (Finset.mem_range.mp hi)
      exact mul_nonneg hx.1 (by positivity)
  have hx24lo : 2 ^ 79 ≤ x 24 := by rw [h24]; omega
  have hx24hi : x 24 ≤ 2 ^ 80 - 1 := by rw [h24]; omega
  have h2047 : (2 : ℤ) ^ 79 * 2 ^ 1968 = (2 : ℤ) ^ 2047 := by rw [← pow_add]
  have h2048 : (2 : ℤ) ^ 80 * 2 ^ 1968 = (2 : ℤ) ^ 2048 := by rw [← pow_add]
  constructor
  · rw [hsplit, hW24]
    have hx : (2 : ℤ) ^ 2047 ≤ x 24 * 2 ^ 1968 := by
      rw [← h2047]
      exact mul_le_mul_of_nonneg_right hx24lo (by positivity)
    calc (2 : ℤ) ^ 2047 = (2 : ℤ) ^ 79 * 2 ^ 1968 := h2047.symm
      _ ≤ x 24 * 2 ^ 1968 := hx
      _ ≤ (∑ i ∈ Finset.range 24, x i * W ^ i) + x 24 * 2 ^ 1968 :=
          le_add_of_nonneg_left hnonneg
  · rw [hsplit, hW24]
    have hlow' : (∑ i ∈ Finset.range 24, x i * W ^ i) ≤ (2 : ℤ) ^ 1968 - 1 := by
      rw [← hW24]
      exact hlow
    have h1 : x 24 * (2 : ℤ) ^ 1968 ≤ ((2 : ℤ) ^ 80 - 1) * 2 ^ 1968 :=
      mul_le_mul_of_nonneg_right hx24hi (by positivity)
    have h3 : ((2 : ℤ) ^ 1968 - 1) + ((2 : ℤ) ^ 80 - 1) * 2 ^ 1968 =
        (2 : ℤ) ^ 2048 - 1 := by
      rw [← h2048]
      ring
    calc (∑ i ∈ Finset.range 24, x i * W ^ i) + x 24 * (2 : ℤ) ^ 1968
        ≤ ((2 : ℤ) ^ 1968 - 1) + ((2 : ℤ) ^ 80 - 1) * 2 ^ 1968 :=
          add_le_add hlow' h1
      _ = (2 : ℤ) ^ 2048 - 1 := h3
      _ < (2 : ℤ) ^ 2048 := by
        have : (0 : ℤ) < 2 ^ 2048 := by positivity
        linarith

/-- **The 16 squarings.** A step that is congruent to `a ↦ a·a` keeps the
congruence: `step` applied `k` times to `a` is `a^(2^k)`. -/
theorem squarings (n : ℤ) (step : ℤ → ℤ) (hstep : ∀ a, step a ≡ a * a [ZMOD n]) :
    ∀ (k : ℕ) (a : ℤ), Nat.iterate step k a ≡ a ^ (2 ^ k) [ZMOD n]
  | 0, a => by simp
  | k + 1, a => by
    have ih := squarings n step hstep k a
    have h1 : step (Nat.iterate step k a) ≡
        (Nat.iterate step k a) * (Nat.iterate step k a) [ZMOD n] := hstep _
    have h2 : (Nat.iterate step k a) * (Nat.iterate step k a) ≡
        a ^ (2 ^ k) * a ^ (2 ^ k) [ZMOD n] := ih.mul ih
    have h3 : a ^ (2 ^ k) * a ^ (2 ^ k) = a ^ (2 ^ (k + 1)) := by
      rw [← pow_add]
      congr 1
      rw [pow_succ]
      ring
    calc Nat.iterate step (k + 1) a = step (Nat.iterate step k a) := by
          rw [Function.iterate_succ_apply']
      _ ≡ (Nat.iterate step k a) * (Nat.iterate step k a) [ZMOD n] := h1
      _ ≡ a ^ (2 ^ k) * a ^ (2 ^ k) [ZMOD n] := h2
      _ = a ^ (2 ^ (k + 1)) := h3

/-- **The chain's congruence.** `k` squarings of `sig` (`step a ≡ a·a`) followed by the
terminal multiply `acc·sig = q·n + em` give `em ≡ sig^(2^k+1) (mod n)`; at
`k = 16` that is RSA verification with `e = 65537`. -/
theorem chain (n sig em q : ℤ) (step : ℤ → ℤ) (k : ℕ)
    (hstep : ∀ a, step a ≡ a * a [ZMOD n])
    (hfinal : Nat.iterate step k sig * sig = q * n + em) :
    em ≡ sig ^ (2 ^ k + 1) [ZMOD n] := by
  have hsq := squarings n step hstep k sig
  have hmul : Nat.iterate step k sig * sig ≡ sig ^ (2 ^ k) * sig [ZMOD n] :=
    hsq.mul_right sig
  have hright : q * n + em ≡ em [ZMOD n] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-q, by ring⟩
  calc em ≡ q * n + em [ZMOD n] := hright.symm
    _ = Nat.iterate step k sig * sig := hfinal.symm
    _ ≡ sig ^ (2 ^ k) * sig [ZMOD n] := hmul
    _ = sig ^ (2 ^ k + 1) := by rw [pow_succ]

end Xark.Rsa.Chain
