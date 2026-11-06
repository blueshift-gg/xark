/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.DoubleAdd
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The odd signed recoding of `ecdsa_verify_packed`'s chain

From `O`, `n` fused steps (`Formal/EcK1Check.lean`'s `EcDoubleAddK1Check`) with all-odd signed
digits `±1` (`2·bit − 1`) over the 8-entry table `P₁ + σ(e₂)P₂ + σ(e₃)P₃ + σ(e₄)P₄` (entry
`e` read at `eⱼ = c₁ ⊕ cⱼ`, negated when `c₁ = 0`) reach `2ⁿ·O + Σₘ kₘ·Pₘ` with
`kₘ = 2cₘ − (2ⁿ − 1)`, and the digits of each odd `|k| < 2ⁿ` are unique (recoding
canonicity).
-/

/-! ### The odd signed recoding -/

namespace Xark.OddRecode

open Finset

variable {G : Type*} [AddCommGroup G]

/-- The accumulator of a chain of fused steps (`DoubleAdd.accum`) in closed form: from `A`,
`n` steps with addends `S 0, S 1, …` (most significant first) reach
`2ⁿ·A + Σⱼ 2^(n−1−j)·S j`. -/
theorem accum_eq (A : G) (S : ℕ → G) (n : ℕ) :
    DoubleAdd.accum A S n = (2 ^ n : ℤ) • A + ∑ j ∈ range n, (2 ^ (n - 1 - j) : ℤ) • S j := by
  induction n with
  | zero => simp [DoubleAdd.accum]
  | succ n ih =>
    have key : ∑ j ∈ range n, (2 ^ (n + 1 - 1 - j) : ℤ) • S j =
        (2 : ℤ) • ∑ j ∈ range n, (2 ^ (n - 1 - j) : ℤ) • S j := by
      rw [smul_sum]
      refine sum_congr rfl fun j hj => ?_
      rw [smul_smul, ← pow_succ']
      congr 2
      have := mem_range.mp hj
      omega
    rw [DoubleAdd.accum, ih, sum_range_succ, key]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_smul]
    rw [pow_succ]
    module

/-- A digit's sign: `σ(b) = 2b − 1`. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- `Σⱼ 2^(n−1−j) = 2ⁿ − 1`. -/
theorem geom (n : ℕ) : ∑ j ∈ range n, (2 : ℤ) ^ (n - 1 - j) = 2 ^ n - 1 := by
  rw [sum_range_reflect (fun j => (2 : ℤ) ^ j) n]
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- The all-odd signed digits of `c` (bit `j` of `c`, most significant first) spell
`2c − (2ⁿ − 1)`. -/
theorem digits_eq (c : ℕ → Bool) (n : ℕ) :
    ∑ j ∈ range n, (2 ^ (n - 1 - j) : ℤ) * sgn (c j) =
      2 * ∑ j ∈ range n, (2 ^ (n - 1 - j) : ℤ) * (if c j then 1 else 0) - (2 ^ n - 1) := by
  have h : ∀ j ∈ range n, (2 ^ (n - 1 - j) : ℤ) * sgn (c j) =
      2 * ((2 ^ (n - 1 - j) : ℤ) * (if c j then 1 else 0)) - 2 ^ (n - 1 - j) := fun j _ => by
    cases c j <;> simp [sgn]
    ring
  rw [sum_congr rfl h, sum_sub_distrib, ← mul_sum, geom]

/-- **Recoding canonicity.** Each odd `k` with `|k| < 2ⁿ⁺¹` is `2c − (2ⁿ⁺¹ − 1)` for
exactly one `c < 2ⁿ⁺¹` (so, by `Gadgets.bits_unique`, for exactly one digit vector), and
every `c < 2ⁿ⁺¹` gives such a `k`. -/
theorem odd_recode (n : ℕ) (k : ℤ) :
    (Odd k ∧ |k| < 2 ^ (n + 1)) ↔
      ∃! c : ℤ, 0 ≤ c ∧ c < 2 ^ (n + 1) ∧ k = 2 * c - (2 ^ (n + 1) - 1) := by
  have hp : (0 : ℤ) < 2 ^ n := by positivity
  rw [pow_succ]
  constructor
  · rintro ⟨⟨m, rfl⟩, hk⟩
    rw [abs_lt] at hk
    exact ⟨m + 2 ^ n, ⟨by omega, by omega, by ring⟩, fun c ⟨_, _, hc⟩ => by omega⟩
  · rintro ⟨c, ⟨h0, h1, rfl⟩, -⟩
    exact ⟨⟨c - 2 ^ n, by ring⟩, by rw [abs_lt]; constructor <;> omega⟩

/-- **The table.** Entry `e = (e₂, e₃, e₄)` is `A_{e₂} + σ'(e₃)·B_{e₃ ⊕ e₄}` with
`A_e = P₁ + σ'(e)P₂`, `B_e = P₃ + σ'(e)P₄`, `σ'(e) = 1 − 2e` (built from two adds and
eight table adds), and the digit vector `c` adds `σ(c₁)` times entry `(c₁⊕c₂, c₁⊕c₃,
c₁⊕c₄)`: that is `Σₘ σ(cₘ)·Pₘ`. -/
theorem table_entry (P₁ P₂ P₃ P₄ : G) (c₁ c₂ c₃ c₄ : Bool) :
    let s' : Bool → ℤ := fun e => if e then -1 else 1
    let A : Bool → G := fun e => P₁ + s' e • P₂
    let B : Bool → G := fun e => P₃ + s' e • P₄
    sgn c₁ • (A (xor c₁ c₂) + s' (xor c₁ c₃) • B (xor (xor c₁ c₃) (xor c₁ c₄))) =
      sgn c₁ • P₁ + sgn c₂ • P₂ + sgn c₃ • P₃ + sgn c₄ • P₄ := by
  cases c₁ <;> cases c₂ <;> cases c₃ <;> cases c₄ <;> simp [sgn] <;> abel

/-- **What the chain computes.** If step `j` adds `Σₘ σ(c m j)·P m` (four bases) from
`O`, after `n` steps the accumulator is `2ⁿ·O + Σₘ kₘ·P m` with
`kₘ = 2cₘ − (2ⁿ − 1)`, `cₘ = Σⱼ 2^(n−1−j)·[c m j]`. -/
theorem chain_value (O : G) (P : Fin 4 → G) (c : Fin 4 → ℕ → Bool) (n : ℕ) :
    DoubleAdd.accum O (fun j => ∑ m, sgn (c m j) • P m) n =
      (2 ^ n : ℤ) • O + ∑ m, (2 * ∑ j ∈ range n, (2 ^ (n - 1 - j) : ℤ) *
        (if c m j then 1 else 0) - (2 ^ n - 1)) • P m := by
  rw [accum_eq]
  congr 1
  simp_rw [smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [← digits_eq, sum_smul]

end Xark.OddRecode
