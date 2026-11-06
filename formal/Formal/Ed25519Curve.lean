/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Ed25519Primes
import Formal.Edwards
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set
import Mathlib.FieldTheory.Finite.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The Ed25519 curve over `ZMod p`: completeness of the affine law, the torsion test

`p = 2²⁵⁵ − 19` is prime (`Formal/Ed25519Primes.lean`), so `ZMod p` is a field.

* `d_nonsquare`: Ed25519's `d` is not a square mod `p` (Euler's criterion, by `Pratt.powMod`).
* `complete`: on two points of `−x² + y² = 1 + d·x²·y²`, `1 ± d·x₁x₂y₁y₂ ≠ 0`
  (Bernstein–Birkner–Joye–Lange–Peters, *Twisted Edwards curves*, AFRICACRYPT 2008,
  Thm 3.3, through `X = √−1·x`). So `Xark.EdwardsComplete d` holds and the addition and
  doubling formulas the verifier certifies are defined everywhere on the curve.
* `torsion_iff`: on the curve, `x·y·(x² + y²) = 0` iff three doublings reach `(0, 1)`:
  the points of order dividing 8 (the verifier's cofactor test, `ed_torsion_check`).
-/

namespace Xark.Ed25519

/-- `p = 2²⁵⁵ − 19`. -/
abbrev p : ℕ := 57896044618658097711785492504343953926634992332820282019728792003956564819949

theorem p_eq : p = 2 ^ 255 - 19 := by norm_num

instance : Fact (Nat.Prime p) :=
  ⟨Pratt.prime_57896044618658097711785492504343953926634992332820282019728792003956564819949⟩

abbrev Fp := ZMod p

/-- `d = −121665/121666 mod p`. -/
def dN : ℕ := 37095705934669439343138083508754565189542113879843219016388785533085940283555
abbrev d : Fp := (dN : Fp)

theorem d_def : d * 121666 = -121665 := by decide

/-- `√−1 = 2^((p−1)/4) mod p`. -/
def iN : ℕ := 19681161376707505956807079304988542015446066515923890162744021073123829784752
abbrev i : Fp := (iN : Fp)

theorem i_sq : i * i = -1 := by decide

theorem euler_d : d ^ ((p - 1) / 2) = -1 := by
  rw [← Pratt.powMod_cast dN _ p (by norm_num)]
  decide +kernel

/-- **`d` is not a square mod `p`.** -/
theorem d_nonsquare : ∀ r : Fp, r * r ≠ d := by
  intro r hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : (0 : Fp) = d := by simpa using hr
    exact absurd this (by decide)
  have h1 : r ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hr0
  have h2 : r ^ (p - 1) = d ^ ((p - 1) / 2) := by
    rw [← hr, ← sq, ← pow_mul]
    congr 1
  rw [h2, euler_d] at h1
  exact absurd h1 (by decide)

/-- The untwisted core of BBJLP Thm 3.3: on `X² + y² = 1 + D·X²·y²` with `D` not a square,
`(D·X₁X₂y₁y₂)² ≠ 1`. Stated over `Fp`, where `2 ≠ 0`. -/
theorem untwisted_complete (D : Fp) (hD : ∀ r : Fp, r * r ≠ D)
    (X1 y1 X2 y2 : Fp) (h1 : X1 ^ 2 + y1 ^ 2 = 1 + D * X1 ^ 2 * y1 ^ 2)
    (h2 : X2 ^ 2 + y2 ^ 2 = 1 + D * X2 ^ 2 * y2 ^ 2) :
    (D * X1 * X2 * y1 * y2) ^ 2 ≠ 1 := by
  intro he
  set e := D * X1 * X2 * y1 * y2 with he_def
  have hxy : X1 * y1 ≠ 0 := by
    intro h0
    have : e = 0 := by rw [he_def]; linear_combination D * X2 * y2 * h0
    rw [this] at he; norm_num at he
  have hX2 : X2 ≠ 0 := by
    intro h0
    have : e = 0 := by rw [he_def, h0]; ring
    rw [this] at he; norm_num at he
  have hp : (X1 + e * y1) ^ 2 = D * (X1 * y1) ^ 2 * (X2 + y2) ^ 2 := by
    rw [he_def] at he ⊢
    linear_combination (y1 ^ 2 - 1) * he + h1 - D * X1 ^ 2 * y1 ^ 2 * h2
  have hm : (X1 - e * y1) ^ 2 = D * (X1 * y1) ^ 2 * (X2 - y2) ^ 2 := by
    rw [he_def] at he ⊢
    linear_combination (y1 ^ 2 - 1) * he + h1 - D * X1 ^ 2 * y1 ^ 2 * h2
  by_cases hs : X2 + y2 = 0
  · have hd : X2 - y2 ≠ 0 := by
      intro h0
      have h2x : (2 : Fp) * X2 = 0 := by linear_combination h0 + hs
      exact hX2 ((mul_eq_zero.mp h2x).resolve_left (by decide))
    have hn : X1 * y1 * (X2 - y2) ≠ 0 := mul_ne_zero hxy hd
    apply hD ((X1 - e * y1) / (X1 * y1 * (X2 - y2)))
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hn hn)]
    linear_combination hm
  · have hn : X1 * y1 * (X2 + y2) ≠ 0 := mul_ne_zero hxy hs
    apply hD ((X1 + e * y1) / (X1 * y1 * (X2 + y2)))
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hn hn)]
    linear_combination hp

/-- **Completeness of the twisted law** (BBJLP Thm 3.3 for `a = −1`, `X = √−1·x`):
both denominators are nonzero on any two curve points. -/
theorem complete : EdwardsComplete d := by
  intro x1 y1 x2 y2 h1 h2
  unfold OnEdwards at h1 h2
  have hD : ∀ r : Fp, r * r ≠ -d := fun r hr => d_nonsquare (i * r) (by
    linear_combination r ^ 2 * i_sq - hr)
  have hc := untwisted_complete (-d) hD (i * x1) y1 (i * x2) y2
    (by linear_combination h1 + (x1 ^ 2 + d * x1 ^ 2 * y1 ^ 2) * i_sq)
    (by linear_combination h2 + (x2 ^ 2 + d * x2 ^ 2 * y2 ^ 2) * i_sq)
  have he : (-d) * (i * x1) * (i * x2) * y1 * y2 = d * x1 * x2 * y1 * y2 := by
    linear_combination (-d * x1 * x2 * y1 * y2) * i_sq
  rw [he] at hc
  constructor
  · intro h0
    apply hc
    linear_combination (d * x1 * x2 * y1 * y2 - 1) * h0
  · intro h0
    apply hc
    linear_combination (-(d * x1 * x2 * y1 * y2) - 1) * h0

/-- The doubling denominators: on the curve `y² − x² = 1 + d·x²y²` and
`2 − y² + x² = 1 − d·x²y²`, both nonzero. -/
theorem double_dens (x y : Fp) (h : OnEdwards d x y) :
    y ^ 2 - x ^ 2 ≠ 0 ∧ 2 - y ^ 2 + x ^ 2 ≠ 0 := by
  obtain ⟨h1, h2⟩ := complete x y x y h h
  unfold OnEdwards at h
  exact ⟨fun h0 => h1 (by linear_combination h0 - h), fun h0 => h2 (by linear_combination h0 + h)⟩

/-- Affine doubling. -/
noncomputable def dbl (P : Fp × Fp) : Fp × Fp :=
  (2 * P.1 * P.2 / (P.2 ^ 2 - P.1 ^ 2), (P.1 ^ 2 + P.2 ^ 2) / (2 - P.2 ^ 2 + P.1 ^ 2))

/-- Doubling stays on the curve (`edwards_add_on_curve` with both points `P`). -/
theorem dbl_on (P : Fp × Fp) (h : OnEdwards d P.1 P.2) : OnEdwards d (dbl P).1 (dbl P).2 := by
  obtain ⟨hn1, hn2⟩ := double_dens P.1 P.2 h
  have hc := h
  unfold OnEdwards at hc
  refine edwards_add_on_curve d P.1 P.2 P.1 P.2 _ _ h h ?_ ?_ ?_ ?_
  · simp only [dbl]; rw [div_mul_eq_mul_div, div_eq_iff hn1]
    linear_combination (-(2 * P.1 * P.2)) * hc
  · simp only [dbl]; rw [div_mul_eq_mul_div, div_eq_iff hn2]
    linear_combination (P.1 ^ 2 + P.2 ^ 2) * hc
  · exact (complete _ _ _ _ h h).1
  · exact (complete _ _ _ _ h h).2

/-- On the curve, doubling gives the identity `(0, 1)` iff `x = 0`. -/
theorem dbl_eq_O (P : Fp × Fp) (h : OnEdwards d P.1 P.2) : dbl P = (0, 1) ↔ P.1 = 0 := by
  obtain ⟨hn1, hn2⟩ := double_dens P.1 P.2 h
  have hc := h
  unfold OnEdwards at hc
  constructor
  · intro he
    have hx : 2 * P.1 * P.2 / (P.2 ^ 2 - P.1 ^ 2) = 0 := congrArg Prod.fst he
    have hy : (P.1 ^ 2 + P.2 ^ 2) / (2 - P.2 ^ 2 + P.1 ^ 2) = 1 := congrArg Prod.snd he
    rw [div_eq_zero_iff] at hx
    rw [div_eq_one_iff_eq hn2] at hy
    rcases hx with hx | hx
    · rcases mul_eq_zero.mp hx with hx | hx
      · rcases mul_eq_zero.mp hx with hx | hx
        · exact absurd hx (by decide)
        · exact hx
      · exfalso; rw [hx] at hy; apply (show (2 : Fp) ≠ 0 by decide)
        linear_combination -hy
    · exact absurd hx hn1
  · intro hx
    have hy : P.2 ^ 2 = 1 := by rw [hx] at hc; linear_combination hc
    simp only [dbl, hx]
    ext
    · simp
    · simp only; rw [div_eq_one_iff_eq (by rw [hy]; norm_num)]; rw [hy]; ring

/-- On the curve, `dbl P` has `x = 0` iff `x·y = 0`. -/
theorem dbl_x_eq_zero (P : Fp × Fp) (h : OnEdwards d P.1 P.2) :
    (dbl P).1 = 0 ↔ P.1 * P.2 = 0 := by
  obtain ⟨hn1, -⟩ := double_dens P.1 P.2 h
  simp only [dbl, div_eq_zero_iff, hn1, or_false]
  rw [mul_assoc, mul_eq_zero, or_iff_right (by decide : (2 : Fp) ≠ 0)]

/-- On the curve, `dbl P` has `x·y = 0` iff `x·y·(x² + y²) = 0`. -/
theorem dbl_xy_eq_zero (P : Fp × Fp) (h : OnEdwards d P.1 P.2) :
    (dbl P).1 * (dbl P).2 = 0 ↔ P.1 * P.2 * (P.1 ^ 2 + P.2 ^ 2) = 0 := by
  obtain ⟨hn1, hn2⟩ := double_dens P.1 P.2 h
  simp only [dbl]
  rw [div_mul_div_comm, div_eq_zero_iff, or_iff_left (mul_ne_zero hn1 hn2)]
  rw [show 2 * P.1 * P.2 * (P.1 ^ 2 + P.2 ^ 2) = 2 * (P.1 * P.2 * (P.1 ^ 2 + P.2 ^ 2)) by ring,
    mul_eq_zero, or_iff_right (by decide : (2 : Fp) ≠ 0)]

/-- **The torsion test.** On the curve, three doublings reach the identity iff
`x·y·(x² + y²) = 0`. -/
theorem torsion_iff (P : Fp × Fp) (h : OnEdwards d P.1 P.2) :
    dbl (dbl (dbl P)) = (0, 1) ↔ P.1 * P.2 * (P.1 ^ 2 + P.2 ^ 2) = 0 := by
  have h2 := dbl_on P h
  have h4 := dbl_on (dbl P) h2
  rw [dbl_eq_O _ h4, dbl_x_eq_zero _ h2, dbl_xy_eq_zero _ h]

end Xark.Ed25519
