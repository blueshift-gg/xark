/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.DoubleAdd
import Formal.Secp256k1Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.FieldTheory.Finite.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# secp256k1 incomplete add by certificates

`xark_bignum::ec_add_k1` checks each field relation with one
`mul_cert_k1` (`Formal/MulCertK1.lean`: its rows force `a·b ≡ t (mod p)`), and range-check
the hinted `w`, `λ`, `x₃`, `y₃` below `2⁶⁴`. Read mod `p`, the certificates are:

```text
  add:     w·(x_Q − x_P) = 1        the chord guard
           λ·(x_Q − x_P) = y_Q − y_P
           λ² = x₃ + x_P + x_Q
           λ·(x_P − x₃) = y₃ + y_P
```

(each difference carries the bias `8p ≡ 0`, so its limbs are non-negative).

* `add_sound`: on affine `P`, `Q`, the four add certificates force `(x₃, y₃)` to be the
  affine point `P + Q`.
* `slope_free_without_guard`: without the guard, `x_P = x_Q` lets the slope certificate
  hold for every `λ` and the chord formulas give different `x₃` (bug checklist 1); the
  guard rules that case out (`guard_ne`). With unreduced limbs this covers every
  `x_Q − x_P ∈ {0, p, 2p, …}`: the certificate is a congruence mod `p`.
-/

namespace Xark.EcK1

open WeierstrassCurve WeierstrassCurve.Affine

/-- secp256k1's base field. -/
abbrev K := ZMod secp256k1_p

theorem p_eq : secp256k1_p =
    115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [secp256k1_p]

theorem seven_ne_zero : (7 : K) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 7 secp256k1_p).mp (by exact_mod_cast h)
  rw [p_eq] at this
  norm_num at this

/-- `−7` is not a cube mod `p`: `(−7)^((p − 1)/3) ≠ 1`, computed by the kernel. -/
theorem neg_seven_not_cube : Pratt.powMod (secp256k1_p - 7) ((secp256k1_p - 1) / 3)
    secp256k1_p % secp256k1_p ≠ 1 := by
  rw [p_eq]; decide +kernel

/-- **No 2-torsion**: no affine point of secp256k1 has `y = 0`. -/
theorem noTwoTorsion (x : K) : ¬secp256k1Curve.Equation x 0 := by
  intro h
  rw [equation_iff] at h
  simp only [secp256k1Curve_a₁, secp256k1Curve_a₂, secp256k1Curve_a₃, secp256k1Curve_a₄,
    secp256k1Curve_a₆] at h
  have hx3 : x ^ 3 = -7 := by linear_combination -h
  have hx : x ≠ 0 := by
    rintro rfl
    apply seven_ne_zero
    linear_combination hx3
  have hdvd : 3 * ((secp256k1_p - 1) / 3) = secp256k1_p - 1 := by rw [p_eq]
  have hf := ZMod.pow_card_sub_one_eq_one hx
  rw [← hdvd, pow_mul, hx3] at hf
  have hcast : ((secp256k1_p - 7 : ℕ) : K) = -7 := by
    rw [Nat.cast_sub (by rw [p_eq]; norm_num), ZMod.natCast_self]; ring
  have he : (secp256k1_p - 1) / 3 < 2 ^ 256 := by rw [p_eq]; norm_num
  rw [← hcast, ← Pratt.powMod_cast _ _ _ he] at hf
  have := (ZMod.natCast_eq_natCast_iff' _ 1 secp256k1_p).mp (by exact_mod_cast hf)
  rw [Nat.one_mod_eq_one.mpr (by rw [p_eq]; norm_num)] at this
  exact neg_seven_not_cube this

theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 2 secp256k1_p).mp (by exact_mod_cast h)
  rw [p_eq] at this
  norm_num at this

/-- secp256k1 is a short Weierstrass curve with no 2-torsion: `DoubleAdd`'s setting. -/
theorem short : DoubleAdd.Short secp256k1Curve :=
  ⟨rfl, rfl, rfl, two_ne_zero, noTwoTorsion⟩

/-- The guard `w·(x_Q − x_P) = 1` rules out `x_P = x_Q`. -/
theorem guard_ne {px qx w : K} (guard : w * (qx - px) = 1) : px ≠ qx := by
  rintro rfl
  rw [sub_self, mul_zero] at guard
  exact zero_ne_one guard

/-- **Soundness of the add certificates.** On affine `P`, `Q`, the guard, slope, `x₃` and
`y₃` certificates force `(x₃, y₃)` to be the affine point `P + Q`. -/
theorem add_sound {px py qx qy w l x3 y3 : K} (hP : secp256k1Curve.Nonsingular px py)
    (hQ : secp256k1Curve.Nonsingular qx qy) (guard : w * (qx - px) = 1)
    (hl : l * (qx - px) = qy - py) (hx3 : l ^ 2 = x3 + px + qx)
    (hy3 : l * (px - x3) = y3 + py) :
    ∃ h : secp256k1Curve.Nonsingular x3 y3, Point.some _ _ hP + Point.some _ _ hQ =
      Point.some _ _ h :=
  DoubleAdd.add_of_slope (l := l) (x₃ := x3) (y₃ := y3) short hP hQ (guard_ne guard) (by linear_combination -hl)
    (by linear_combination -hx3) (by linear_combination -hy3)

/-- **The guard is necessary.** At `x_P = x_Q` (here `P = Q`) the slope certificate holds
for every `λ`, and the chord formulas then give different `x₃` for `λ = 0` and `λ = 1`:
without `w·(x_Q − x_P) = 1` the add's output would be the prover's choice. -/
theorem slope_free_without_guard (px py : K) :
    (∀ l : K, l * (px - px) = py - py) ∧
      (0 : K) ^ 2 - px - px ≠ (1 : K) ^ 2 - px - px := by
  refine ⟨fun l => by ring, fun h => ?_⟩
  have : (0 : K) = 1 := by linear_combination h
  exact zero_ne_one this

end Xark.EcK1
