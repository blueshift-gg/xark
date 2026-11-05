/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.DoubleAdd
import Formal.Secp256r1Group

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# secp256r1 (P-256) incomplete add by certificates: the curve facts

`DoubleAdd`'s fused step needs a short Weierstrass curve with no affine point of order 2.
For P-256 (`y² = x³ − 3x + b`) that is: `f = X³ − 3X + b` has no root mod `p`. The kernel
computes `r = Xᵖ mod f` by square-and-multiply in `F_p[X]/(f)` (`powF`); a root `x` would
satisfy `r(x) = xᵖ = x`, and the Bézout certificate `u·f + v·(r − X) = 1` (checked coefficient
by coefficient) rules that out (`noTwoTorsion`).
-/

namespace Xark.EcR1

open WeierstrassCurve WeierstrassCurve.Affine

/-- secp256r1's base field. -/
abbrev K := ZMod secp256r1_p

/-- Multiplication in `K[X]/(X³ − 3X + b)` on coefficient triples. -/
def mul3 (u v : K × K × K) : K × K × K :=
  (u.1 * v.1 - secp256r1_b * (u.2.1 * v.2.2 + u.2.2 * v.2.1),
   u.1 * v.2.1 + u.2.1 * v.1 + 3 * (u.2.1 * v.2.2 + u.2.2 * v.2.1) - secp256r1_b * (u.2.2 * v.2.2),
   u.1 * v.2.2 + u.2.1 * v.2.1 + u.2.2 * v.1 + 3 * (u.2.2 * v.2.2))

/-- `uⁿ` by square-and-multiply, `f` levels of fuel (enough for `n < 2^f`). -/
def powF (u : K × K × K) : ℕ → ℕ → K × K × K
  | 0, _ => (1, 0, 0)
  | f + 1, n => if n = 0 then (1, 0, 0) else
      match n % 2 with
      | 0 => mul3 (powF u f (n / 2)) (powF u f (n / 2))
      | _ => mul3 (mul3 (powF u f (n / 2)) (powF u f (n / 2))) u

/-- A triple at `x`. -/
def ev (u : K × K × K) (x : K) : K := u.1 + u.2.1 * x + u.2.2 * x ^ 2

theorem ev_mul {x : K} (hx : x ^ 3 - 3 * x + secp256r1_b = 0) (u v : K × K × K) :
    ev (mul3 u v) x = ev u x * ev v x := by
  simp only [ev, mul3]
  linear_combination (-(u.2.1 * v.2.2 + u.2.2 * v.2.1 + u.2.2 * v.2.2 * x)) * hx

theorem ev_pow {x : K} (hx : x ^ 3 - 3 * x + secp256r1_b = 0) (u : K × K × K) :
    ∀ f n, n < 2 ^ f → ev (powF u f n) x = ev u x ^ n
  | 0, n, hn => by
    have : n = 0 := by simpa using hn
    subst this; simp [powF, ev]
  | f + 1, n, hn => by
    have hlt : n / 2 < 2 ^ f := by
      have := pow_succ 2 f; generalize 2 ^ f = m at *; omega
    have ih := ev_pow hx u f (n / 2) hlt
    unfold powF
    split_ifs with h0
    · subst h0; simp [ev]
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · simp only [h, ev_mul hx, ih, ← pow_add]; congr 1; omega
      · simp only [h, ev_mul hx, ih, ← pow_add, ← pow_succ]; congr 1; omega

/-- `Xᵖ mod f`. -/
def R0 : K := 66434390973925144466073271287821796038003695194169110494110089305650096453661
def R1 : K := 12402202686218762177567235911775779164004716598278868847786114277539554646092
def R2 : K := 24678849118215552148312087830792888746041224110560601850711771001608500700145
/-- The Bézout certificate `u·f + v·(r − X) = 1`. -/
def U0 : K := 107286402702237026811154678719514266289498743974321057492273529440068429825344
def U1 : K := 6389611969556882025875921584714237703390037729321797349080302270353162149340
def V0 : K := 76626890310466861426869089647039036757962535851890885406097439786770458211455
def V1 : K := 74462945259064871768191128030512052509059297803194871526163573358218695456204
def V2 : K := 34768139465301476436978405170953382516735956999154666452188405812258086013549

theorem powF_val : powF (0, 1, 0) 256 secp256r1_p = (R0, R1, R2) := by decide +kernel

theorem bezout : U0 * secp256r1_b + V0 * R0 = 1 ∧
    U1 * secp256r1_b - 3 * U0 + V0 * (R1 - 1) + V1 * R0 = 0 ∧
    -3 * U1 + V0 * R2 + V1 * (R1 - 1) + V2 * R0 = 0 ∧
    U0 + V1 * R2 + V2 * (R1 - 1) = 0 ∧ U1 + V2 * R2 = 0 := by decide +kernel

/-- **No 2-torsion**: no affine point of P-256 has `y = 0`. -/
theorem noTwoTorsion (x : K) : ¬secp256r1Curve.Equation x 0 := by
  intro h
  rw [equation_iff] at h
  have h' : (0 : K) ^ 2 + 0 * x * 0 + 0 * 0 = x ^ 3 + 0 * x ^ 2 + (-3) * x + secp256r1_b := h
  have hx : x ^ 3 - 3 * x + secp256r1_b = 0 := by linear_combination -h'
  have hp := ev_pow hx (0, 1, 0) 256 secp256r1_p (by norm_num [secp256r1_p])
  rw [powF_val] at hp
  simp only [ev, zero_add, one_mul, zero_mul, add_zero] at hp
  rw [ZMod.pow_card] at hp
  have hg : R0 + (R1 - 1) * x + R2 * x ^ 2 = 0 := by linear_combination hp
  obtain ⟨c0, c1, c2, c3, c4⟩ := bezout
  have : (1 : K) = 0 := by
    linear_combination (U0 + U1 * x) * hx + (V0 + V1 * x + V2 * x ^ 2) * hg - c0 - x * c1 -
      x ^ 2 * c2 - x ^ 3 * c3 - x ^ 4 * c4
  exact one_ne_zero this

theorem p_eq : secp256r1_p =
    115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  norm_num [secp256r1_p]

theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 2 secp256r1_p).mp (by exact_mod_cast h)
  rw [p_eq] at this
  norm_num at this

/-- P-256 is a short Weierstrass curve with no 2-torsion: `DoubleAdd`'s setting. -/
theorem short : DoubleAdd.Short secp256r1Curve :=
  ⟨rfl, rfl, rfl, two_ne_zero, noTwoTorsion⟩

/-- The guard `w·(x_Q − x_P) = 1` rules out `x_P = x_Q`. -/
theorem guard_ne {px qx w : K} (guard : w * (qx - px) = 1) : px ≠ qx := by
  rintro rfl
  rw [sub_self, mul_zero] at guard
  exact zero_ne_one guard

/-- **Soundness of the add certificates.** On affine `P`, `Q`, the guard, slope, `x₃` and
`y₃` certificates force `(x₃, y₃)` to be the affine point `P + Q`. -/
theorem add_sound {px py qx qy w l x3 y3 : K} (hP : secp256r1Curve.Nonsingular px py)
    (hQ : secp256r1Curve.Nonsingular qx qy) (guard : w * (qx - px) = 1)
    (hl : l * (qx - px) = qy - py) (hx3 : l ^ 2 = x3 + px + qx)
    (hy3 : l * (px - x3) = y3 + py) :
    ∃ h : secp256r1Curve.Nonsingular x3 y3, Point.some _ _ hP + Point.some _ _ hQ =
      Point.some _ _ h :=
  DoubleAdd.add_of_slope (l := l) (x₃ := x3) (y₃ := y3) short hP hQ (guard_ne guard)
    (by linear_combination -hl) (by linear_combination -hx3) (by linear_combination -hy3)

end Xark.EcR1
