/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib
import Formal.CurvePrimes

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# secp256k1 point group as a concrete `AddCommGroup`

The actual secp256k1 point group `{(x, y) : ZMod p × ZMod p // y² = x³ + 7} ∪ {∞}`
as an `AddCommGroup`: the curve the secp256k1 template proofs (`Formal.EcK1`) work in.

## Strategy: reuse mathlib's `WeierstrassCurve.Affine.Point`

Mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` defines

    inductive WeierstrassCurve.Affine.Point (W : Affine F)
      | zero
      | some (x y : F) (h : W.Nonsingular x y)

over an arbitrary `[Field F]`, equips it with `Zero`, `Neg`, `Add`, and
proves `instance : AddCommGroup W.Point` via the class-group embedding
(`WeierstrassCurve.Affine.Point.toClass`). Associativity — the algebraic
heart of the curve group law — is the standard textbook argument, mechanised
by mathlib via the ideal-class-group injection of an affine Weierstrass curve.

We instantiate this machinery with the secp256k1 short Weierstrass curve
`y² = x³ + 7` (coefficients `a₁ = a₂ = a₃ = a₄ = 0, a₆ = 7`) over
`F := ZMod secp256k1_p`, and define `Secp256k1Point` as an alias for the
resulting `Point` type. The `AddCommGroup` is then automatically inherited.

## Primality of secp256k1_p

`secp256k1_p = 2^256 - 2^32 - 977` is a 256-bit prime.
`secp256k1_p_prime : Fact (Nat.Prime secp256k1_p)` is a **theorem**, proven by a
Pratt certificate (`Formal.CurvePrimes`, kernel-checked; see `Formal.Pratt`). It
supplies the `Fact p.Prime` needed to derive `Field (ZMod secp256k1_p)`, which in
turn enables mathlib's `AddCommGroup` instance on the affine-point type.

## Theorem / instance index

| Name                          | Statement                                       |
|-------------------------------|-------------------------------------------------|
| `secp256k1_p`                 | `2^256 - 2^32 - 977` as `ℕ`                     |
| `secp256k1_p_prime`           | primality of `secp256k1_p` (Pratt)              |
| `secp256k1Curve`              | the short Weierstrass curve `y² = x³ + 7`       |
| `Secp256k1Point`              | nonsingular points of `secp256k1Curve` ∪ {∞}    |
| `Secp256k1Point.addCommGroup` | inherited `AddCommGroup` instance               |
-/

namespace Xark

/-! ## The secp256k1 base-field prime -/

/-- **The secp256k1 base-field prime** `p = 2^256 − 2^32 − 977`. -/
def secp256k1_p : ℕ := 2^256 - 2^32 - 977

/-- **Primality of `secp256k1_p`**, proven by the Pratt certificate
`Pratt.prime_115792089237316195423570985008687907853269984665640564039457584007908834671663` (`Formal/CurvePrimes.lean`). -/
theorem secp256k1_p_prime : Fact (Nat.Prime secp256k1_p) :=
  ⟨by rw [show secp256k1_p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 by norm_num [secp256k1_p]]; exact Pratt.prime_115792089237316195423570985008687907853269984665640564039457584007908834671663⟩

attribute [instance] secp256k1_p_prime

/-! ## The secp256k1 Weierstrass curve over `ZMod secp256k1_p` -/

/-- **The secp256k1 short Weierstrass curve** `y² = x³ + 7` over the base
field `ZMod secp256k1_p`, expressed in mathlib's general Weierstrass form
`y² + a₁·x·y + a₃·y = x³ + a₂·x² + a₄·x + a₆` with
`a₁ = a₂ = a₃ = a₄ = 0` and `a₆ = 7`. -/
def secp256k1Curve : WeierstrassCurve.Affine (ZMod secp256k1_p) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 7

/-! ## The secp256k1 point group -/

/-- **A nonsingular point on the secp256k1 curve.** This is either the point
at infinity (`WeierstrassCurve.Affine.Point.zero`) or a pair `(x, y)`
satisfying `y² = x³ + 7` together with the (algebraically automatic, in
this case) nonsingularity witness.

The type is an alias for mathlib's `WeierstrassCurve.Affine.Point` at the
secp256k1 curve, so we automatically inherit the textbook `AddCommGroup`
structure. -/
abbrev Secp256k1Point : Type := secp256k1Curve.Point

namespace Secp256k1Point

/-- The point at infinity (group identity). -/
abbrev infinity : Secp256k1Point := WeierstrassCurve.Affine.Point.zero

/-- Smart constructor: build a `Secp256k1Point` from coordinates and a
nonsingularity proof. The user-facing curve equation `y² = x³ + 7` is
recoverable via `WeierstrassCurve.Affine.Nonsingular.left` (the `Equation`
component). -/
abbrev affine (x y : ZMod secp256k1_p)
    (h : secp256k1Curve.Nonsingular x y) : Secp256k1Point :=
  WeierstrassCurve.Affine.Point.some _ _ h

end Secp256k1Point

/-! ## Inherited `AddCommGroup` instance

The `AddCommGroup` instance on `WeierstrassCurve.Affine.Point W` (with
`W : Affine F`, `[Field F]`, `[DecidableEq F]`) is mathlib-proved via the
`toClass` group homomorphism into the class group of the affine coordinate
ring. Since `Secp256k1Point` is definitionally `secp256k1Curve.Point` and
`ZMod secp256k1_p` is a field (by the primality theorem above) with
decidable equality, we inherit the instance for free. -/

/-- **`Secp256k1Point` is an additive abelian group** under the secp256k1
group law (mathlib instance, inherited via `abbrev`). Associativity follows
from the textbook ideal-class-group argument in
`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`. -/
instance Secp256k1Point.addCommGroup : AddCommGroup Secp256k1Point :=
  inferInstance

/-! ### Coefficients of the secp256k1 curve

The curve `y² = x³ + 7` has all Weierstrass coefficients zero except `a₆ = 7`.
The following hold by `rfl` from the definition of `secp256k1Curve`. -/

@[simp] theorem secp256k1Curve_a₁ : secp256k1Curve.a₁ = 0 := rfl
@[simp] theorem secp256k1Curve_a₂ : secp256k1Curve.a₂ = 0 := rfl
@[simp] theorem secp256k1Curve_a₃ : secp256k1Curve.a₃ = 0 := rfl
@[simp] theorem secp256k1Curve_a₄ : secp256k1Curve.a₄ = 0 := rfl
@[simp] theorem secp256k1Curve_a₆ : secp256k1Curve.a₆ = 7 := rfl

/-- For our curve, `negY x y = -y`. -/
theorem secp256k1Curve_negY (x y : ZMod secp256k1_p) :
    secp256k1Curve.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

end Xark
