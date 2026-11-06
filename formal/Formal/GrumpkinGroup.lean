/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.CurvePrimes
import Formal.Gadgets
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Grumpkin point group as a concrete `AddCommGroup`

Mirrors `Formal.Secp256k1Group` for **Grumpkin** (the BN254 embedded curve
used by the xark scalar-mul gadget): the actual Grumpkin point group
`{(x, y) : ZMod r × ZMod r // y² = x³ − 17} ∪ {∞}` as an `AddCommGroup`.

## Strategy: reuse mathlib's `WeierstrassCurve.Affine.Point`

Same recipe as `Formal.Secp256k1Group`: instantiate mathlib's
`WeierstrassCurve.Affine.Point` at the Grumpkin short Weierstrass curve
`y² = x³ + a·x + b` with `a = 0`, `b = −17`, over the BN254 scalar field
`ZMod r` (`r` defined in `Formal.Gadgets`). The `AddCommGroup` instance is
then inherited via the class-group injection.

## Primality of `r` (BN254 Fr modulus)

`r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`
is the 254-bit BN254 scalar field prime — the standard `ark_bn254::Fr` modulus.
`bn254_r_prime : Fact (Nat.Prime r)` is a **theorem**, proven by a Pratt certificate
(`Formal.CurvePrimes`, kernel-checked; see `Formal.Pratt`).

## Theorem / instance index

| Name                              | Statement                                              |
|-----------------------------------|--------------------------------------------------------|
| `bn254_r_prime`                   | primality of the BN254 scalar prime `r` (Pratt)        |
| `grumpkinCurve`                   | the short Weierstrass curve `y² = x³ − 17` over `ZMod r` |
| `GrumpkinPoint`                   | nonsingular points of `grumpkinCurve` ∪ {∞}            |
| `GrumpkinPoint.addCommGroup`      | inherited `AddCommGroup` instance                      |
-/

namespace Xark

/-! ## Primality of the BN254 scalar field modulus `r` -/

/-- **Primality of `r`** (the BN254 scalar prime), proven by the Pratt certificate
`Pratt.prime_21888242871839275222246405745257275088548364400416034343698204186575808495617` (`Formal/CurvePrimes.lean`: `r - 1`'s factorization, a witness of
order `r - 1`, and recursive certificates for its large factors). -/
theorem bn254_r_prime : Fact (Nat.Prime r) :=
  ⟨by rw [show r = 21888242871839275222246405745257275088548364400416034343698204186575808495617 from rfl]; exact Pratt.prime_21888242871839275222246405745257275088548364400416034343698204186575808495617⟩

attribute [instance] bn254_r_prime

/-! ## The Grumpkin Weierstrass curve over `ZMod r` -/

/-- **The Grumpkin short Weierstrass curve** `y² = x³ − 17` over the base
field `ZMod r`. In mathlib's general Weierstrass form
`y² + a₁·x·y + a₃·y = x³ + a₂·x² + a₄·x + a₆`: `a₁ = a₂ = a₃ = a₄ = 0`,
`a₆ = -17`. -/
def grumpkinCurve : WeierstrassCurve.Affine (ZMod r) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := -17

/-! ## The Grumpkin point group -/

/-- **A nonsingular point on the Grumpkin curve.** Either the point at
infinity (`WeierstrassCurve.Affine.Point.zero`) or a pair `(x, y)` with
`y² = x³ − 17` and a nonsingularity witness. Alias for mathlib's
`WeierstrassCurve.Affine.Point` so we inherit the textbook `AddCommGroup`. -/
abbrev GrumpkinPoint : Type := grumpkinCurve.Point

namespace GrumpkinPoint

/-- The point at infinity (group identity). -/
abbrev infinity : GrumpkinPoint := WeierstrassCurve.Affine.Point.zero

/-- Smart constructor from coordinates and a nonsingularity proof. -/
abbrev affine (x y : ZMod r)
    (h : grumpkinCurve.Nonsingular x y) : GrumpkinPoint :=
  WeierstrassCurve.Affine.Point.some _ _ h

end GrumpkinPoint

/-! ## Inherited `AddCommGroup` instance -/

/-- **`GrumpkinPoint` is an additive abelian group** under the Grumpkin
group law (mathlib instance, inherited via `abbrev`). -/
instance GrumpkinPoint.addCommGroup : AddCommGroup GrumpkinPoint :=
  inferInstance

end Xark
