/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Gadgets
import Formal.Curve
import Formal.EcdsaVerify
import Mathlib
import Formal.CurvePrimes

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Grumpkin point group as a concrete `AddCommGroup`

Mirrors `Formal.Secp256k1Group` for **Grumpkin** (the BN254 embedded curve
used by the xark scalar-mul gadget). Closes the end-to-end chain at
`G = GrumpkinPoint` so that `EcdsaVerifyRel` and `ecdsa_verify_compose`
specialise to a fully concrete statement at the actual Grumpkin point group
`{(x, y) : ZMod r × ZMod r // y² = x³ − 17} ∪ {∞}`.

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
| `ecdsa_verify_compose_grumpkin`   | `ecdsa_verify_compose` at `G = GrumpkinPoint`          |
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

/-! ## Headline: full ECDSA-verify soundness specialised to Grumpkin -/

/-- **ECDSA-verify end-to-end soundness, specialised to Grumpkin.**
Direct specialisation of `Formal.EcdsaVerify.ecdsa_verify_compose` at
`G = GrumpkinPoint`. -/
theorem ecdsa_verify_compose_grumpkin
    {n : ℕ} [NeZero n] {g Q : GrumpkinPoint} {xProj : GrumpkinPoint → ZMod n}
    {e r s w u₁ u₂ : ZMod n} {acc₁ acc₂ Rpt : GrumpkinPoint}
    (h_r_ne : r ≠ 0) (h_s_ne : s ≠ 0)
    (h_w : s * w = 1)
    (h_u1_nat : u₁.val = (e.val * w.val) % n)
    (h_u2_nat : u₂.val = (r.val * w.val) % n)
    (h_acc1 : acc₁ = u₁.val • g)
    (h_acc2 : acc₂ = u₂.val • Q)
    (h_R : Rpt = acc₁ + acc₂)
    (h_r_eq : r = xProj Rpt) :
    EcdsaVerifyRel n g Q xProj e r s :=
  ecdsa_verify_compose h_r_ne h_s_ne h_w h_u1_nat h_u2_nat h_acc1 h_acc2 h_R h_r_eq

end Xark
