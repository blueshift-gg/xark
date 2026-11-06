/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.CurvePrimes
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# secp256r1 point group as a concrete `AddCommGroup`

Mirrors `Formal.Secp256k1Group` for **secp256r1** (NIST P-256): the curve the
secp256r1 template proofs (`Formal.EcR1`) work in, the NIST P-256 point group `{(x, y) : ZMod p × ZMod p // y² = x³ − 3·x + b} ∪ {∞}`.

## Strategy: reuse mathlib's `WeierstrassCurve.Affine.Point`

Same recipe as `Formal.Secp256k1Group`: instantiate
`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` at the secp256r1
short Weierstrass curve `y² = x³ + a·x + b` with `a = −3` and the standard
NIST b-constant. The `AddCommGroup` instance is then automatically inherited
via the class-group injection of an affine Weierstrass curve.

## Primality of `secp256r1_p`

`secp256r1_p = 2^256 − 2^224 + 2^192 + 2^96 − 1` is the 256-bit NIST P-256
base-field prime (FIPS 186-4 D.1.2.3 / SEC 2 §2.4.2).
`secp256r1_p_prime : Fact (Nat.Prime secp256r1_p)` is a **theorem**, proven by a
Pratt certificate (`Formal.CurvePrimes`, kernel-checked; see `Formal.Pratt`).

## Theorem / instance index

| Name                              | Statement                                              |
|-----------------------------------|--------------------------------------------------------|
| `secp256r1_p`                     | `2^256 − 2^224 + 2^192 + 2^96 − 1` as `ℕ`              |
| `secp256r1_p_prime`               | primality of `secp256r1_p` (Pratt)                     |
| `secp256r1_b`                     | the NIST P-256 b-constant                              |
| `secp256r1Curve`                  | the short Weierstrass curve `y² = x³ − 3·x + b`        |
| `Secp256r1Point`                  | nonsingular points of `secp256r1Curve` ∪ {∞}           |
| `Secp256r1Point.addCommGroup`     | inherited `AddCommGroup` instance                      |
-/

namespace Xark

/-! ## The secp256r1 base-field prime -/

/-- **The secp256r1 (NIST P-256) base-field prime**
`p = 2^256 − 2^224 + 2^192 + 2^96 − 1` (FIPS 186-4 D.1.2.3 / SEC 2 §2.4.2). -/
def secp256r1_p : ℕ :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- **Primality of `secp256r1_p`**, proven by the Pratt certificate
`Pratt.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951` (`Formal/CurvePrimes.lean`). -/
theorem secp256r1_p_prime : Fact (Nat.Prime secp256r1_p) :=
  ⟨by rw [show secp256r1_p = 115792089210356248762697446949407573530086143415290314195533631308867097853951 by norm_num [secp256r1_p]]; exact Pratt.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951⟩

attribute [instance] secp256r1_p_prime

/-! ## The secp256r1 Weierstrass curve over `ZMod secp256r1_p` -/

/-- **The secp256r1 (NIST P-256) curve b-constant** — standard SEC 2 value. -/
def secp256r1_b : ZMod secp256r1_p :=
  0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

/-- **The secp256r1 short Weierstrass curve** `y² = x³ − 3·x + b` over the
base field `ZMod secp256r1_p`, expressed in mathlib's general Weierstrass
form `y² + a₁·x·y + a₃·y = x³ + a₂·x² + a₄·x + a₆` with
`a₁ = a₂ = a₃ = 0`, `a₄ = −3`, and `a₆ = secp256r1_b`. -/
def secp256r1Curve : WeierstrassCurve.Affine (ZMod secp256r1_p) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -3
  a₆ := secp256r1_b

/-! ## The secp256r1 point group -/

/-- **A nonsingular point on the secp256r1 curve.** Either the point at
infinity (`WeierstrassCurve.Affine.Point.zero`) or a pair `(x, y)` with
`y² = x³ − 3·x + b` and a nonsingularity witness. Alias for mathlib's
`WeierstrassCurve.Affine.Point` so we inherit the textbook `AddCommGroup`. -/
abbrev Secp256r1Point : Type := secp256r1Curve.Point

namespace Secp256r1Point

/-- The point at infinity (group identity). -/
abbrev infinity : Secp256r1Point := WeierstrassCurve.Affine.Point.zero

/-- Smart constructor from coordinates and a nonsingularity proof. -/
abbrev affine (x y : ZMod secp256r1_p)
    (h : secp256r1Curve.Nonsingular x y) : Secp256r1Point :=
  WeierstrassCurve.Affine.Point.some _ _ h

end Secp256r1Point

/-! ## Inherited `AddCommGroup` instance -/

/-- **`Secp256r1Point` is an additive abelian group** under the NIST P-256
group law (mathlib instance, inherited via `abbrev`). -/
instance Secp256r1Point.addCommGroup : AddCommGroup Secp256r1Point :=
  inferInstance

end Xark
