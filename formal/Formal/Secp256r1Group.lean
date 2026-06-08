/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Secp256r1
import Formal.EcdsaVerify
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# secp256r1 point group as a concrete `AddCommGroup` (Layer B closure)

Mirrors `Formal.Secp256k1Group` for **secp256r1** (NIST P-256). Closes the
end-to-end chain at `G = Secp256r1Point` so that `EcdsaVerifyRel` and
`ecdsa_verify_compose` specialise to a fully concrete statement at the
actual NIST P-256 point group `{(x, y) : ZMod p × ZMod p // y² = x³ − 3·x + b} ∪ {∞}`.

## Strategy: reuse mathlib's `WeierstrassCurve.Affine.Point`

Same recipe as `Formal.Secp256k1Group`: instantiate
`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` at the secp256r1
short Weierstrass curve `y² = x³ + a·x + b` with `a = −3` and the standard
NIST b-constant. The `AddCommGroup` instance is then automatically inherited
via the class-group injection of an affine Weierstrass curve.

## Trusted base addition: primality of `secp256r1_p`

`secp256r1_p = 2^256 − 2^224 + 2^192 + 2^96 − 1` is the 256-bit NIST P-256
base-field prime (FIPS 186-4 D.1.2.3 / SEC 2 §2.4.2). As with `secp256k1_p`,
mathlib's `decide` is infeasible at this size, so we declare

    axiom secp256r1_p_prime : Fact (Nat.Prime secp256r1_p)

as a **trusted base addition** — verifiable in seconds outside Lean using a
standard primality test (e.g. `openssl prime
0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF`).

## Theorem / instance index

| Name                              | Statement                                              |
|-----------------------------------|--------------------------------------------------------|
| `secp256r1_p`                     | `2^256 − 2^224 + 2^192 + 2^96 − 1` as `ℕ`              |
| `secp256r1_p_prime`               | trusted primality axiom for `secp256r1_p`              |
| `secp256r1_b`                     | the NIST P-256 b-constant                              |
| `secp256r1Curve`                  | the short Weierstrass curve `y² = x³ − 3·x + b`        |
| `Secp256r1Point`                  | nonsingular points of `secp256r1Curve` ∪ {∞}           |
| `Secp256r1Point.addCommGroup`     | inherited `AddCommGroup` instance                      |
| `ecdsa_verify_compose_secp256r1`  | `ecdsa_verify_compose` at `G = Secp256r1Point`         |
-/

namespace Xark

/-! ## The secp256r1 base-field prime -/

/-- **The secp256r1 (NIST P-256) base-field prime**
`p = 2^256 − 2^224 + 2^192 + 2^96 − 1` (FIPS 186-4 D.1.2.3 / SEC 2 §2.4.2). -/
def secp256r1_p : ℕ :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- **Trusted primality fact for `secp256r1_p`** (standard public parameter).

NIST P-256's base-field prime is a well-known 256-bit prime listed in
FIPS 186-4 D.1.2.3 and SEC 2 §2.4.2. Independently verifiable outside Lean
(e.g. `openssl prime 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF`).
Declared as `Fact (Nat.Prime secp256r1_p)` because mathlib's `decide` is
infeasible and `native_decide` also doesn't terminate at this size. -/
axiom secp256r1_p_prime : Fact (Nat.Prime secp256r1_p)

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

/-! ## Headline: full ECDSA-verify soundness specialised to secp256r1 -/

/-- **ECDSA-verify end-to-end soundness, specialised to secp256r1.**
Direct specialisation of `Formal.EcdsaVerify.ecdsa_verify_compose` at
`G = Secp256r1Point`. -/
theorem ecdsa_verify_compose_secp256r1
    {n : ℕ} [NeZero n] {g Q : Secp256r1Point} {xProj : Secp256r1Point → ZMod n}
    {e r s w u₁ u₂ : ZMod n} {acc₁ acc₂ Rpt : Secp256r1Point}
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
