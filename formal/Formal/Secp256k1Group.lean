/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Secp256k1
import Formal.EcdsaVerify
import Formal.Glv
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# secp256k1 point group as a concrete `AddCommGroup`

`Formal.Secp256k1` proves the in-circuit ECDSA `ec_add` gadget faithfully
implements the secp256k1 group law *at the algebraic level* — every gadget
witness lands in the `EcAddSemantics_secp256k1` relation over an abstract
field. `Formal.EcdsaVerify` packages full ECDSA-verify soundness parametric
over **any** `[AddCommGroup G]`.

What was missing to close the chain is a concrete `AddCommGroup` instance on
the actual secp256k1 point group `{(x, y) : ZMod p × ZMod p // y² = x³ + 7} ∪ {∞}`,
so that `EcdsaVerifyRel` and `ecdsa_verify_compose` specialise to a fully
closed statement at `G = Secp256k1Point`.

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

## Trusted base addition: primality of secp256k1_p

`secp256k1_p = 2^256 - 2^32 - 977` is a 256-bit prime. Mathlib's `Nat.Prime`
*can* in principle be decided by trial division, but the decision procedure
is not practical at this size at elaboration time (~ minutes to TB of
allocations for naive `decide`). We therefore declare

    axiom secp256k1_p_prime : Fact (Nat.Prime secp256k1_p)

as a **trusted base addition**. This is a single, audit-checkable
mathematical fact (verifiable in seconds outside Lean using any standard
primality test, e.g. Miller–Rabin via `openssl prime` or sage). It and
the matching primality axioms for `secp256r1_p` (`Formal.Secp256r1Group`)
and BN254's `r` (`Formal.GrumpkinGroup`) are the only `axiom` declarations
in the Lean development. It supplies the `Fact p.Prime` needed to derive
`Field (ZMod secp256k1_p)`, which in turn enables mathlib's `AddCommGroup`
instance on the affine-point type.

## Theorem / instance index

| Name                          | Statement                                       |
|-------------------------------|-------------------------------------------------|
| `secp256k1_p`                 | `2^256 - 2^32 - 977` as `ℕ`                     |
| `secp256k1_p_prime`           | trusted primality axiom for `secp256k1_p`       |
| `secp256k1Curve`              | the short Weierstrass curve `y² = x³ + 7`       |
| `Secp256k1Point`              | nonsingular points of `secp256k1Curve` ∪ {∞}    |
| `Secp256k1Point.addCommGroup` | inherited `AddCommGroup` instance               |
| `ecdsa_verify_compose_secp256k1` | `ecdsa_verify_compose` at `G = Secp256k1Point` |
-/

namespace Xark

/-! ## The secp256k1 base-field prime -/

/-- **The secp256k1 base-field prime** `p = 2^256 − 2^32 − 977`. -/
def secp256k1_p : ℕ := 2^256 - 2^32 - 977

/-- **Trusted primality fact for `secp256k1_p`** (standard public parameter).

This is the single `axiom` in the development. `secp256k1_p` is a well-known
256-bit prime listed in SEC 2 §2.4.1 / FIPS 186-4 D.1.2; its primality is
independently verifiable outside Lean (e.g. `openssl prime
0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`). We
declare it as `Fact (Nat.Prime secp256k1_p)` rather than computing it,
because mathlib's `decide` tactic is infeasible on 256-bit naturals and
`native_decide` also doesn't terminate in reasonable time (kernel-recursive
trial division is exponential even compiled). Lucas/Pratt-certificate
tooling would discharge this with hand-supplied factorizations of `p − 1`. -/
axiom secp256k1_p_prime : Fact (Nat.Prime secp256k1_p)

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
`ZMod secp256k1_p` is a field (given the primality axiom above) with
decidable equality, we inherit the instance for free. -/

/-- **`Secp256k1Point` is an additive abelian group** under the secp256k1
group law (mathlib instance, inherited via `abbrev`). Associativity follows
from the textbook ideal-class-group argument in
`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`. -/
instance Secp256k1Point.addCommGroup : AddCommGroup Secp256k1Point :=
  inferInstance

/-! ## Headline: full ECDSA-verify soundness specialised to secp256k1

We now instantiate `ecdsa_verify_compose` at `G = Secp256k1Point` to obtain
a fully concrete statement: any gadget witness for secp256k1 ECDSA verifies
the textbook `EcdsaVerifyRel` predicate over the *actual* secp256k1 point
group. -/

/-- **ECDSA-verify end-to-end soundness, specialised to secp256k1.**
Direct specialisation of `Formal.EcdsaVerify.ecdsa_verify_compose` at
`G = Secp256k1Point`. The proof is by definitional unfolding; the content
is in `ecdsa_verify_compose` together with the `AddCommGroup` instance on
`Secp256k1Point` we just established. -/
theorem ecdsa_verify_compose_secp256k1
    {n : ℕ} [NeZero n] {g Q : Secp256k1Point} {xProj : Secp256k1Point → ZMod n}
    {e r s w u₁ u₂ : ZMod n} {acc₁ acc₂ Rpt : Secp256k1Point}
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

/-! ## Concrete secp256k1 endomorphism instantiation

The secp256k1 endomorphism is `φ(x, y) = (β · x, y)` where `β` is a
specific cube root of unity in `ZMod secp256k1_p`. We define `secp256k1_beta`
and `secp256k1_lambda`, then specialise `glv_endomorphism_correct` from
`Formal.Glv` to give: any group homomorphism `φ : Secp256k1Point →
Secp256k1Point` satisfying `φ(G) = λ • G` on the secp256k1 generator
acts as scalar multiplication by `λ` on the entire cyclic subgroup `⟨G⟩`.

The pieces still needed for a fully discharged concrete chain:

1. A concrete `secp256k1_phi : Secp256k1Point → Secp256k1Point` defined
   by the case-split on `WeierstrassCurve.Affine.Point.zero | .some`,
   mapping `(x, y) → (β · x, y)` on the affine arm. Defined below.
2. The group-homomorphism property `∀ a b, φ(a + b) = φ(a) + φ(b)`.
   This is an algebraic computation over the secp256k1 addition law;
   we state it as `Secp256k1Endomorphism` (a `Prop`) and document the
   derivation. The mechanical proof needs case-splits on the four
   `WeierstrassCurve.Affine.Point.add` arms and substitution of
   `(β x_i, y_i)` per arm.
3. The eigenvalue `φ(G) = λ • G` for the secp256k1 generator. A finite
   computation (run the ladder for `λ` steps and check equality); we
   state it as `secp256k1_phi_eigenvalue`. -/

/-- secp256k1 endomorphism scalar `β` — the non-trivial cube root of unity
in `ZMod secp256k1_p`. Sage `GF(p).cube_roots(1)` produces the published
value. -/
def secp256k1_beta : ZMod secp256k1_p :=
  0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

/-- secp256k1 endomorphism eigenvalue `λ` — the integer scalar such that
`λ³ ≡ 1 (mod secp256k1_n)` and `λ ≠ 1`. The published value. -/
def secp256k1_lambda : ℕ :=
  0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

/-- **`β³ = 1` in the secp256k1 base field.** `secp256k1_beta` is the
published nontrivial cube root of unity in `ZMod secp256k1_p`. Checking
that its cube equals 1 in `F = ZMod secp256k1_p` is a single 256-bit
field-arithmetic computation (one squaring + one multiplication + one
modular reduction), trivially carried out in Sage / Python:

```python
p = 2**256 - 2**32 - 977
beta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
assert pow(beta, 3, p) == 1
```

The Lean kernel cannot `decide` an equality in `ZMod p` at 256-bit `p` in
practical time, but `native_decide` (compiled-code reduction, which adds
the standard `Lean.ofReduceBool` axiom strictly weaker than ad-hoc
field-arithmetic claims) discharges this in milliseconds. -/
theorem secp256k1_beta_cube_eq_one : secp256k1_beta ^ 3 = 1 := by native_decide

/-- A trivial corollary: `β ≠ 0`. If `β = 0` then `β³ = 0 = 1`,
contradicting `1 ≠ 0` in `ZMod p` for prime `p > 1`. Depends only on
`secp256k1_beta_cube_eq_one` plus the curve's primality hypothesis. -/
theorem secp256k1_beta_ne_zero : secp256k1_beta ≠ 0 := by
  intro h
  have h3 : secp256k1_beta ^ 3 = 0 := by rw [h]; ring
  have h1 : (1 : ZMod secp256k1_p) = 0 := by
    rw [← secp256k1_beta_cube_eq_one, h3]
  exact one_ne_zero h1

/-- A handy fact: `β² ≠ 0`. -/
theorem secp256k1_beta_sq_ne_zero : secp256k1_beta ^ 2 ≠ 0 :=
  pow_ne_zero 2 secp256k1_beta_ne_zero

/-- `β⁴ = β` follows from `β³ = 1` by multiplying both sides by `β`. -/
theorem secp256k1_beta_pow_four : secp256k1_beta ^ 4 = secp256k1_beta := by
  have h := secp256k1_beta_cube_eq_one
  calc secp256k1_beta ^ 4
      = secp256k1_beta ^ 3 * secp256k1_beta := by ring
    _ = 1 * secp256k1_beta := by rw [h]
    _ = secp256k1_beta := by ring

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
  show -y - secp256k1Curve.a₁ * x - secp256k1Curve.a₃ = -y
  simp

/-- **Nonsingularity preservation under the endomorphism.** `φ : (x, y) ↦
(β · x, y)` maps nonsingular points to nonsingular points. Mechanically
proved from `secp256k1_beta_cube_eq_one` (`β³ = 1`) and `secp256k1_beta_ne_zero`.

* **Equation arm**: `y² = (β·x)³ + 7 = β³·x³ + 7 = x³ + 7` discharges by
  `linear_combination heq - x³ * (β³ - 1)`.
* **Smoothness arm**: either `3·x² ≠ 0` (then `3·(β·x)² = β²·(3·x²) ≠ 0`,
  using `β ≠ 0`) or `2·y ≠ 0` (y unchanged by the endomorphism). -/
theorem secp256k1_phi_preserves_nonsingular (x y : ZMod secp256k1_p)
    (h : secp256k1Curve.Nonsingular x y) :
    secp256k1Curve.Nonsingular (secp256k1_beta * x) y := by
  obtain ⟨heq, hns⟩ := h
  refine ⟨?_, ?_⟩
  · have hβ3 := secp256k1_beta_cube_eq_one
    rw [WeierstrassCurve.Affine.equation_iff'] at heq ⊢
    simp only [secp256k1Curve_a₁, secp256k1Curve_a₂, secp256k1Curve_a₃,
      secp256k1Curve_a₄, secp256k1Curve_a₆] at heq ⊢
    linear_combination heq - (x^3) * hβ3
  · have hβ := secp256k1_beta_ne_zero
    rcases hns with hx | hy
    · left
      simp only [WeierstrassCurve.Affine.evalEval_polynomialX,
        secp256k1Curve_a₁, secp256k1Curve_a₂, secp256k1Curve_a₄] at hx ⊢
      intro h0
      apply hx
      have hβ3 := secp256k1_beta_cube_eq_one
      linear_combination secp256k1_beta * h0 + (3 * x^2) * hβ3
    · right
      simp only [WeierstrassCurve.Affine.evalEval_polynomialY,
        secp256k1Curve_a₁, secp256k1Curve_a₃] at hy ⊢
      simpa using hy

/-- **Concrete secp256k1 endomorphism.** Acts as `(x, y) → (β · x, y)`
on affine points, and as identity on the point at infinity. -/
def secp256k1_phi : Secp256k1Point → Secp256k1Point := fun P =>
  match P with
  | WeierstrassCurve.Affine.Point.zero => WeierstrassCurve.Affine.Point.zero
  | WeierstrassCurve.Affine.Point.some x y h =>
    WeierstrassCurve.Affine.Point.some (secp256k1_beta * x) y
      (secp256k1_phi_preserves_nonsingular x y h)

/-- **End-to-end algebraic specialisation.** Direct
specialisation of `glv_endomorphism_correct` from `Formal.Glv` at
`G = Secp256k1Point`, `φ = secp256k1_phi`, `λ = secp256k1_lambda`.
Reduces to: given `φ` is a group homomorphism (`h_hom`), preserves zero
(`h_zero`), and satisfies the eigenvalue equation at the secp256k1
generator `G` (`h_eig`), then `φ(k • G) = λ • (k • G)` for all `k`.

The three hypotheses are precisely what an implementer needs to discharge
for a fully closed claim:
* `h_hom` — substitute `secp256k1_phi` into the secp256k1 addition law
  and check arm-by-arm (mechanical case-split on the four
  `WeierstrassCurve.Affine.Point.add` arms).
* `h_zero` — definitional unfolding of `secp256k1_phi` at `.zero`.
* `h_eig` — finite computation: run the secp256k1 ladder at scalar
  `λ = secp256k1_lambda` starting from `G` and check the equality
  `secp256k1_phi G = λ.val • G`.

Together they close the GLV decomposition chain over the secp256k1
generator's cyclic subgroup. -/
theorem glv_endomorphism_correct_secp256k1
    (G : Secp256k1Point)
    (h_hom : ∀ a b : Secp256k1Point,
        secp256k1_phi (a + b) = secp256k1_phi a + secp256k1_phi b)
    (h_zero : secp256k1_phi 0 = 0)
    (h_eig : secp256k1_phi G = secp256k1_lambda • G) :
    ∀ k : ℕ, secp256k1_phi (k • G) = secp256k1_lambda • (k • G) :=
  glv_endomorphism_correct secp256k1_phi h_hom h_zero G secp256k1_lambda h_eig

/-! ## Discharging `h_hom`, `h_zero`, and `h_eig` for the
concrete `secp256k1_phi`

We now close out the three hypotheses required by
`glv_endomorphism_correct_secp256k1` for the concrete `secp256k1_phi`
and a fixed generator `secp256k1_G`. The chain reduces to four trusted
finite axioms (each documented at its declaration site with the exact
external discharge procedure):

* `secp256k1_beta_cube_eq_one`: `β³ = 1` in `ZMod secp256k1_p` —
  a single 256-bit modular exponentiation.
* `secp256k1_phi_hom`: the endomorphism property of `secp256k1_phi`
  — a chord-tangent-algebra arm-by-arm check (case-split on the five
  arms of `WeierstrassCurve.Affine.Point.add`; the discharge of the two
  non-trivial arms is a polynomial identity modulo `β³ = 1`).
* `secp256k1_G_nonsingular`: the published generator is on-curve.
* `secp256k1_phi_eigenvalue_at_G`: `φ(G) = λ • G` for the published
  `(G, λ)` — a 256-bit scalar multiplication on the curve.

`secp256k1_phi_zero` and the final composition into
`secp256k1_phi_acts_as_lambda` are proved without `sorry`. -/

/-! ### Zero preservation: `phi(0) = 0` -/

/-- **`secp256k1_phi` preserves zero** (by definitional unfolding). -/
theorem secp256k1_phi_zero : secp256k1_phi 0 = 0 := rfl

/-! ### Homomorphism property: `secp256k1_phi (a + b) = secp256k1_phi a + secp256k1_phi b`

The endomorphism property of `secp256k1_phi`. -/

/-! ### Auxiliary lemmas for the homomorphism proof

We prove the two coordinate identities — `β · addX_old = addX_new` and
`addY_old = addY_new` — under the generic-case hypothesis
`¬(x₁ = x₂ ∧ y₁ = negY x₂ y₂)`. The case-split on `x₁ = x₂` vs. `x₁ ≠ x₂`
distinguishes doubling from secant. -/

/-- The image-side `x₁ = x₂` condition follows from the original one
(since `β ≠ 0`, multiplication by `β` is injective). -/
private lemma secp256k1_phi_hom_aux_hxy
    {x₁ x₂ y₁ y₂ : ZMod secp256k1_p}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = secp256k1Curve.negY x₂ y₂)) :
    ¬(secp256k1_beta * x₁ = secp256k1_beta * x₂ ∧
      y₁ = secp256k1Curve.negY (secp256k1_beta * x₂) y₂) := by
  intro ⟨h_x, h_y⟩
  apply hxy
  refine ⟨mul_left_cancel₀ secp256k1_beta_ne_zero h_x, ?_⟩
  rw [secp256k1Curve_negY] at h_y ⊢
  exact h_y

/-- Doubling denominator `2·y₁ ≠ 0` from `y₁ ≠ negY x₁ y₁ = -y₁`.
Mathematical content: `y ≠ -y` in `ZMod p` for odd `p` iff `2y ≠ 0`.
Proof: assume `2y = 0`; then `y = -y` (from `y + y = 0`), contradicting `y ≠ -y`. -/
private theorem secp256k1Curve_two_y_ne_zero
    {x₁ y₁ : ZMod secp256k1_p} (hy : y₁ ≠ secp256k1Curve.negY x₁ y₁) :
    (2 : ZMod secp256k1_p) * y₁ ≠ 0 := by
  rw [secp256k1Curve_negY] at hy
  intro h
  apply hy
  linear_combination h

/-- **`secp256k1_phi` is a group homomorphism.** Proof strategy:
case-split on the arms of `WeierstrassCurve.Affine.Point.add`.

* `zero + b` / `a + zero`: definitional (both `add` and `phi` distribute).
* `some + some` with `x₁ = x₂ ∧ y₁ = negY x₂ y₂` (inverse): both sides
  equal `0` because the same condition holds with `x` replaced by `β·x`
  (and `negY x y = -y` doesn't depend on `x`).
* `some + some` generic / doubling: after rewriting `+` via `add_some`,
  the goal reduces to two polynomial identities (one for x-coordinate, one
  for y-coordinate), both of which hold modulo `β³ - 1` (Lemmas
  `secp256k1_phi_hom_*_identity`). -/
theorem secp256k1_phi_hom : ∀ a b : Secp256k1Point,
    secp256k1_phi (a + b) = secp256k1_phi a + secp256k1_phi b := by
  intro a b
  rcases a with _ | ⟨x₁, y₁, h₁⟩
  · -- arm 1: 0 + b
    show secp256k1_phi (0 + b) = secp256k1_phi 0 + secp256k1_phi b
    rw [zero_add, secp256k1_phi_zero, zero_add]
  rcases b with _ | ⟨x₂, y₂, h₂⟩
  · -- arm 2: some + 0
    show secp256k1_phi (_ + 0) = secp256k1_phi _ + secp256k1_phi 0
    rw [add_zero, secp256k1_phi_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = secp256k1Curve.negY x₂ y₂
  · -- arm 3: inverse case (some + (-some) = 0)
    rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2, secp256k1_phi_zero]
    show (0 : Secp256k1Point) =
      WeierstrassCurve.Affine.Point.some (secp256k1_beta * x₁) y₁
        (secp256k1_phi_preserves_nonsingular x₁ y₁ h₁) +
      WeierstrassCurve.Affine.Point.some (secp256k1_beta * x₂) y₂
        (secp256k1_phi_preserves_nonsingular x₂ y₂ h₂)
    have hx' : secp256k1_beta * x₁ = secp256k1_beta * x₂ := by rw [hxy.1]
    have hy' : y₁ = secp256k1Curve.negY (secp256k1_beta * x₂) y₂ := by
      rw [secp256k1Curve_negY] at hxy ⊢; exact hxy.2
    rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx' hy']
  · -- arms 4 + 5: generic add OR doubling
    rw [WeierstrassCurve.Affine.Point.add_some hxy]
    have hxy' :
        ¬(secp256k1_beta * x₁ = secp256k1_beta * x₂ ∧
          y₁ = secp256k1Curve.negY (secp256k1_beta * x₂) y₂) :=
      secp256k1_phi_hom_aux_hxy hxy
    show WeierstrassCurve.Affine.Point.some
        (secp256k1_beta * secp256k1Curve.addX x₁ x₂ (secp256k1Curve.slope x₁ x₂ y₁ y₂))
        (secp256k1Curve.addY x₁ x₂ y₁ (secp256k1Curve.slope x₁ x₂ y₁ y₂)) _ =
      WeierstrassCurve.Affine.Point.some (secp256k1_beta * x₁) y₁
        (secp256k1_phi_preserves_nonsingular x₁ y₁ h₁) +
      WeierstrassCurve.Affine.Point.some (secp256k1_beta * x₂) y₂
        (secp256k1_phi_preserves_nonsingular x₂ y₂ h₂)
    rw [WeierstrassCurve.Affine.Point.add_some hxy']
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    have hβ := secp256k1_beta_ne_zero
    have hβ3 := secp256k1_beta_cube_eq_one
    by_cases hx : x₁ = x₂
    · -- arm 5: doubling
      have hy : y₁ ≠ secp256k1Curve.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      have hyy : y₁ = y₂ :=
        WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx hy
      subst hx; subst hyy
      have hy' : y₁ ≠ secp256k1Curve.negY x₁ y₁ := hy
      have hy_img : y₁ ≠ secp256k1Curve.negY (secp256k1_beta * x₁) y₁ := by
        rw [secp256k1Curve_negY] at hy' ⊢; exact hy'
      rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy',
          WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_img]
      simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.addX, secp256k1Curve_a₁, secp256k1Curve_a₂,
        secp256k1Curve_a₄, secp256k1Curve_negY,
        zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_sub, sub_neg_eq_add]
      have htwo : y₁ + y₁ = 2 * y₁ := by ring
      rw [htwo]
      refine ⟨?_, ?_⟩
      · field_simp
        linear_combination (-9 * x₁^4 * y₁⁻¹^2 * 4⁻¹) * hβ3
      · field_simp
        linear_combination
          (-9 * x₁^3 * y₁⁻¹ * 2⁻¹
           + 27 * x₁^6 * y₁⁻¹^3 * 4⁻¹ * 2⁻¹ * (secp256k1_beta^3 + 1)) * hβ3
    · -- arm 4: generic
      have hβx : (secp256k1_beta * x₁) ≠ (secp256k1_beta * x₂) := by
        intro h; exact hx (mul_left_cancel₀ hβ h)
      rw [WeierstrassCurve.Affine.slope_of_X_ne hx,
          WeierstrassCurve.Affine.slope_of_X_ne hβx]
      simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.addX, secp256k1Curve_a₁, secp256k1Curve_a₂,
        secp256k1Curve_negY,
        zero_mul, mul_zero, sub_zero, add_zero, zero_add]
      refine ⟨?_, ?_⟩
      · have hx_sub : x₁ - x₂ ≠ 0 := sub_ne_zero_of_ne hx
        have hβx_sub : secp256k1_beta * x₁ - secp256k1_beta * x₂ ≠ 0 :=
          sub_ne_zero_of_ne hβx
        field_simp
        linear_combination ((y₁ - y₂)^2) * hβ3
      · have hx_sub : x₁ - x₂ ≠ 0 := sub_ne_zero_of_ne hx
        have hβx_sub : secp256k1_beta * x₁ - secp256k1_beta * x₂ ≠ 0 :=
          sub_ne_zero_of_ne hβx
        field_simp
        linear_combination (-(y₁ - y₂)^3) * hβ3

/-! ### Eigenvalue equation at the generator: `phi(G) = λ • G` -/

/-- **secp256k1 generator x-coordinate.** Published in SEC 2 §2.4.1 /
FIPS 186-4 D.1.2 / Bitcoin Improvement Proposal §0009. -/
def secp256k1_G_x : ZMod secp256k1_p :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- **secp256k1 generator y-coordinate.** Published in SEC 2 §2.4.1 /
FIPS 186-4 D.1.2 / Bitcoin Improvement Proposal §0009. -/
def secp256k1_G_y : ZMod secp256k1_p :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-- **Nonsingularity of the published secp256k1 generator.** A single
256-bit field-arithmetic check that `(Gx, Gy)` lies on the curve
`y² = x³ + 7` and the derivative does not simultaneously vanish there.
Trivially verified externally:

```python
p = 2**256 - 2**32 - 977
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
assert (Gy * Gy - Gx**3 - 7) % p == 0
# Nonsingularity: at least one of `polynomialX(Gx, Gy)`, `polynomialY(Gx, Gy)`
# is non-zero; for `y² = x³ + 7` this reduces to `Gy ≠ 0 ∨ 3·Gx² ≠ 0`.
assert Gy != 0 or (3 * Gx**2) % p != 0
```

The Lean kernel cannot `decide` either constraint at 256-bit field
size in practical time, but `native_decide` (compiled-code reduction,
which adds the standard `Lean.ofReduceBool` axiom strictly weaker than
ad-hoc field-arithmetic claims) handles both checks in seconds. -/
theorem secp256k1_G_nonsingular :
    secp256k1Curve.Nonsingular secp256k1_G_x secp256k1_G_y := by
  refine ⟨?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff']
    simp only [secp256k1Curve_a₁, secp256k1Curve_a₂, secp256k1Curve_a₃,
      secp256k1Curve_a₄, secp256k1Curve_a₆]
    native_decide
  · right
    simp only [WeierstrassCurve.Affine.evalEval_polynomialY,
      secp256k1Curve_a₁, secp256k1Curve_a₃]
    intro h
    revert h
    native_decide

/-- **The secp256k1 generator point.** Concrete `Secp256k1Point` formed
from the published `(Gx, Gy)` and the trusted nonsingularity axiom. -/
def secp256k1_G : Secp256k1Point :=
  WeierstrassCurve.Affine.Point.some secp256k1_G_x secp256k1_G_y
    secp256k1_G_nonsingular

/-- **Eigenvalue equation at the secp256k1 generator.** A finite check:
running the standard secp256k1 double-and-add ladder for the 256-bit
scalar `secp256k1_lambda` starting from `secp256k1_G` and comparing the
resulting affine coordinates with `(β · Gx, Gy)`. The published value of
`λ` is chosen so that this identity holds; verification:

```python
p = 2**256 - 2**32 - 977
n = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
F = GF(p)
E = EllipticCurve(F, [0, 7])
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = E(Gx, Gy)
beta   = F(0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee)
lam    = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
assert (lam * G).xy() == (beta * Gx, Gy)
```

Symbolic scalar multiplication by a 256-bit constant inside the Lean
kernel via `decide` is infeasible, but `native_decide` (compiled-code
reduction, adding the standard `Lean.ofReduceBool` axiom — strictly
weaker than ad-hoc 256-bit point-arithmetic claims) handles the
~256-step `npow_recAux` binary expansion through the secp256k1
point-add formula in a few seconds. -/
theorem secp256k1_phi_eigenvalue_at_G :
    secp256k1_phi secp256k1_G = secp256k1_lambda • secp256k1_G := by
  native_decide

/-! ### Final composition: closed GLV-correctness statement on `⟨G⟩` -/

/-- **secp256k1 GLV correctness, fully closed at the published generator.**
All three hypotheses of `glv_endomorphism_correct_secp256k1`
(`h_hom`, `h_zero`, `h_eig`) are now discharged. The statement reads:
for every scalar `k : ℕ`, applying the concrete endomorphism
`secp256k1_phi` to `k • G` equals scalar multiplication by the published
eigenvalue `secp256k1_lambda` of `k • G`.

This is the user-facing GLV correctness statement on the secp256k1
generator's cyclic subgroup, with no remaining proof obligations and
no `sorry`. Audit trail: depends only on
`secp256k1_p_prime` (250+-bit primality),
`secp256k1_phi_preserves_nonsingular` (preservation of `Nonsingular`
under `(x, y) ↦ (β·x, y)`),
`secp256k1_beta_cube_eq_one` (β³ = 1),
`secp256k1_phi_hom` (chord-tangent algebra check),
`secp256k1_G_nonsingular` (on-curve check for the published `G`), and
`secp256k1_phi_eigenvalue_at_G` (256-bit ladder identity). -/
theorem secp256k1_phi_acts_as_lambda :
    ∀ k : ℕ, secp256k1_phi (k • secp256k1_G) =
      secp256k1_lambda • (k • secp256k1_G) :=
  glv_endomorphism_correct_secp256k1 secp256k1_G secp256k1_phi_hom
    secp256k1_phi_zero secp256k1_phi_eigenvalue_at_G

end Xark
