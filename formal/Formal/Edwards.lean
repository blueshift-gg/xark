/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Twisted-Edwards complete addition

The curve predicate `OnEdwards d x y` (`a = −1`: `−x² + y² = 1 + d·x²·y²`) and the closure of
the addition law over any field: `edwards_add_on_curve` (product form, the core) and
`edwards_add_closure` (division form, under `EdwardsComplete`, which holds when `d` is a
non-square: Bernstein–Birkner–Joye–Lange–Peters, *Twisted Edwards Curves*, AFRICACRYPT
2008, Thm 3.3). `Formal.Ed25519Curve` instantiates it at Ed25519. Split out of
`Formal.Legacy.Edwards`, which keeps the hand-restated EdDSA relation.
-/

namespace Xark

/-! ## Part 1 — twisted-Edwards complete addition -/

/-- **Curve-membership predicate** for the Ed25519 twisted-Edwards curve
(`a = −1`): `(x, y)` is on the curve iff `−x² + y² = 1 + d·x²·y²`. -/
def OnEdwards {F : Type*} [Field F] (d x y : F) : Prop :=
  -x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2

/-- The neutral element `(0, 1)` (`identity()` in the gadget) is on the curve. -/
theorem onEdwards_identity {F : Type*} [Field F] (d : F) : OnEdwards d 0 1 := by
  unfold OnEdwards; ring

/-- **Affine negation stays on-curve.** Twisted-Edwards negation is `(−x, y)`
(as used by `let neg_a = Point::new(0 - a_pub.x, a_pub.y)` in `eddsa_verify`).
Since only `x²` appears in the curve equation, negating `x` preserves membership. -/
theorem onEdwards_neg {F : Type*} [Field F] (d x y : F) (h : OnEdwards d x y) :
    OnEdwards d (-x) y := by
  unfold OnEdwards at *
  linear_combination h

/-- `d` is a **non-square** in `F`: no field element squares to it. For Ed25519
this holds for the concrete `d` above, which — together with `a = −1` being a
square (`p ≡ 1 mod 4`) — is exactly the BBJLP completeness precondition. -/
def IsNonSquare {F : Type*} [Field F] (d : F) : Prop :=
  ∀ r : F, r * r ≠ d

/-- **Denominator nonvanishing from the gadget's inverse witness.** The circuit
computes `x3 = (a + b) · (1 + e).inverse()`; the inverse witness `inv` satisfies
`(1 + e) · inv = 1`, which already forces `1 + e ≠ 0` — no number theory needed.
This is the *faithful* soundness route for the denominators. -/
theorem denom_ne_zero_of_inv {F : Type*} [Field F] (den inv : F)
    (h : den * inv = 1) : den ≠ 0 := by
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- **Completeness hypothesis (BBJLP Thm 3.3).** For a non-square `d`, the
twisted-Edwards addition (`a = −1`) is *complete*: the two denominators
`1 ± d·x1·x2·y1·y2` never vanish on pairs of on-curve points, so the group law
has no exceptional cases. We package this standard fact as a predicate on `d`
(justified for Ed25519's `d`, cf. the module docstring) and consume it in
`edwards_add_closure` to obtain the **unconditional** closure theorem — the
cleanliness the twisted-Edwards form buys over the secp256k1 chord law. -/
def EdwardsComplete {F : Type*} [Field F] (d : F) : Prop :=
  ∀ x1 y1 x2 y2 : F, OnEdwards d x1 y1 → OnEdwards d x2 y2 →
    (1 + d * x1 * x2 * y1 * y2 ≠ 0) ∧ (1 - d * x1 * x2 * y1 * y2 ≠ 0)

/-- **Complete-addition soundness — product/witness form (SORRY-FREE core).**

This is the algebraic heart of Ed25519 point addition, mirroring
`Formal.Legacy.Secp256k1.ec_add_incomplete_secp256k1_sound` for the twisted-Edwards
law. The gadget's inverse-based output is captured by the *multiplicative*
witness equations

    x3 · (1 + E) = x1·y2 + y1·x2 ,   y3 · (1 − E) = y1·y2 + x1·x2

with `E = d·x1·x2·y1·y2` (exactly what `(a + b)·(1 + e).inverse()` enforces).
Given both inputs on the curve and nonzero denominators, the output `(x3, y3)`
lies back on the curve: **the addition law closes**, so the gadget computes a
genuine curve point, not an off-curve forgery.

The proof multiplies the target curve equation through by `(1 + E)²·(1 − E)²`
(nonzero by `hdx, hdy`), reduces via the two witness equations and the two
on-curve equations — a single `linear_combination` whose cofactors were computed
by an offline Gröbner reduction — then divides the nonzero factor back out. -/
theorem edwards_add_on_curve {F : Type*} [Field F]
    (d x1 y1 x2 y2 x3 y3 : F)
    (hE1 : OnEdwards d x1 y1) (hE2 : OnEdwards d x2 y2)
    (hx3 : x3 * (1 + d * x1 * x2 * y1 * y2) = x1 * y2 + y1 * x2)
    (hy3 : y3 * (1 - d * x1 * x2 * y1 * y2) = y1 * y2 + x1 * x2)
    (hdx : (1 + d * x1 * x2 * y1 * y2) ≠ 0)
    (hdy : (1 - d * x1 * x2 * y1 * y2) ≠ 0) :
    OnEdwards d x3 y3 := by
  unfold OnEdwards at hE1 hE2 ⊢
  -- Multiply the (rearranged) target by the nonzero factor (1+E)²(1−E)².
  have hfac : (1 + d * x1 * x2 * y1 * y2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hdx) (pow_ne_zero 2 hdy)
  have key :
      (-x3 ^ 2 + y3 ^ 2 - (1 + d * x3 ^ 2 * y3 ^ 2))
        * ((1 + d * x1 * x2 * y1 * y2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) ^ 2) = 0 := by
    linear_combination
        (-d^4*x1^3*x2^3*x3*y1^3*y2^3*y3^2 - d^3*x1^3*x2^3*x3*y1^3*y2^3 - d^3*x1^3*x2^2*y1^2*y2^3*y3^2 - d^3*x1^2*x2^3*y1^3*y2^2*y3^2 + d^3*x1^2*x2^2*x3*y1^2*y2^2*y3^2 - d^2*x1^3*x2^2*y1^2*y2^3 - d^2*x1^2*x2^3*y1^3*y2^2 + d^2*x1^2*x2^2*x3*y1^2*y2^2 + 2*d^2*x1^2*x2*y1*y2^2*y3^2 + 2*d^2*x1*x2^2*y1^2*y2*y3^2 + d^2*x1*x2*x3*y1*y2*y3^2 + 2*d*x1^2*x2*y1*y2^2 + 2*d*x1*x2^2*y1^2*y2 + d*x1*x2*x3*y1*y2 - d*x1*y2*y3^2 - d*x2*y1*y3^2 - d*x3*y3^2 - x1*y2 - x2*y1 - x3) * hx3
      + (-d^3*x1^3*x2^3*y1^3*y2^3*y3 + d^2*x1^3*x2^3*y1^2*y2^2 + d^2*x1^3*x2*y1*y2^3*y3 + d^2*x1^2*x2^2*y1^3*y2^3 + d^2*x1^2*x2^2*y1^2*y2^2*y3 + d^2*x1*x2^3*y1^3*y2*y3 - d*x1^3*x2*y2^2 - d*x1^2*y1*y2^3 - d*x1^2*y2^2*y3 - d*x1*x2^3*y1^2 - d*x1*x2*y1*y2*y3 - d*x2^2*y1^3*y2 - d*x2^2*y1^2*y3 + x1*x2 + y1*y2 + y3) * hy3
      + (d^3*x1^2*x2^4*y1^2*y2^4 - d^2*x1^2*x2^4*y2^4 + d^2*x2^4*y1^2*y2^4 - d^2*x2^4*y2^4 - d*x1^2*x2^4*y2^2 + d*x1^2*x2^2*y2^4 + d*x2^4*y1^2*y2^2 - 2*d*x2^4*y2^4 - d*x2^2*y1^2*y2^4 - 2*d*x2^2*y2^2 - 2*x2^4*y2^2 + x2^4 + 2*x2^2*y2^4 - 4*x2^2*y2^2 + y2^4) * hE1
      + (d*x1^4*x2^2*y2^2 + 2*d*x1^2*x2^2*y2^2 + d*x2^2*y1^4*y2^2 - 2*d*x2^2*y1^2*y2^2 + d*x2^2*y2^2 + 2*x1^2*x2^2*y2^2 - x1^2*x2^2 + x1^2*y2^2 - 2*x2^2*y1^2*y2^2 + x2^2*y1^2 + 2*x2^2*y2^2 - x2^2 - y1^2*y2^2 + y2^2 + 1) * hE2
  -- The nonzero factor cancels: the curve equation holds.
  have h0 : -x3 ^ 2 + y3 ^ 2 - (1 + d * x3 ^ 2 * y3 ^ 2) = 0 :=
    (mul_eq_zero.mp key).resolve_right hfac
  linear_combination h0

/-- **Complete-addition soundness — division/affine form (UNCONDITIONAL).**

The affine addition exactly as written in the spec

    x3 = (x1·y2 + y1·x2) / (1 + d·x1·x2·y1·y2)
    y3 = (y1·y2 + x1·x2) / (1 − d·x1·x2·y1·y2)

maps two on-curve points to an on-curve point, with **no side-condition**: the
denominators are supplied nonzero by the completeness hypothesis
`hc : EdwardsComplete d` (Ed25519's `d` is a non-square). This is the
twisted-Edwards analogue of `ec_add_incomplete_secp256k1_sound`, minus the
`x1 ≠ x2` guard the incomplete Weierstrass law needs. -/
theorem edwards_add_closure {F : Type*} [Field F]
    (d x1 y1 x2 y2 : F) (hc : EdwardsComplete d)
    (hE1 : OnEdwards d x1 y1) (hE2 : OnEdwards d x2 y2) :
    OnEdwards d
      ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2))
      ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)) := by
  obtain ⟨hdx, hdy⟩ := hc x1 y1 x2 y2 hE1 hE2
  refine edwards_add_on_curve d x1 y1 x2 y2 _ _ hE1 hE2 ?_ ?_ hdx hdy
  · exact div_mul_cancel₀ _ hdx
  · exact div_mul_cancel₀ _ hdy

/-- **Group identity axiom (formula level).** Adding the neutral element `(0, 1)`
returns the point unchanged: with `P2 = (0, 1)` we get `E = 0`, both denominators
are `1`, and the formulas collapse to `(x1, y1)`. Part of "the addition realizes
the group law". -/
theorem edwards_add_identity_right {F : Type*} [Field F] (d x1 y1 : F) :
    (x1 * (1 : F) + y1 * 0) / (1 + d * x1 * 0 * y1 * 1) = x1 ∧
    (y1 * (1 : F) + x1 * 0) / (1 - d * x1 * 0 * y1 * 1) = y1 := by
  constructor <;> · simp

/-- **Commutativity of the addition formulas.** Swapping the two summands leaves
`(x3, y3)` unchanged — both numerators and the `E` term are symmetric in the two
points. Another group-law axiom realized at the formula level. -/
theorem edwards_add_comm {F : Type*} [Field F] (d x1 y1 x2 y2 : F) :
    (x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)
      = (x2 * y1 + y2 * x1) / (1 + d * x2 * x1 * y2 * y1) ∧
    (y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)
      = (y2 * y1 + x2 * x1) / (1 - d * x2 * x1 * y2 * y1) := by
  constructor <;> · congr 1 <;> ring

end Xark
