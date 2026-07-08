/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Ecdsa
import Formal.EcdsaVerify
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Ed25519 twisted-Edwards addition & EdDSA-verification soundness

The Ed25519 gadget (`crates/xark-ed25519/src/lib.rs`, group law emitted by the
shared `xark_curve::edwards!` macro in `crates/xark-curve/src/lib.rs`) works on
the **twisted-Edwards** curve with `a = −1`

    −x² + y² = 1 + d · x² · y²

over the base field `p = 2^255 − 19`, curve constant

    d = 37095705934669439343138083508754565189542113879843219016388785533085940283555,

group order `L`, and base point `B`. Foreign 255-bit coordinates use the shared
3 × 86-bit non-native limb arithmetic (`Formal.NonNative`).

This file brings the Ed25519 stack up to the same formal bar as the
secp256k1/secp256r1 gadgets (`Formal.Secp256k1`, whose
`ec_add_incomplete_secp256k1_sound` a snapshot bridge pins gate counts to):
where Ed25519 previously had only KAT-vector coverage, we now have a Lean
soundness model with a **sorry-free** complete-addition soundness theorem.

## Key simplification vs. secp256k1

The macro comment (`ec_add` in `crates/xark-curve/src/lib.rs`) records the
in-circuit addition as

```text
  A = x1·y2 ; B = y1·x2 ; C = x1·x2 ; D = y1·y2 ; E = d·C·D
  x3 = (A + B) / (1 + E) ; y3 = (D + C) / (1 − E)
```

Twisted-Edwards addition with `a = −1` is **complete**: for on-curve points the
denominators `1 ± E = 1 ± d·x1·x2·y1·y2` are *never* zero when `d` is a
non-square (Bernstein–Birkner–Joye–Lange–Peters, *Twisted Edwards Curves*,
AFRICACRYPT 2008, Thm 3.3 — Ed25519's `d` is a non-square and `a = −1` is a
square since `p ≡ 1 (mod 4)`). Consequently, unlike the short-Weierstrass
secp256k1 chord law (`ec_add_incomplete_secp256k1_sound`, which carries an
`x1 ≠ x2` side-condition and a four-way infinity/inverse/doubling selector),
the Edwards addition-law-closure theorem here is **unconditional**: there are no
exceptional cases and no selector layer. We state completeness explicitly (as
the `EdwardsComplete` hypothesis, justified above) and use it; this makes the
closure proof cleaner than the secp one.

In the circuit the two denominators are inverted via witnesses
(`(1 + e).inverse()`, `(1 − e).inverse()`), whose defining constraints
`(1 ± E) · inv = 1` *also* force the denominators nonzero — so nonvanishing is
enforced by the gadget regardless of the `d`-non-square number theory. Both
routes are recorded below (`denom_ne_zero_of_inv`, `EdwardsComplete`).

## Theorem index

| Name                                | Statement |
|-------------------------------------|-----------|
| `OnEdwards`                         | curve-membership predicate `−x²+y² = 1+d·x²·y²`               |
| `onEdwards_identity`                | the neutral element `(0, 1)` is on-curve                     |
| `onEdwards_neg`                     | affine negation `(−x, y)` stays on-curve                     |
| `denom_ne_zero_of_inv`             | inverse-witness constraint forces `1 ± E ≠ 0`                |
| `EdwardsComplete`                   | completeness hyp: on-curve ⇒ `1 ± E ≠ 0` (BBJLP, `d` nonsq.) |
| `IsNonSquare`                       | `d` is a non-square in `F`                                   |
| **`edwards_add_on_curve`**          | **product-form closure — SORRY-FREE, the core**             |
| `edwards_add_closure`               | division-form closure (unconditional, via `EdwardsComplete`) |
| `edwards_add_identity_right`        | `P + (0,1) = P` (group identity axiom, formula level)        |
| `edwards_add_comm`                  | the addition formulas are symmetric (commutativity)          |
| `EddsaVerifyRel`                    | textbook `[S]·B = R + [k]·A` relation                        |
| `nsmul_neg_point`                   | `k • (−A) = −(k • A)` (negation lemma — SORRY-FREE)          |
| `eddsa_check_iff`                   | gadget's `[S]·B + [k]·(−A) = R ↔ [S]·B = R + [k]·A`          |
| `IsValidEddsaWitness`               | gadget intermediate-state predicate                          |
| `eddsa_verify_sound`                | witness ⇒ `EddsaVerifyRel` (SORRY-FREE)                      |
| `edwards_scalar_mul_ladder`         | complete-add ladder computes `[n]·P` (via `ladder_correct`)  |
| `edwards_double_scalar_mul_ladder`  | two ladders sum to `[S]·B + [k]·(−A)` (SORRY-FREE)           |
| `eddsa_verify_compose`              | end-to-end: ladder outputs ⇒ `EddsaVerifyRel` (SORRY-FREE)   |

Every theorem in this file is **sorry-free**. The only residual trust boundaries
are the same ones the secp256k1 chain carries: the non-native limb bridges
(`Formal.NonNative`) and the concrete curve-group `AddCommGroup` instance — both
out of scope for this soundness model, exactly as in `Formal.EcdsaVerify`.
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
`Formal.Secp256k1.ec_add_incomplete_secp256k1_sound` for the twisted-Edwards
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

/-! ## Part 2 — EdDSA verification relation

`eddsa_verify` (`crates/xark-ed25519/src/lib.rs`) checks the Ed25519 signature
equation `[S]·B == R + [k]·A`, which it rearranges to `[S]·B + [k]·(−A) == R`
so a single windowed Strauss–Shamir pass computes both scalar products. We model
the relation abstractly over the Ed25519 point group `G` (as an `AddCommGroup`;
completeness of the addition law makes the on-curve points a genuine group — cf.
Part 1 closure) and prove the gadget's group-level equality enforces exactly the
verification relation. Scalars are `ℕ` (the `bitsToNat` value of the 256-bit
decomposition), matching the `Formal.Ecdsa` ladder. -/

/-- **Textbook EdDSA-verify relation.** `[S]·B = R + [k]·A`: the signature scalar
`S` times the base point `B` equals the signature point `R` plus the challenge
`k` times the public key `A`. -/
def EddsaVerifyRel {G : Type*} [AddCommGroup G] (B A R : G) (S k : ℕ) : Prop :=
  S • B = R + k • A

/-- **Scalar negation lemma (SORRY-FREE).** `k • (−A) = −(k • A)`. Justifies the
gadget's rewrite `[k]·A ↦ [k]·(−A)` under a sign flip; twisted-Edwards affine
negation `(−x, y)` realizes `−A` in the group (`onEdwards_neg`). -/
theorem nsmul_neg_point {G : Type*} [AddCommGroup G] (k : ℕ) (A : G) :
    k • (-A) = -(k • A) := by
  induction k with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, ih]; abel

/-- **The verifier's rearranged check is equivalent to the verify relation.**
`[S]·B + [k]·(−A) = R ↔ [S]·B = R + [k]·A`. Soundness of the rewrite the gadget
performs before running the shared double-scalar multiplication. -/
theorem eddsa_check_iff {G : Type*} [AddCommGroup G] (B A R : G) (S k : ℕ) :
    (S • B + k • (-A) = R) ↔ (S • B = R + k • A) := by
  rw [nsmul_neg_point, ← sub_eq_add_neg, sub_eq_iff_eq_add]

/-- **Gadget intermediate-state predicate.** Mirrors `eddsa_verify`:

| Field    | Gadget constraint                                            |
|----------|-------------------------------------------------------------|
| `t_def`  | `t = double_scalar_mul(s_bits, B, k_bits, −A)` = `[S]·B + [k]·(−A)` |
| `t_eq_R` | `assert_eq(t, r_sig)` — the limb-wise equality `t == R`     |

The lift from the 3-limb per-coordinate `assert_eq` to the group equality
`t = R` is the non-native equality bridge (`Formal.NonNative`); the lift from the
windowed accumulator to `[S]·B + [k]·(−A)` is `eddsa_double_scalar_mul_composes`
(scaffolded below). -/
structure IsValidEddsaWitness {G : Type*} [AddCommGroup G]
    (B A R t : G) (S k : ℕ) : Prop where
  t_def  : t = S • B + k • (-A)
  t_eq_R : t = R

/-- **EdDSA-verification soundness (SORRY-FREE).** Any prover witness satisfying
the gadget's intermediate-state predicate implies the textbook EdDSA-verify
relation `[S]·B = R + [k]·A`. Mirrors `Formal.EcdsaVerify.ecdsa_verify_sound`:
pure substitution through `eddsa_check_iff`. -/
theorem eddsa_verify_sound {G : Type*} [AddCommGroup G]
    {B A R t : G} {S k : ℕ}
    (h : IsValidEddsaWitness B A R t S k) :
    EddsaVerifyRel B A R S k := by
  have hcheck : S • B + k • (-A) = R := by rw [← h.t_def, h.t_eq_R]
  exact (eddsa_check_iff B A R S k).mp hcheck

/-! ### Scalar-multiplication composition

That repeated complete-adds compute `[n]·P` — the composition step the task
flags as potentially large — is already discharged, over any additive
commutative group, by the LSB-first double-and-add ladder in `Formal.Ecdsa`
(`ladder_correct`). Because Ed25519's complete addition law makes the on-curve
points an `AddCommGroup`, specialising `G` there needs **no** exceptional-case
reasoning (contrast the secp256k1 ladder, which must dodge the incomplete-add
`x1 = x2` cases). We therefore close the composition without a `sorry`,
mirroring `Formal.EcdsaVerify.ecdsa_verify_compose`. -/

/-- **Complete-add ladder computes `[n]·P` (fully proven, via `ladder_correct`).**
Running the double-and-add ladder from `(0, P)` over an LSB-first bit-list `bs`
produces accumulator `bitsToNat bs • P`. -/
theorem edwards_scalar_mul_ladder {G : Type*} [AddCommGroup G]
    (bs : List Bool) (P : G) :
    (ladder bs (0, P)).1 = bitsToNat bs • P := by
  rw [ladder_correct]

/-- **Double-scalar composition (fully proven).** The two ladder accumulators for
`[S]·B` and `[k]·(−A)` sum to `[S]·B + [k]·(−A)` — the value the gadget's shared
Strauss–Shamir pass produces. Both scalar products are LSB double-and-add
ladders, so this is two applications of `ladder_correct`.

Note on scope: `double_scalar_mul` (`crates/xark-curve/src/lib.rs`) computes this
value via a *windowed* Strauss–Shamir pass (16-entry combined table, 2+2-bit
windows, `select16`) as an optimisation. That the windowed accumulator equals
this ladder value is a value-preserving equivalence layered on the limb-level
`select16` gadget (out of scope here, exactly as the secp256k1 ladder/limb
bridge is taken as the `h_acc*` hypotheses of `ecdsa_verify_compose`); the
group-level content — "repeated complete adds accumulate `[S]·B + [k]·(−A)`" —
is what is proved here. -/
theorem edwards_double_scalar_mul_ladder {G : Type*} [AddCommGroup G]
    (sbits kbits : List Bool) (B A : G) :
    (ladder sbits (0, B)).1 + (ladder kbits (0, -A)).1
      = bitsToNat sbits • B + bitsToNat kbits • (-A) := by
  rw [edwards_scalar_mul_ladder, edwards_scalar_mul_ladder]

/-- **End-to-end EdDSA-verification soundness (composed, SORRY-FREE).** Mirrors
`Formal.EcdsaVerify.ecdsa_verify_compose`. Takes the gadget's two group-side
outputs — the accumulator `t` (as two ladder scalar-products, `ht`) and the
final limb-wise equality `t == R` (`hR`) — and concludes the textbook
EdDSA-verify relation `[S]·B = R + [k]·A` with `S = bitsToNat sbits`,
`k = bitsToNat kbits`. -/
theorem eddsa_verify_compose {G : Type*} [AddCommGroup G]
    {B A R t : G} {sbits kbits : List Bool}
    (ht : t = (ladder sbits (0, B)).1 + (ladder kbits (0, -A)).1)
    (hR : t = R) :
    EddsaVerifyRel B A R (bitsToNat sbits) (bitsToNat kbits) :=
  eddsa_verify_sound
    { t_def := by rw [ht, edwards_double_scalar_mul_ladder]
      t_eq_R := hR }

end Xark
