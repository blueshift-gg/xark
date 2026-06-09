/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Ecdsa
import Formal.NonNative
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# ECDSA verification end-to-end soundness

Top-level soundness statement for the in-circuit ECDSA verifier in
`crates/acir-r1cs/src/gadgets/ecdsa.rs::ecdsa_verify_with_curve`, packaging the
per-primitive theorems already proved in `formal/`:

* `Formal.NonNative.mul_mod_via_Fr_limbwise_constraints` — the non-native
  modular product (`a · b mod m`) over 4 × 64-bit BN254 `Fr` limbs is sound.
* `Formal.Ecdsa.ladder_correct` — the LSB-first double-and-add scalar ladder
  computes `scalar • P` in any additive commutative group.

into one theorem of the form
**"any valid gadget witness implies the textbook ECDSA-verify predicate"**.

## Scope

This wrapper is **parametric over the curve point group**
`G : Type*` `[AddCommGroup G]`. Concrete specialisations live in
`Formal.Secp256k1Group` and `Formal.Secp256r1Group`, which close the chain
by providing verified `AddCommGroup` instances for the two ECDSA curves.

What the wrapper *does* close, in Lean, over all assignments:

* The **algebraic verification flow** — `w = s⁻¹ mod n`, `u₁ = e·w mod n`,
  `u₂ = r·w mod n`, `R = u₁•g + u₂•Q`, `r = R.x mod n` — is exactly the
  textbook ECDSA predicate. The non-native arithmetic and the scalar ladder
  are the two pieces the gadget actually composes, and both have their own
  end-to-end soundness theorems already.
* The two bridges below (`mul_mod_lifts_to_ZMod`, `ladder_gives_R_def`) plug
  those theorems' conclusions directly into the wrapper's hypotheses, so the
  end-to-end statement composes without slack.

What it does **not** close:

* secp256k1 / secp256r1 point-addition closure (`Formal.Curve` is Grumpkin).
* The on-curve check for the public key — meaningful only once `G` is a
  concrete curve group.
* The 4-limb `range`-gadget bridge from prover-supplied limbs in
  `Fin 4 → ZMod r` to the `.val` of the corresponding `ZMod n` element. That
  is layered separately in `Formal.NonNative` and feeds the `_val` hypotheses
  here as `valOfLimbs` equalities.

## Theorem chain

| Name                      | Statement                                                            |
|---------------------------|----------------------------------------------------------------------|
| `EcdsaVerifyRel`          | textbook ECDSA-verify predicate, abstractly                          |
| `IsValidEcdsaWitness`     | gadget intermediate-state predicate, mirrors `ecdsa_verify_with_curve` |
| `ecdsa_verify_sound`      | `IsValidEcdsaWitness → EcdsaVerifyRel`                               |
| `mul_mod_lifts_to_ZMod`   | bridge from `valOfLimbs`/`mul_mod` ℕ identity to `ZMod n` equality    |
| `ladder_gives_R_def`      | bridge from `ladder_correct` to the `R_def` field                    |
| `ecdsa_verify_compose`    | full chain — per-primitive ℕ/group hypotheses ⇒ `EcdsaVerifyRel`      |
-/

namespace Xark

/-! ## Textbook ECDSA-verify relation -/

/-- **The mathematical ECDSA-verify predicate.** Given:

* `n`       — the curve's scalar field order;
* `g`       — the curve generator (in the abstract additive group `G`);
* `Q`       — the public key (as a point in `G`);
* `xProj`   — the `R.x mod n` projection used by ECDSA;
* `e r s`   — the message digest and signature components, pre-reduced
              `mod n`,

`EcdsaVerifyRel n g Q xProj e r s` says: `r` and `s` are nonzero, and there
exists a modular inverse `w` of `s` mod `n` such that `r` equals the
x-coordinate (mod `n`) of `u₁ • g + u₂ • Q` with `u₁ = e · w` and
`u₂ = r · w`. This is the textbook definition (FIPS 186-4 §6.4 / SEC 1 §4.1.4)
specialised to the digest already being reduced to `ZMod n`. -/
def EcdsaVerifyRel {G : Type*} [AddCommGroup G]
    (n : ℕ) (g Q : G) (xProj : G → ZMod n) (e r s : ZMod n) : Prop :=
  r ≠ 0 ∧ s ≠ 0 ∧ ∃ w : ZMod n, s * w = 1 ∧
    r = xProj ((e * w).val • g + (r * w).val • Q)

/-! ## Gadget intermediate-state witness -/

/-- **Gadget intermediate-state predicate.** Mirrors the witness allocations
in `gadgets/ecdsa.rs::ecdsa_verify_with_curve` one-to-one:

| Field            | Gadget constraint                                                |
|------------------|------------------------------------------------------------------|
| `r_nonzero`      | `enforce_in_range_one_to_n(r)` (the `1 ≤ r` half)                |
| `s_nonzero`      | `enforce_in_range_one_to_n(s)`                                   |
| `w_inv_s`        | `inv_mod(s, n) = w`  ⇒  `s · w ≡ 1 (mod n)`                      |
| `u1_def`         | `bigint256_mul_mod(e, w, n) = u₁`                                |
| `u2_def`         | `bigint256_mul_mod(r, w, n) = u₂`                                |
| `R_def`          | `scalar_mul_2p_* (u₁, g, Q, u₂) = Rpt`                           |
| `r_eq_xR`        | `enforce_bigint_eq(Rpt.x mod n, r)`                              |

Notice: every field is an algebraic equality (or non-zero predicate) in
`ZMod n` / `G`. The lift from prover-supplied 4-limb `Fr` witnesses to these
`ZMod n` equalities is exactly what `mul_mod_via_Fr_limbwise_constraints`
(arithmetic) and `ladder_correct` + `range_unique` (scalar mul) discharge —
see `mul_mod_lifts_to_ZMod` and `ladder_gives_R_def` below. -/
structure IsValidEcdsaWitness {G : Type*} [AddCommGroup G]
    (n : ℕ) (g Q : G) (xProj : G → ZMod n)
    (e r s w u₁ u₂ : ZMod n) (Rpt : G) : Prop where
  r_nonzero : r ≠ 0
  s_nonzero : s ≠ 0
  w_inv_s   : s * w = 1
  u1_def    : u₁ = e * w
  u2_def    : u₂ = r * w
  R_def     : Rpt = u₁.val • g + u₂.val • Q
  r_eq_xR   : r = xProj Rpt

/-! ## End-to-end soundness -/

/-- **End-to-end soundness wrapper.** Any prover witness satisfying the
gadget's intermediate-state predicate (`IsValidEcdsaWitness`) implies the
textbook ECDSA-verify relation (`EcdsaVerifyRel`).

The proof is pure substitution: every existential / projection in
`EcdsaVerifyRel` is pinned by a field of `IsValidEcdsaWitness`. -/
theorem ecdsa_verify_sound {G : Type*} [AddCommGroup G]
    {n : ℕ} {g Q : G} {xProj : G → ZMod n}
    {e r s w u₁ u₂ : ZMod n} {Rpt : G}
    (h : IsValidEcdsaWitness n g Q xProj e r s w u₁ u₂ Rpt) :
    EcdsaVerifyRel n g Q xProj e r s := by
  refine ⟨h.r_nonzero, h.s_nonzero, w, h.w_inv_s, ?_⟩
  -- Goal: r = xProj ((e * w).val • g + (r * w).val • Q).
  -- Rewriting `r` via `h.r_eq_xR` would substitute inside the `(r * w)` term
  -- on the RHS as well, creating a recursive goal. Instead, rewrite the RHS
  -- expression to `Rpt` (using `h.u1_def`, `h.u2_def`, `h.R_def` in reverse)
  -- and then close with `h.r_eq_xR`.
  have hRpt : (e * w).val • g + (r * w).val • Q = Rpt := by
    rw [← h.u1_def, ← h.u2_def, ← h.R_def]
  rw [hRpt]
  exact h.r_eq_xR

/-! ## Composition bridges

These two lemmas let the existing per-primitive soundness theorems feed
`IsValidEcdsaWitness` directly. They are deliberately small / mechanical —
the heavy lifting is in the primitives' own end-to-end theorems
(`mul_mod_via_Fr_limbwise_constraints`, `ladder_correct`). -/

/-- **Bridge: `mul_mod` ⇒ `ZMod n` multiplication.** The conclusion of
`mul_mod_via_Fr_limbwise_constraints` (after composing with the limb-`.val`
recomposition) is an ℕ-identity `u.val = (a.val · b.val) % n`. This lemma
upgrades that to the algebraic equality `u = a · b` in `ZMod n` — exactly
what the `u1_def` / `u2_def` fields of `IsValidEcdsaWitness` expect.

The standard mathlib fact this rests on is `ZMod.val_mul`:
`(a · b : ZMod n).val = a.val · b.val % n`. -/
theorem mul_mod_lifts_to_ZMod {n : ℕ} [NeZero n] {a b u : ZMod n}
    (h : u.val = (a.val * b.val) % n) : u = a * b := by
  have hv : u.val = (a * b).val := by rw [ZMod.val_mul]; exact h
  exact ZMod.val_injective _ hv

/-- **Bridge: scalar ladder + ec_add ⇒ `R_def`.** Given two ladder
accumulators that have already been pinned to `u₁ • g` and `u₂ • Q` by
`ladder_correct`, and an `ec_add` output `Rpt = acc₁ + acc₂`, conclude
`Rpt = u₁ • g + u₂ • Q` — the `R_def` field of `IsValidEcdsaWitness`.

This is the trivial substitution; the *content* is in `ladder_correct`
(`Formal.Ecdsa`) and (for the concrete curve) the `ec_add` soundness
theorem for that group. We package it as a named lemma so the composition
chain is visible in the axiom check / theorem list. -/
theorem ladder_gives_R_def {G : Type*} [AddCommGroup G]
    {g Q acc₁ acc₂ Rpt : G} {u₁ u₂ : ℕ}
    (h₁ : acc₁ = u₁ • g) (h₂ : acc₂ = u₂ • Q) (hR : Rpt = acc₁ + acc₂) :
    Rpt = u₁ • g + u₂ • Q := by
  rw [hR, h₁, h₂]

/-! ## Full composition theorem -/

/-- **End-to-end ECDSA verifier soundness (composed).** Takes the per-primitive
guarantees in the exact shape produced by the existing soundness theorems
(`mul_mod_via_Fr_limbwise_constraints` for the two products, `ladder_correct`
+ ec_add for the point-side, the gadget's algebraic checks for the rest) and
concludes the textbook `EcdsaVerifyRel`.

Hypotheses, in the order they appear in `ecdsa_verify_with_curve`:

* `h_r_ne, h_s_ne` — `enforce_in_range_one_to_n(r)` and `(s)` (the `≥ 1` half).
* `h_w` — `inv_mod(s, n) = w` constraint.
* `h_u1_nat, h_u2_nat` — `mul_mod` outputs at the `ZMod n`-value level
  (output of `mul_mod_via_Fr_limbwise_constraints` composed with the limb
  `.val` recomposition).
* `h_acc1, h_acc2` — `ladder_correct` outputs for `u₁ • g` and `u₂ • Q`.
* `h_R` — the `ec_add` output `Rpt = acc₁ + acc₂`.
* `h_r_eq` — the final `enforce_bigint_eq` check.

The conclusion `EcdsaVerifyRel n g Q xProj e r s` is the textbook
"this is a valid ECDSA signature" predicate. -/
theorem ecdsa_verify_compose
    {G : Type*} [AddCommGroup G]
    {n : ℕ} [NeZero n] {g Q : G} {xProj : G → ZMod n}
    {e r s w u₁ u₂ : ZMod n} {acc₁ acc₂ Rpt : G}
    (h_r_ne : r ≠ 0) (h_s_ne : s ≠ 0)
    (h_w : s * w = 1)
    (h_u1_nat : u₁.val = (e.val * w.val) % n)
    (h_u2_nat : u₂.val = (r.val * w.val) % n)
    (h_acc1 : acc₁ = u₁.val • g)
    (h_acc2 : acc₂ = u₂.val • Q)
    (h_R : Rpt = acc₁ + acc₂)
    (h_r_eq : r = xProj Rpt) :
    EcdsaVerifyRel n g Q xProj e r s :=
  ecdsa_verify_sound
    { r_nonzero := h_r_ne
      s_nonzero := h_s_ne
      w_inv_s   := h_w
      u1_def    := mul_mod_lifts_to_ZMod h_u1_nat
      u2_def    := mul_mod_lifts_to_ZMod h_u2_nat
      R_def     := ladder_gives_R_def h_acc1 h_acc2 h_R
      r_eq_xR   := h_r_eq }

end Xark
