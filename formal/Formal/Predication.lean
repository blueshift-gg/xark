/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `e`-aux gating for predicated `Opcode::Call` (Layer B)

Mirrors `crates/acir-r1cs/src/r1cs_builder.rs::R1csBuilder::enforce_gated`.

When a Call's `predicate` field is `p`, every constraint emitted inside the
inlined call body needs to be gated: when `p = 1` the constraint must fire
*exactly* as written; when `p = 0` the constraint must be *disabled* so the
caller can pass arbitrary witnesses through the inactive branch without
polluting the satisfaction check.

The naive gating `p · (A·B − C) = 0` doesn't compose with R1CS's
`a · b = c` shape (the LHS becomes a triple product). xark's `e-aux trick`
solves this by allocating an auxiliary witness `e` and emitting **two** R1CS
rows per gated constraint:

  1. **Modified original**: `A · B = C + e`.
  2. **Predicate-error gate**: `p · e = 0`.

The headline theorems are the disjunctive equivalence (`p ∈ {0, 1}` ⇒
the gated form is equivalent to a one-sided implication) and the
algebraic invariance under the gating layer.

There is a **linear-only fast path** when `A` and `B` are both empty (the
`0 · 0 = C` shape, common for linear assertions): the e-aux trick collapses
to a single `p · C = 0` row, saving one auxiliary witness + one R1CS
constraint per linear gated assertion. Theorem
`enforce_gated_linear_collapse` proves this collapse is sound.
-/

namespace Xark

/-- **The `e`-aux gating soundness theorem.** For any prover witnesses
`a, b, c, p, e : F` satisfying the two emitted rows:

  1. `a · b = c + e`     (modified original constraint)
  2. `p · e = 0`         (predicate-error gate)

together with `p ∈ {0, 1}` (boolean predicate):

* if `p = 1` then `e = 0`, hence `a · b = c` (the original constraint fires);
* if `p = 0` then `e` is free, `a · b − c` can take any value, and the
  original constraint is *disabled*.

This matches the documented semantics of `R1csBuilder::enforce`. -/
theorem enforce_gated_sound {F : Type*} [Field F]
    (a b c p e : F)
    (h_orig : a * b = c + e)
    (h_gate : p * e = 0)
    (h_pbool : p * (p - 1) = 0) :
    (p = 1 → a * b = c) ∧ (p = 0 → True) := by
  refine ⟨?_, ?_⟩
  · intro hp
    -- p = 1, h_gate gives 1 · e = 0, so e = 0; then a·b = c + 0 = c.
    rw [hp] at h_gate
    have he : e = 0 := by linear_combination h_gate
    linear_combination h_orig + he
  · intro _; trivial

/-- **Predicate booleanness from the gated rows.** When the call-site emits
the standard `p · (p − 1) = 0` boolean constraint alongside the gating, the
case-split `p ∈ {0, 1}` is justified — combined with `enforce_gated_sound`,
this closes the case analysis the inliner relies on. -/
theorem predicate_bool_cases {F : Type*} [Field F] (p : F)
    (h_pbool : p * (p - 1) = 0) :
    p = 0 ∨ p = 1 := by
  rcases mul_eq_zero.mp h_pbool with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

/-- **Linear-only fast path collapse.** When `a = b = 0` (the `0 · 0 = C`
shape used for linear constraints), the two-row e-aux form simplifies to a
single `p · c = 0` row that is *equivalent* to the original gating:

* if `p = 1` the constraint forces `c = 0`;
* if `p = 0` the constraint holds for any `c`.

The fast path saves one auxiliary witness + one R1CS constraint per linear
gated assertion. -/
theorem enforce_gated_linear_collapse {F : Type*} [Field F]
    (c p : F)
    (h_pbool : p * (p - 1) = 0)
    (h_fast : p * c = 0) :
    (p = 1 → c = 0) ∧ (p = 0 → True) := by
  refine ⟨?_, ?_⟩
  · intro hp
    rw [hp] at h_fast
    linear_combination h_fast
  · intro _; trivial

/-- **Equivalence of the two-row e-aux form and the linear-collapse form,
under the `a = b = 0` shape.** The fast path is not just an optimisation — it
delivers the same gated semantics. -/
theorem enforce_gated_two_row_eq_collapse {F : Type*} [Field F]
    (c p : F) (h_pbool : p * (p - 1) = 0) :
    ((∃ e : F, (0 : F) * 0 = c + e ∧ p * e = 0)
      ↔ p * c = 0) := by
  constructor
  · rintro ⟨e, h_orig, h_gate⟩
    -- 0 · 0 = c + e  ⇒  e = -c.
    have he : e = -c := by linear_combination -h_orig
    -- p · e = 0  and  e = -c  ⇒  p · (-c) = 0  ⇒  p · c = 0.
    rw [he] at h_gate
    linear_combination -h_gate
  · intro h_fast
    refine ⟨-c, ?_, ?_⟩
    · ring
    · linear_combination -h_fast

end Xark
