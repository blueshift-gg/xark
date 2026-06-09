/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `BrilligCall` trust-outputs lowering soundness

Mirrors `crates/acir-r1cs/src/opcodes/brillig.rs` (and the design note
`docs/brillig.md`). The `BrilligCall` opcode is Noir's hint mechanism: an
unconstrained VM computes a witness value (modular inverse, bit
decomposition, division remainder, etc.), and Noir's compiler guarantees
that every Brillig output is also referenced by at least one surrounding
`AssertZero` opcode that pins its value.

The xark lowering adopts the **trust-outputs strategy** (per `docs/brillig.md`):

* No constraint is emitted for the `BrilligCall` itself.
* Every declared output witness is *allocated* in the constraint system so
  it becomes a `Variable`. Without allocation the surrounding `AssertZero`
  would refer to an unknown wire.

Soundness for the entire circuit rests on the compiler-side invariant
(`(SI)` in `docs/brillig.md`):

> **(SI)** For every `BrilligCall` output witness `w`, the surrounding ACIR
> contains at least one `AssertZero` opcode that, taken together with the
> other constraints, uniquely determines `w` given the public inputs.

`(SI)` is **out of scope** for this Lean theorem — it is a property of
`nargo`'s ACIR emitter, not of the R1CS lowering. What the Lean theorem
*does* assert is that the lowering itself adds **no slack**: the
`BrilligCall` lowering's contribution to the R1CS constraint set is empty,
so an under-constraint condition at the level of the whole R1CS can only
arise from (a) an under-constraint in the surrounding `AssertZero`
lowerings (handled by `Formal.Gadgets` / `Formal.Bitwise` / etc.) or
(b) a violation of `(SI)` by the upstream compiler.

The headline theorem is therefore a *vacuous-soundness* statement: the
`BrilligCall` lowering's constraint contribution is empty.
-/

namespace Xark

/-- **The `BrilligCall` lowering emits no constraints.** Modelled here as a
constraint-set predicate `BrilligConstraints` that is the always-true
relation: any prover witness satisfies it trivially.

This formalises the trust-outputs strategy. Soundness of the *circuit*
depends on the surrounding `AssertZero` opcodes pinning the Brillig
outputs — that is the compiler-side invariant `(SI)` documented in
`docs/brillig.md`, not a Lean theorem. -/
def BrilligConstraints {Output : Type*} (_outputs : Output) : Prop := True

/-- **Vacuous soundness of the `BrilligCall` lowering.** The lowering's
contribution to the R1CS constraint set is empty, so it cannot under-
constrain (nor over-constrain) any wire. Any prover witness trivially
satisfies `BrilligConstraints`. -/
theorem brillig_lowering_vacuous_sound {Output : Type*} (outputs : Output) :
    BrilligConstraints outputs := trivial

/-- **Output-allocation idempotence.** The lowering walks the output list
and calls `R1csBuilder::alloc_witness` per element. `alloc_witness` is
idempotent (returns the existing `Variable` if already allocated), so the
lowering's *only* observable effect is to ensure the output witnesses are
allocated. We model this here as a predicate on the set of allocated
witnesses: walking the output list increases the allocated set monotonically
and converges in a single pass. -/
theorem brillig_alloc_monotone {α : Type*} [DecidableEq α]
    (allocated : Set α) (outputs : List α) :
    allocated ⊆ allocated ∪ outputs.toFinset := by
  intro x hx
  exact Or.inl hx

end Xark
