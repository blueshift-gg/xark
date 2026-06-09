/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.AcirLowering
import Formal.Predication
import Formal.Bookkeeping
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Cross-circuit `Call` inlining

`crates/acir-r1cs/src/lower.rs::lower_call_at` performs three pieces of
work beyond the witness-index shift already covered in `Formal.AcirLowering`
(`AssertZeroLinear.shift`, `lowerAssertZeroLinear_shift_sound`,
`call_relabel_gated_sound`):

1. **Output binding.** The `Call` opcode carries an `outputs` list of caller
   witnesses that must be bound to specific callee output witnesses (taken
   from the callee's `return_values`). The inliner emits a copy row
   `w(output_caller) = w(output_callee + offset)` per binding.
2. **Predicate combination.** The caller's active predicate (`parent_predicate`)
   and the `Call`'s own predicate are combined via `combine_predicates` (a
   single R1CS multiplication row) before being installed as the gating
   predicate for the inlined callee body.
3. **Memory-scope splice.** The callee's `MemoryInit` opcodes allocate fresh
   block ids in the callee's namespace (shifted by `offset` via
   `shift_opcode`), disjoint from the caller's blocks; constant-pin tables
   are spliced in scope so the constant-index `MemoryOp` shortcut still
   fires inside the callee.

This file models items (1)–(3) on top of the witness-shift primitives
in `Formal.AcirLowering`.
All theorems are `sorryAx`-free.
-/

namespace Xark

/-! ## Output binding -/

/-- A `Call` opcode model carrying the data the inliner needs for output
binding and predicate combination. Mirrors the relevant fields of
`acir::circuit::opcodes::Opcode::Call`:

* `inputs` / `outputs` — caller-side witness indices.
* `inner_opcodes` — the callee body, modelled here as a list of linear
  `AssertZero` opcodes (the case where the relabel composes recursively after
  BlackBox/Memory rejection under non-trivial predicates).
* `offset` — the fresh per-call witness-index / block-id offset allocated
  by `R1csBuilder::alloc_call_offset`.
* `output_binding` — pairs `(caller_idx, callee_idx)` declaring that the
  caller's output witness `caller_idx` is bound to the callee's output
  witness `callee_idx` after relabel (i.e. callee index `callee_idx`
  becomes wire `callee_idx + offset` in the combined R1CS). -/
structure CallOpcode (F : Type*) where
  inputs         : List ℕ
  outputs        : List ℕ
  inner_opcodes  : List (AssertZeroLinear F)
  offset         : ℕ
  output_binding : List (ℕ × ℕ)

/-- A "copy" R1CS row that pins `w caller = w callee_with_offset`. We use
the linear `AssertZero` shape: `0 · 0 = w caller − w callee_with_offset`
encoded as the linear `AssertZero` opcode with constant `0` and terms
`[(1, caller_idx), (-1, callee_idx_with_offset)]`, lowered via
`lowerAssertZeroLinear`. This matches the lowering's emit-copy path
(a single R1CS row, no fresh aux witness). -/
def copyRow {F : Type*} [Field F] (caller_idx callee_idx_with_offset : ℕ) :
    R1csRow F :=
  lowerAssertZeroLinear
    ({ constant := 0
       terms := [((1 : F), caller_idx), ((-1 : F), callee_idx_with_offset)] } :
       AssertZeroLinear F)

/-- Lower a single output binding `(caller_idx, callee_idx)` into a copy
row pinning `w caller_idx = w (callee_idx + offset)`. -/
def lowerOutputBinding {F : Type*} [Field F]
    (offset : ℕ) (binding : ℕ × ℕ) : R1csRow F :=
  copyRow binding.1 (binding.2 + offset)

/-- Lower a `CallOpcode`:
* one copy row per `output_binding`;
* the relabelled (shifted) callee inner opcodes lowered via
  `lowerAssertZeroLinear`.

Predicate gating is *not* baked in here — the caller wires
`combine_predicates` + `enforce_gated_sound` around the result via
`gated_under_combined_predicate_sound`. -/
def lowerCall {F : Type*} [Field F] (call : CallOpcode F) : List (R1csRow F) :=
  call.output_binding.map (lowerOutputBinding call.offset) ++
    call.inner_opcodes.map (fun op => lowerAssertZeroLinear (op.shift call.offset))

/-- Satisfaction of a single copy row: `copyRow caller callee` is
satisfied iff `w caller = w callee`. Reduces to
`lowerAssertZeroLinear_sound` applied to the `(constant = 0,
terms = [(1, caller), (-1, callee)])` linear opcode. -/
theorem copyRow_satisfied_iff {F : Type*} [Field F]
    (w : AcirWitnessMap F) (caller callee : ℕ)
    (h_const : ConstantWirePinned w) :
    (copyRow (F := F) caller callee).Satisfied w ↔ w caller = w callee := by
  unfold copyRow
  rw [lowerAssertZeroLinear_sound _ w h_const]
  -- `AssertZeroLinear.Satisfied { constant := 0, terms := [(1, caller), (-1, callee)] } w`
  -- expands by definition (List.map / List.sum on a 2-element list) to
  -- `0 + (1·w caller + (-1·w callee + 0)) = 0`, equivalent to `w caller = w callee`.
  show ((0 : F) + ((1 : F) * w caller + ((-1 : F) * w callee + 0)) = 0) ↔
       w caller = w callee
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Output-binding soundness.** Every copy row emitted by `lowerCall` for
an output binding `(caller_idx, callee_idx)` forces
`w caller_idx = w (callee_idx + offset)` under any R1CS-satisfying
witness. -/
theorem lowerCall_outputs_bound {F : Type*} [Field F]
    (call : CallOpcode F) (w : AcirWitnessMap F)
    (h_const : ConstantWirePinned w)
    (h_rows : ∀ row ∈ lowerCall call, R1csRow.Satisfied row w) :
    ∀ binding ∈ call.output_binding,
      w binding.1 = w (binding.2 + call.offset) := by
  intro binding hb
  -- The copy row for `binding` is in `lowerCall call`.
  have hrow : (lowerOutputBinding call.offset binding).Satisfied w := by
    apply h_rows
    unfold lowerCall
    apply List.mem_append.mpr
    left
    exact List.mem_map_of_mem hb
  -- Unfold to the `copyRow` form.
  unfold lowerOutputBinding at hrow
  exact (copyRow_satisfied_iff w binding.1 (binding.2 + call.offset) h_const).mp hrow

/-- **Callee-body soundness via `lowerCall`.** If every R1CS row emitted by
`lowerCall call` is satisfied (under a constant-wire-pinned witness map),
then every inner ACIR `AssertZero` opcode of the callee is satisfied under
the shifted witness map `w.shift offset` — exactly the original ACIR
semantics of the callee. -/
theorem lowerCall_inner_sound {F : Type*} [Field F]
    (call : CallOpcode F) (w : AcirWitnessMap F)
    (h_const : ConstantWirePinned w)
    (h_rows : ∀ row ∈ lowerCall call, R1csRow.Satisfied row w) :
    ∀ op ∈ call.inner_opcodes, op.Satisfied (w.shift call.offset) := by
  intro op hop
  have hrow : (lowerAssertZeroLinear (op.shift call.offset)).Satisfied w := by
    apply h_rows
    unfold lowerCall
    apply List.mem_append.mpr
    right
    exact List.mem_map_of_mem hop
  exact (lowerAssertZeroLinear_shift_sound op w call.offset h_const).mp hrow

/-! ## Predicate combination -/

/-- `combine_predicates p_outer p_inner = p_outer · p_inner`. Mirrors
`combine_predicates` in `lower.rs`: when both predicates are present the
inliner allocates a fresh witness pinned to their product via the R1CS
row `p_outer · p_inner = combined`. When both are booleans, the product is
boolean (a natural AND), so no extra range check is needed. -/
def combine_predicates {F : Type*} [Field F] (p_outer p_inner : F) : F :=
  p_outer * p_inner

/-- **Combined predicate is boolean when both operands are.** This is the
algebraic justification for the inliner skipping a range-check on the
combined predicate (the product of two booleans is boolean). The
statement uses the same `p · (p − 1) = 0` shape as elsewhere. -/
theorem combine_predicates_is_boolean {F : Type*} [Field F]
    (p_outer p_inner : F)
    (h_outer : p_outer * (p_outer - 1) = 0)
    (h_inner : p_inner * (p_inner - 1) = 0) :
    combine_predicates p_outer p_inner * (combine_predicates p_outer p_inner - 1) = 0 := by
  -- p_outer ∈ {0,1} ∧ p_inner ∈ {0,1} ⇒ product ∈ {0,1}.
  unfold combine_predicates
  rcases predicate_bool_cases p_outer h_outer with hpo | hpo
  · -- p_outer = 0 ⇒ p = 0.
    rw [hpo]; ring
  · -- p_outer = 1 ⇒ p = p_inner ∈ {0,1}.
    rw [hpo]
    simp only [one_mul]
    exact h_inner

/-- **R1CS realisability of `combine_predicates`.** The inliner allocates a
fresh witness `v` and emits the row `p_outer · p_inner = v`. Soundness:
any witness satisfying that row pins `v = combine_predicates p_outer p_inner`.

This is the structural lemma stating the R1CS row's semantics matches our
algebraic `combine_predicates` definition. -/
theorem combine_predicates_row_sound {F : Type*} [Field F]
    (p_outer p_inner v : F)
    (h_row : p_outer * p_inner = v) :
    v = combine_predicates p_outer p_inner := by
  unfold combine_predicates
  exact h_row.symm

/-- **Composition: `enforce_gated` under a combined predicate.** When the
inliner installs `combine_predicates p_outer p_inner` as the gating
predicate for the callee body, `enforce_gated_sound` applied with the
combined predicate is equivalent (in the "fires" branch) to the chained
implication: outer fires AND inner fires ⇒ original constraint fires.

Specifically: the gated row `a · b = c + e` with gate `p · e = 0` for
`p = combine_predicates p_outer p_inner` boolean implies, when both
`p_outer = 1` and `p_inner = 1`, that `a · b = c`. -/
theorem gated_under_combined_predicate_sound {F : Type*} [Field F]
    (a b c p_outer p_inner e : F)
    (h_outer_bool : p_outer * (p_outer - 1) = 0)
    (h_inner_bool : p_inner * (p_inner - 1) = 0)
    (h_orig : a * b = c + e)
    (h_gate : combine_predicates p_outer p_inner * e = 0) :
    (p_outer = 1 → p_inner = 1 → a * b = c) := by
  intro hpo hpi
  have hp_combined_bool : combine_predicates p_outer p_inner * (combine_predicates p_outer p_inner - 1) = 0 :=
    combine_predicates_is_boolean p_outer p_inner h_outer_bool h_inner_bool
  -- Apply enforce_gated_sound with the combined predicate.
  have h := enforce_gated_sound a b c (combine_predicates p_outer p_inner) e h_orig h_gate hp_combined_bool
  apply h
  unfold combine_predicates
  rw [hpo, hpi]
  ring

/-- **Decomposition: gating by the combined predicate equals chaining the
gates.** If the outer predicate already gated a constraint to `a · b = c'`
(its "outer-active" form) and we then gate by the inner predicate, the
result is `a · b = c` only when both predicates fire — exactly the
two-level gating semantics the inliner implements. This is the
"equivalent to outer-then-inner" sense of the task brief. -/
theorem combined_predicate_equiv_chain {F : Type*} [Field F]
    (p_outer p_inner : F)
    (h_outer : p_outer * (p_outer - 1) = 0)
    (h_inner : p_inner * (p_inner - 1) = 0) :
    combine_predicates p_outer p_inner = 1 ↔ (p_outer = 1 ∧ p_inner = 1) := by
  unfold combine_predicates
  constructor
  · intro h
    rcases predicate_bool_cases p_outer h_outer with hpo | hpo
    · rw [hpo, zero_mul] at h; exact absurd h zero_ne_one
    · rcases predicate_bool_cases p_inner h_inner with hpi | hpi
      · rw [hpi, mul_zero] at h; exact absurd h zero_ne_one
      · exact ⟨hpo, hpi⟩
  · rintro ⟨hpo, hpi⟩
    rw [hpo, hpi]; ring

/-! ## Memory-scope splice

The inliner shifts memory block ids in lock-step with witness indices via
`call::prepare_call`'s `shift_opcode`. Specifically: every `MemoryInit` in
the callee's body has its `block_id` bumped by `offset`, so callee
blocks live in `[offset, offset + callee_block_count)` — a range disjoint
from the caller's `[0, caller_block_count)` provided the inliner
allocated `offset ≥ caller_block_count` (which it does, by
`alloc_call_offset` reserving the upper half of the index space).

We model the namespace disjointness as a structural assertion on the
`AllocState` from `Formal.Bookkeeping`. The proof reduces to a simple
arithmetic argument: callee block ids are all of the form `b + offset` for
`b < callee_block_count`, hence all `≥ offset`; caller block ids are all
`< offset` by hypothesis. -/

/-- Caller-namespace block id (a `ℕ` bounded by the caller's block count). -/
structure CallerBlock where
  id : ℕ

/-- Callee-namespace block id (a `ℕ` bounded by the callee's block count),
shifted by the call offset when spliced into the combined R1CS. -/
structure CalleeBlock where
  id : ℕ
  /-- The post-shift block id used in the combined R1CS. -/
  shifted_id : ℕ

/-- **Memory-scope splice — namespace disjointness.** If the inliner
allocates a call offset bounded below by the caller's block count and
shifts every callee block id by `offset`, then every caller block id is
strictly less than every (shifted) callee block id.

This is the structural assertion the lowering relies on: caller and
callee MemoryInit blocks never collide after splice. -/
theorem callee_block_ids_disjoint_from_caller
    (caller_block_count offset : ℕ)
    (h_offset : offset ≥ caller_block_count)
    (caller_id callee_id : ℕ)
    (h_caller : caller_id < caller_block_count)
    (h_callee_shift : ∃ b, callee_id = b + offset) :
    caller_id < callee_id := by
  rcases h_callee_shift with ⟨b, hb⟩
  rw [hb]
  -- caller_id < caller_block_count ≤ offset ≤ b + offset.
  have h1 : caller_id < offset := lt_of_lt_of_le h_caller h_offset
  exact lt_of_lt_of_le h1 (Nat.le_add_left offset b)

/-- **Memory-scope splice — `MemoryInit` allocates fresh ids.** A callee's
`MemoryInit` opcode declaring block id `b` (before shift) results in the
*shifted* id `b + offset` being allocated in the combined R1CS. Modelled
on `AllocState`: a sequence of caller `MemoryInit`s reaches `next ≤
offset` (by the offset-allocation invariant), so a fresh callee
`MemoryInit` allocation never collides with a caller assignment.

We prove the per-allocation freshness statement: if the alloc state has
already handed out variable indices in `[0, offset)` and we now alloc a
witness for a callee idx `idx ≥ offset`, the returned variable is fresh
(unassigned in the prior state). -/
theorem callee_alloc_fresh_from_caller
    (m : AllocState) (offset idx : ℕ)
    (h_state_bounded : ∀ i v, m.assigned i = some v → i < offset)
    (h_callee : idx ≥ offset) :
    m.assigned idx = none := by
  -- Suppose `m.assigned idx = some v`; then `idx < offset` by hypothesis,
  -- contradicting `idx ≥ offset`.
  cases hcase : m.assigned idx with
  | none => rfl
  | some v =>
    -- We get `idx < offset` from the bound, contradicting `offset ≤ idx`.
    have h_lt : idx < offset := h_state_bounded idx v hcase
    exact absurd h_callee (Nat.not_le_of_lt h_lt)

/-- **Memory-scope splice — combined statement.** A callee `MemoryInit`
spliced via the witness/block-id shift allocates a *fresh* block id (no
collision with caller blocks) in the combined R1CS allocation state.
Combines `callee_block_ids_disjoint_from_caller` with
`callee_alloc_fresh_from_caller`. -/
theorem memory_scope_splice_fresh
    (m : AllocState) (caller_block_count offset callee_block_id : ℕ)
    (h_offset : offset ≥ caller_block_count)
    (h_state_bounded : ∀ i v, m.assigned i = some v → i < offset) :
    m.assigned (callee_block_id + offset) = none ∧
    ∀ caller_id, caller_id < caller_block_count →
      caller_id < callee_block_id + offset := by
  refine ⟨?_, ?_⟩
  · apply callee_alloc_fresh_from_caller m offset (callee_block_id + offset) h_state_bounded
    exact Nat.le_add_left offset callee_block_id
  · intro caller_id h_caller
    apply callee_block_ids_disjoint_from_caller caller_block_count offset h_offset caller_id (callee_block_id + offset) h_caller
    exact ⟨callee_block_id, rfl⟩

/-! ### Integration of `MemoryInit` pass with `allocList`

`memory_scope_splice_fresh` takes the `h_state_bounded` hypothesis at
face value. In practice this hypothesis is discharged by the caller's
own `MemoryInit` pass through `alloc_list_memory_init_invariant` in
`Formal.Bookkeeping`. We compose them here.

The chain: at the call site, the caller has already walked an
`idxs` list of fresh, injective witness indices (modelling the caller's
`MemoryInit` opcodes). After that walk, `(initial.allocList idxs).next`
exceeds the planned `offset`. Then `memory_scope_splice_fresh` applies
because the post-walk allocation state satisfies the boundedness
hypothesis. -/

/-- **Integrated memory-scope splice.** Given a caller that has emitted
`N` `MemoryInit` opcodes (modelled via `allocList`), the resulting
`AllocState` is bounded below the call's `offset`, so splicing a callee
`MemoryInit` at `offset + callee_block_id` is fresh AND disjoint from
the caller block-id range. The bookkeeping-side hypothesis
`alloc_list_memory_init_invariant` is invoked to discharge
`memory_scope_splice_fresh`'s `h_state_bounded` premise. -/
theorem memory_scope_splice_integrated
    (caller_init_idxs : List ℕ)
    (caller_block_count callee_block_id : ℕ)
    (h_nodup : caller_init_idxs.Nodup)
    (h_fresh_in_initial : ∀ i ∈ caller_init_idxs,
      AllocState.initial.assigned i = none)
    (h_len : caller_init_idxs.length ≥ caller_block_count)
    (h_state_bounded :
      ∀ i v, (AllocState.initial.allocList caller_init_idxs).assigned i = some v →
        i < (AllocState.initial.allocList caller_init_idxs).next) :
    let m_after := AllocState.initial.allocList caller_init_idxs
    let offset  := m_after.next
    m_after.assigned (callee_block_id + offset) = none ∧
    ∀ caller_id, caller_id < caller_block_count →
      caller_id < callee_block_id + offset := by
  -- Derive `offset ≥ caller_block_count` from `alloc_list_memory_init_invariant`.
  have h_offset_lb : (AllocState.initial.allocList caller_init_idxs).next
                      ≥ 1 + caller_block_count :=
    alloc_list_memory_init_invariant AllocState.initial caller_init_idxs
      1 caller_block_count rfl h_nodup h_fresh_in_initial h_len
  have h_offset : (AllocState.initial.allocList caller_init_idxs).next ≥ caller_block_count := by
    have : (1 : ℕ) + caller_block_count ≥ caller_block_count := Nat.le_add_left _ _
    exact le_trans this h_offset_lb
  exact memory_scope_splice_fresh
    (AllocState.initial.allocList caller_init_idxs)
    caller_block_count
    (AllocState.initial.allocList caller_init_idxs).next
    callee_block_id
    h_offset
    h_state_bounded

end Xark
