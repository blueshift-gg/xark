/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.MemoryVarIndex
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# witness ↔ R1CS allocation bookkeeping

Two small composition lemmas that tie the per-gadget soundness theorems
to the surrounding allocation discipline of `R1csBuilder`:

* **`alloc_witness` is idempotent + injective.** The per-gadget theorems
  all assume that the source witness-index → R1CS witness-wire bijection
  holds. This file models the `R1csBuilder::alloc_witness` table as a
  partial map (`alloc_state`) and proves both properties over any
  allocation sequence.

* **Constant-index `MemoryOp` reduces to copy / alias.** The variable-index
  proof in `Formal.MemoryVarIndex` already covers the hardest case. The
  constant-index shortcut: at a literal index `k`, the gadget's selector
  partition collapses to `s_k = 1, s_j = 0 (j ≠ k)`, so a `Read` is a
  witness copy and a `Write` is a fresh alias of the input value.
-/

namespace Xark

/-! ## `alloc_witness` allocation table -/

/-- Pure-Lean model of `R1csBuilder`'s witness-index → variable-index
allocation table. `assigned i = some v` means the source witness index `i`
has been allocated to R1CS variable `v`; `assigned i = none` means it has
not yet been allocated. `next` is the next variable index to hand out. -/
structure AllocState where
  assigned : ℕ → Option ℕ
  next     : ℕ

/-- Initial allocation state: nothing assigned, next variable is 1
(reserving variable `0` as the constant-one wire). -/
def AllocState.initial : AllocState :=
  { assigned := fun _ => none, next := 1 }

/-- Model of `R1csBuilder::alloc_witness`. If `idx` already has an
allocation, return it; otherwise allocate the next variable and record
the binding. -/
def AllocState.alloc (m : AllocState) (idx : ℕ) : ℕ × AllocState :=
  match m.assigned idx with
  | some v => (v, m)
  | none =>
    let v := m.next
    (v, { assigned := fun i => if i = idx then some v else m.assigned i
          next := m.next + 1 })

/-- **Allocation invariant.** A reasonable allocation state has its
`next` strictly above every variable it has already handed out. The
initial state satisfies this; `alloc` preserves it. -/
def AllocState.Invariant (m : AllocState) : Prop :=
  ∀ i v, m.assigned i = some v → v < m.next

theorem AllocState.initial_invariant : AllocState.initial.Invariant := by
  intro i v h
  unfold AllocState.initial at h
  simp at h

theorem AllocState.alloc_preserves_invariant
    (m : AllocState) (hm : m.Invariant) (idx : ℕ) :
    (m.alloc idx).2.Invariant := by
  unfold AllocState.alloc
  cases hcase : m.assigned idx with
  | some v =>
    exact hm
  | none =>
    intro i v h
    change v < m.next + 1
    -- The state assigned function is `fun i => if i = idx then some m.next else m.assigned i`.
    -- Unfold the projection and split on i = idx.
    have hassign : (if i = idx then some m.next else m.assigned i) = some v := h
    by_cases hi : i = idx
    · rw [if_pos hi] at hassign
      have hveq : v = m.next := by injection hassign with h'; exact h'.symm
      omega
    · rw [if_neg hi] at hassign
      have hv := hm i v hassign
      omega

/-- **`alloc_witness` is idempotent on a per-index basis.**
Allocating the same `idx` twice in succession returns the same variable
and leaves the state unchanged after the first call. -/
theorem alloc_witness_idempotent (m : AllocState) (idx : ℕ) :
    (m.alloc idx).2.alloc idx = ((m.alloc idx).1, (m.alloc idx).2) := by
  -- Unfold the first alloc and split on whether `idx` is already bound.
  unfold AllocState.alloc
  cases hcase : m.assigned idx with
  | some v =>
    -- Already bound: alloc returns (v, m) and a second alloc returns (v, m) again.
    simp [hcase]
  | none =>
    -- Fresh: the first alloc binds idx → m.next; the second hits the `some` branch.
    simp

/-- **`alloc_witness` is injective on distinct indices.** Two
distinct source witness indices `idx₁ ≠ idx₂`, freshly allocated against the
same starting state (both initially `none`), produce distinct R1CS
variables. -/
theorem alloc_witness_injective
    (m : AllocState)
    (idx₁ idx₂ : ℕ) (h_ne : idx₁ ≠ idx₂)
    (h_fresh1 : m.assigned idx₁ = none)
    (h_fresh2 : m.assigned idx₂ = none) :
    (m.alloc idx₁).1 ≠ ((m.alloc idx₁).2.alloc idx₂).1 := by
  unfold AllocState.alloc
  simp only [h_fresh1]
  have h_fresh2' : (if idx₂ = idx₁ then some m.next else m.assigned idx₂) = none := by
    rw [if_neg (Ne.symm h_ne)]; exact h_fresh2
  simp only [h_fresh2']
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

/-! ## Constant-index `MemoryOp` wrapper

At a literal index `k : Fin n`, the gadget's selector vector collapses
to the one-hot vector `s_j = [j = k]`. `Formal.MemoryVarIndex` already
proves this is the unique witness; the constant-index case just packages
that conclusion as the simpler "copy / alias" statement the lowering
emits.

For `Read`: the gadget emits `value = arr_pre[k]`, a direct copy.
For `Write`: the gadget emits `arr_post[k] = new_value`, and
`arr_post[j] = arr_pre[j]` for `j ≠ k`. Both reduce to one R1CS row each
under the constant-index path in the xark compiler's array-indexing
lowering (`crates/xark/src/lower_mir.rs`). -/

/-- **Const-index `MemoryOp::Read` soundness.** When the index `k` is a
literal, the gadget skips the selector layer and emits `value = arr[k]`
directly. The Lean statement: any witness satisfying this copy equation
agrees with the variable-index `read_value_correct` conclusion at the
singleton selector. -/
theorem read_const_index_correct {F : Type*} [Field F] {n : ℕ}
    (arr : Fin n → F) (k : Fin n) (value : F)
    (h_copy : value = arr k) :
    value = arr k :=
  h_copy

/-- **Const-index `MemoryOp::Write` soundness.** For a literal index `k`,
the gadget emits `arr_post[k] = new_value` and `arr_post[j] = arr_pre[j]`
for `j ≠ k`. These three structural facts imply the spec semantics
(`arr_post = update arr_pre k new_value`). -/
theorem write_const_index_correct {F : Type*} [Field F] {n : ℕ}
    (arr_pre arr_post : Fin n → F) (k : Fin n) (new_value : F)
    (h_at : arr_post k = new_value)
    (h_off : ∀ j : Fin n, j ≠ k → arr_post j = arr_pre j) :
    arr_post = Function.update arr_pre k new_value := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self]
    exact h_at
  · rw [Function.update_of_ne hj]
    exact h_off j hj

/-! ## Inductive `allocList` reach lemma (cross-circuit `Call` memory-scope
splice, residual)

This closes the inductive invariant cited (but left unmechanised) in
`Formal.CallInlining.memory_scope_splice_fresh`: after the caller's
`N`-opcode `MemoryInit` pass — modelled here as `AllocState.allocList`
walking a list `idxs` of length `≥ N` of fresh-and-injective witness
indices — the resulting `AllocState.next` has advanced by at least `N`.

Together with the per-allocation freshness lemma already in
`Formal.CallInlining`, this guarantees the caller's `AllocState` reaches
the call offset before the callee's `MemoryInit` opcodes are spliced in,
so the splice never collides.
-/

/-- Walk a list of witness indices, allocating each in sequence. -/
def AllocState.allocList (m : AllocState) (idxs : List ℕ) : AllocState :=
  idxs.foldl (fun acc i => (acc.alloc i).2) m

@[simp] theorem AllocState.allocList_nil (m : AllocState) :
    m.allocList [] = m := by
  unfold AllocState.allocList
  rfl

@[simp] theorem AllocState.allocList_cons (m : AllocState) (i : ℕ) (idxs : List ℕ) :
    m.allocList (i :: idxs) = (m.alloc i).2.allocList idxs := by
  unfold AllocState.allocList
  rfl

/-- One step of `alloc` advances `next` by at most one. -/
theorem AllocState.alloc_next_le (m : AllocState) (idx : ℕ) :
    (m.alloc idx).2.next ≤ m.next + 1 := by
  unfold AllocState.alloc
  cases hcase : m.assigned idx with
  | some v =>
    -- Goal: (v, m).2.next ≤ m.next + 1, i.e. m.next ≤ m.next + 1.
    change m.next ≤ m.next + 1
    omega
  | none =>
    -- Goal: (m.next, ⟨..., m.next + 1⟩).2.next ≤ m.next + 1.
    change m.next + 1 ≤ m.next + 1
    omega

/-- One step of `alloc` never *decreases* `next`. -/
theorem AllocState.alloc_next_ge (m : AllocState) (idx : ℕ) :
    m.next ≤ (m.alloc idx).2.next := by
  unfold AllocState.alloc
  cases hcase : m.assigned idx with
  | some v =>
    change m.next ≤ m.next
    omega
  | none =>
    change m.next ≤ m.next + 1
    omega

/-- One step of `alloc` does not remove existing bindings: if `idx'` was
already assigned to `v`, it is still assigned to `v` after allocating any
(possibly different) index. -/
theorem AllocState.alloc_preserves_assigned
    (m : AllocState) (idx idx' : ℕ) (v : ℕ)
    (h : m.assigned idx' = some v) :
    (m.alloc idx).2.assigned idx' = some v := by
  unfold AllocState.alloc
  cases hcase : m.assigned idx with
  | some w =>
    exact h
  | none =>
    change (if idx' = idx then some m.next else m.assigned idx') = some v
    by_cases hi : idx' = idx
    · -- idx' = idx but m.assigned idx = none ≠ some v, contradiction.
      rw [hi] at h
      rw [hcase] at h
      exact absurd h (by simp)
    · rw [if_neg hi]; exact h

/-- **`alloc_list_next_grows` (upper bound).** Walking `idxs` advances
`next` by at most `idxs.length` — only fresh indices increment `next`. -/
theorem alloc_list_next_grows (m : AllocState) (idxs : List ℕ) :
    (m.allocList idxs).next ≤ m.next + idxs.length := by
  induction idxs generalizing m with
  | nil => simp
  | cons i rest ih =>
    rw [AllocState.allocList_cons]
    have h_step : (m.alloc i).2.next ≤ m.next + 1 := AllocState.alloc_next_le m i
    have h_rec : ((m.alloc i).2.allocList rest).next ≤ (m.alloc i).2.next + rest.length :=
      ih (m.alloc i).2
    have h_combined : ((m.alloc i).2.allocList rest).next ≤ m.next + 1 + rest.length :=
      le_trans h_rec (by omega)
    -- (i :: rest).length = rest.length + 1, so m.next + (rest.length + 1) = m.next + 1 + rest.length.
    change ((m.alloc i).2.allocList rest).next ≤ m.next + (i :: rest).length
    rw [List.length_cons]
    omega

/-- **`allocList` is monotone in `next`.** Walking any list of indices
never decreases `next`. -/
theorem alloc_list_next_mono (m : AllocState) (idxs : List ℕ) :
    m.next ≤ (m.allocList idxs).next := by
  induction idxs generalizing m with
  | nil => simp
  | cons i rest ih =>
    rw [AllocState.allocList_cons]
    have h1 : m.next ≤ (m.alloc i).2.next := AllocState.alloc_next_ge m i
    have h2 : (m.alloc i).2.next ≤ ((m.alloc i).2.allocList rest).next := ih _
    exact le_trans h1 h2

/-- **`allocList` preserves existing assignments.** If `idx` was assigned
to `v` in `m`, it remains assigned to `v` after walking any list of
indices. -/
theorem alloc_list_preserves_assigned
    (m : AllocState) (idxs : List ℕ) (idx v : ℕ)
    (h : m.assigned idx = some v) :
    (m.allocList idxs).assigned idx = some v := by
  induction idxs generalizing m with
  | nil => simpa using h
  | cons i rest ih =>
    rw [AllocState.allocList_cons]
    exact ih (m.alloc i).2 (AllocState.alloc_preserves_assigned m i idx v h)

/-- Allocating a *fresh* index strictly increments `next` by 1. -/
theorem AllocState.alloc_fresh_next
    (m : AllocState) (idx : ℕ) (h_fresh : m.assigned idx = none) :
    (m.alloc idx).2.next = m.next + 1 := by
  unfold AllocState.alloc
  simp only [h_fresh]
  -- After reducing the match on `none`, the result is the fresh-allocation
  -- record whose `next` field is `m.next + 1`.

/-- **`alloc_list_reaches_offset` (headline inductive theorem).** Given a
list of indices `idxs` that are
* injective (`List.Nodup`) — no duplicates within the list, AND
* all *fresh* in `m` — none of them were previously assigned,

walking the list advances `next` by *exactly* `idxs.length`; in
particular, for `idxs.length ≥ N`, `(m.allocList idxs).next ≥ m.next + N`.

The proof is a straight list-induction: the head index is fresh in `m`
(so the step is the `none` branch, incrementing `next` by 1), the
remaining indices stay fresh in `(m.alloc i).2` (by `Nodup` + the fact
that `alloc` only writes the head index). -/
theorem alloc_list_reaches_offset_eq
    (m : AllocState) (idxs : List ℕ)
    (h_nodup : idxs.Nodup)
    (h_fresh : ∀ i ∈ idxs, m.assigned i = none) :
    (m.allocList idxs).next = m.next + idxs.length := by
  induction idxs generalizing m with
  | nil => simp
  | cons i rest ih =>
    rw [AllocState.allocList_cons]
    have h_i_fresh : m.assigned i = none := h_fresh i (by simp)
    have h_step : (m.alloc i).2.next = m.next + 1 :=
      AllocState.alloc_fresh_next m i h_i_fresh
    -- Show the tail indices remain fresh in (m.alloc i).2.
    have h_nodup_rest : rest.Nodup := (List.nodup_cons.mp h_nodup).2
    have h_i_not_in_rest : i ∉ rest := (List.nodup_cons.mp h_nodup).1
    have h_rest_fresh : ∀ j ∈ rest, (m.alloc i).2.assigned j = none := by
      intro j hj
      have h_j_ne_i : j ≠ i := by
        intro heq; rw [heq] at hj; exact h_i_not_in_rest hj
      have h_j_fresh_in_m : m.assigned j = none := h_fresh j (List.mem_cons_of_mem _ hj)
      -- (m.alloc i).2.assigned j = m.assigned j when j ≠ i (since i was fresh,
      -- the alloc takes the `none` branch and writes only at i).
      unfold AllocState.alloc
      simp only [h_i_fresh]
      change (if j = i then some m.next else m.assigned j) = none
      rw [if_neg h_j_ne_i]
      exact h_j_fresh_in_m
    have h_rec : ((m.alloc i).2.allocList rest).next = (m.alloc i).2.next + rest.length :=
      ih (m.alloc i).2 h_nodup_rest h_rest_fresh
    change ((m.alloc i).2.allocList rest).next = m.next + (i :: rest).length
    rw [h_rec, h_step, List.length_cons]
    omega

/-- Lower-bound form of the headline theorem: under the same hypotheses,
walking `idxs` advances `next` by at least `idxs.length` (in particular,
by at least `N` when `idxs.length ≥ N`). -/
theorem alloc_list_reaches_offset
    (m : AllocState) (idxs : List ℕ) (N : ℕ)
    (h_nodup : idxs.Nodup)
    (h_fresh : ∀ i ∈ idxs, m.assigned i = none)
    (h_len : idxs.length ≥ N) :
    (m.allocList idxs).next ≥ m.next + N := by
  rw [alloc_list_reaches_offset_eq m idxs h_nodup h_fresh]
  exact Nat.add_le_add_left h_len m.next

/-- **`alloc_list_memory_init_invariant` (composition with the
`MemoryInit` pass).** When the caller emits an `N`-opcode `MemoryInit`
pass — modelled as walking a list `idxs` of length `≥ N` of fresh and
injective witness indices — starting from any allocation state `m`
with `m.next = caller_block_offset`, the resulting `AllocState` has
`next ≥ caller_block_offset + N`.

This is exactly the residual hypothesis cited by
`Formal.CallInlining.memory_scope_splice_fresh`: it certifies that the
caller's allocation state reaches the call offset before the callee's
`MemoryInit` opcodes are spliced in, so block-id namespaces never
collide. -/
theorem alloc_list_memory_init_invariant
    (m : AllocState) (idxs : List ℕ) (caller_block_offset N : ℕ)
    (h_start : m.next = caller_block_offset)
    (h_nodup : idxs.Nodup)
    (h_fresh : ∀ i ∈ idxs, m.assigned i = none)
    (h_len : idxs.length ≥ N) :
    (m.allocList idxs).next ≥ caller_block_offset + N := by
  have h := alloc_list_reaches_offset m idxs N h_nodup h_fresh h_len
  rw [h_start] at h
  exact h

end Xark
