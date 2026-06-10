/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Gadgets
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Variable-index memory-op soundness

Mirrors `crates/acir-r1cs/src/opcodes/memory.rs::lower_memory_op_variable_index`.
For an `n`-slot block under a variable index the gadget allocates:

* booleans `s_j ∈ {0, 1}` for `j ∈ [0, n)`,
* one row per slot: `s_j · (index − j) = 0`,
* a partition row `Σ s_j = 1`,
* (read case) per-slot products `t_j = s_j · arr_pre[j]`,
* (read case) the read-result row `value = Σ t_j`.

The selector layer is *functionally deterministic* over the index: given any
index `index ∈ {0, …, n−1}` exactly one `s_{index} = 1` and all others
`s_j = 0`.

The proof is parametric in the field, with one extra hypothesis:
`h_inj : ∀ a b : Fin n, (a.val : F) = (b.val : F) → a = b` — the natural-number
indices `{0, …, n−1}` embed injectively into the field. This is automatic for
BN254 `Fr` (`r ≈ 2^254` ≫ any `n` we'd ever use as a block length).
-/

namespace Xark

/-- **Selector partition determinism — variable-index `MemoryOp`.** Given a
boolean witness `s : Fin n → F` satisfying the gadget's selector layer for
a known index `index ∈ Fin n`:

* `s_j ∈ {0, 1}` (booleans),
* `s_j · (index − j) = 0` for each `j` (selector indicator constraints),
* `Σ s_j = 1` (partition / one-hot constraint),

then `s_{index} = 1` and `s_j = 0` for `j ≠ index`. Under-constraint slack
in the routing layer is ruled out. -/
theorem selector_partition_unique {F : Type*} [Field F] {n : ℕ}
    (s : Fin n → F) (index : Fin n)
    (h_bool : ∀ j, s j * (s j - 1) = 0)
    (h_ind : ∀ j : Fin n, s j * ((index.val : F) - (j.val : F)) = 0)
    (h_sum  : (∑ j : Fin n, s j) = 1)
    (h_inj  : ∀ a b : Fin n, (a.val : F) = (b.val : F) → a = b) :
    ∀ j, s j = if j = index then (1 : F) else 0 := by
  -- Boolean cases: each s_j ∈ {0, 1}.
  have hcase : ∀ j, s j = 0 ∨ s j = 1 := fun j => by
    rcases mul_eq_zero.mp (h_bool j) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  -- Off-diagonal slots: any j ≠ index must have s_j = 0.
  have hzero : ∀ j : Fin n, j ≠ index → s j = 0 := by
    intro j hjne
    rcases hcase j with h0 | h1
    · exact h0
    · -- s_j = 1; the indicator constraint gives (index.val - j.val : F) = 0.
      have hi := h_ind j
      rw [h1] at hi
      have hzdiff : (index.val : F) - (j.val : F) = 0 := by linear_combination hi
      have heq : (index.val : F) = (j.val : F) := by linear_combination hzdiff
      exact absurd (h_inj index j heq) hjne.symm
  intro j
  by_cases hj : j = index
  · -- Diagonal: s_{index} = 1 by partition (off-diagonal terms vanish).
    subst hj
    have hpart : s j = 1 := by
      have hcollapse : (∑ b : Fin n, s b) = s j := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          exact hzero k hkj
        · intro hcontra
          exact absurd (Finset.mem_univ j) hcontra
      have hsum := h_sum
      rw [hcollapse] at hsum
      exact hsum
    simp [hpart]
  · simp [hj, hzero j hj]

/-- **Read-value soundness.** Under the determined selector layer (output of
`selector_partition_unique`), the per-slot product row `t_j = s_j · arr_pre[j]`
and the result row `value = Σ t_j` pin `value = arr_pre[index]` uniquely. -/
theorem read_value_correct {F : Type*} [Field F] {n : ℕ}
    (s : Fin n → F) (arr_pre : Fin n → F) (t : Fin n → F) (value : F)
    (index : Fin n)
    (h_sel : ∀ j, s j = if j = index then (1 : F) else 0)
    (h_t : ∀ j, t j = s j * arr_pre j)
    (h_val : value = ∑ j : Fin n, t j) :
    value = arr_pre index := by
  rw [h_val]
  rw [Finset.sum_eq_single (a := index)]
  · rw [h_t index, h_sel index, if_pos rfl]; ring
  · intro k _ hkindex
    rw [h_t k, h_sel k, if_neg hkindex]; ring
  · intro hcontra
    exact absurd (Finset.mem_univ index) hcontra

/-- **Write soundness — selector-gated shadow update.** For a variable-index
write, each slot's post-state `arr_post[j]` is constrained by
`s_j · (value - arr_pre[j]) = arr_post[j] - arr_pre[j]`.

Under the determined selector layer (`s_j = 1[j = index]`):

* For `j = index`: `1 · (value - arr_pre[index]) = arr_post[index] - arr_pre[index]`
  ⇒ `arr_post[index] = value`.
* For `j ≠ index`: `0 · _ = arr_post[j] - arr_pre[j]`
  ⇒ `arr_post[j] = arr_pre[j]` (unchanged).

So the gadget faithfully implements "write `value` at `index`, leave other
slots unchanged" with no prover freedom. -/
theorem write_value_correct {F : Type*} [Field F] {n : ℕ}
    (s : Fin n → F) (arr_pre arr_post : Fin n → F) (value : F)
    (index : Fin n)
    (h_sel : ∀ j, s j = if j = index then (1 : F) else 0)
    (h_write : ∀ j, s j * (value - arr_pre j) = arr_post j - arr_pre j) :
    arr_post index = value ∧
    (∀ j, j ≠ index → arr_post j = arr_pre j) := by
  refine ⟨?_, ?_⟩
  · have hi := h_write index
    rw [h_sel index, if_pos rfl, one_mul] at hi
    linear_combination -hi
  · intro j hjne
    have hj := h_write j
    rw [h_sel j, if_neg hjne, zero_mul] at hj
    linear_combination -hj

end Xark
