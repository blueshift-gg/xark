/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

-- The `style.header` linter hard-codes mathlib's Apache license string; this is
-- an MIT project, so disable that house-style check (it is not a correctness lint).
set_option linter.style.header false

/-!
# xark Merkle-membership soundness — mechanised in Lean 4 / mathlib

`gadgets/xark-merkle/src/lib.rs` verifies a Merkle authentication path by folding
it upward with the Poseidon 2-to-1 compression. At each level the running node is
combined with its sibling in the order dictated by a position bit `b`, using the
linear select

    select b t f = f + b·(t − f),

as `left = select b sib node`, `right = select b node sib`, then
`node' = hash2 left right`.

The Poseidon compression's determinacy is already mechanised
(`Formal/Poseidon.lean`, `poseidon_permutation_determined`). The *additional*
soundness fact a Merkle fold introduces is entirely about that select: given a
**boolean** position bit, the level's `(left, right)` is exactly the input pair
`(node, sib)` in one of the two orders — a genuine conditional swap, with **no
third value reachable**. So the only freedom a prover has at each level is the
position bit itself (which sibling side the node is on) — exactly the freedom a
Merkle membership proof is meant to expose. Everything else (the compression) is
a deterministic function of that pair.

The gadget pins `b` boolean with `b·b = b` (`assert_bool`), which is the sole
hypothesis of `merkle_level_swap_sound` below. The Rust↔Lean bridge test
`merkle_membership_gadget` / `merkle_matches_lean_model`
(`crates/lang/tests/snapshot.rs`) pins the gadget's per-level shape (one Poseidon
`hash2`, one booleanity gate, two select muxes) to this model.

* `merkle_select_pair_preserved` — the two selects always partition the pair:
  `left + right = node + sib`, regardless of `b` (a linear invariant).
* `merkle_level_swap_sound` — given `b·b = b`, the pair `(left, right)` equals
  `(node, sib)` or `(sib, node)`: a real swap, no under-constraint slack, no
  off-pair value a malicious prover could inject.
-/

namespace Xark

/-- The Merkle level's boolean-gated select, `select b t f = f + b·(t − f)`:
    `t` when `b = 1`, `f` when `b = 0`. -/
def merkleSelect {F : Type*} [Ring F] (b t f : F) : F := f + b * (t - f)

/-- The two per-level selects always partition the input pair: their sum is
    `node + sib` for **any** `b` (the `b` terms cancel). Combined with the swap
    lemma this shows `{left, right}` is exactly `{node, sib}` as a multiset — the
    fold can neither drop nor duplicate a value. -/
theorem merkle_select_pair_preserved {F : Type*} [CommRing F] (b node sib : F) :
    merkleSelect b sib node + merkleSelect b node sib = node + sib := by
  unfold merkleSelect; ring

/-- **Merkle level swap soundness.** With the position bit constrained boolean
    (`b·b = b`, as the gadget's `assert_bool` enforces), the level's ordered pair
    `(left, right) = (select b sib node, select b node sib)` is exactly the input
    pair in one of its two orders:

    * `b = 0` → `(node, sib)` (running node is the left child), or
    * `b = 1` → `(sib, node)` (running node is the right child).

    No other `(left, right)` is reachable, so the only prover freedom at the level
    is the position bit — the intended Merkle-membership freedom. This is what
    makes the linear select a *sound* conditional swap rather than an
    under-constrained mux. -/
theorem merkle_level_swap_sound {F : Type*} [Field F]
    (b node sib : F) (hb : b * b = b) :
    (merkleSelect b sib node = node ∧ merkleSelect b node sib = sib) ∨
    (merkleSelect b sib node = sib ∧ merkleSelect b node sib = node) := by
  have h : b * (b - 1) = 0 := by linear_combination hb
  rcases mul_eq_zero.mp h with hb0 | hb1
  · -- b = 0: the node stays on the left.
    left
    unfold merkleSelect
    refine ⟨?_, ?_⟩ <;> rw [hb0] <;> ring
  · -- b - 1 = 0, i.e. b = 1: the node moves to the right.
    right
    have hb1' : b = 1 := by linear_combination hb1
    unfold merkleSelect
    refine ⟨?_, ?_⟩ <;> rw [hb1'] <;> ring

end Xark
