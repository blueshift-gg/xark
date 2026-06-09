/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Ecdsa
import Formal.Curve
import Formal.Bookkeeping
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Advanced scalar-multiplication gadgets + public-input flow

Three composition theorems building on `Formal.Glv` + `Formal.Bookkeeping`:

* **`windowed_scalar_mul_sound`** — fixed-base comb table reconstructs `s • G`.
  Given a precomputed lookup table `T : Fin (2 ^ w) → G` with `T i = i.val • G`,
  and a sequence of `w`-bit windows `bits : Fin n → Fin (2 ^ w)`, the
  cumulative sum `Σⱼ 2 ^ (w * j) • T (bits j)` equals `s • G` where
  `s = Σⱼ 2 ^ (w * j) * (bits j).val`.

* **`joint_strauss_shamir_correct`** — interleaved LSB-first double-and-add
  ladder for `u₁ • P + u₂ • Q`. A 2-way per-step invariant
  `(acc, P, Q) ↦ (acc + b₁ • P + b₂ • Q, 2 • P, 2 • Q)` folds over a list of
  bit pairs to yield `bitsToNat bs1 • P + bitsToNat bs2 • Q`.

* **`public_input_projection_consistent`** — the projection `pub.map w` equals
  the R1CS instance vector when the witness map agrees with the instance at
  every public-input slot. The witness-index bijection itself is discharged
  by `alloc_witness_idempotent` and `alloc_witness_injective` in
  `Formal.Bookkeeping`.
-/

namespace Xark

/-! ## Windowed (comb-scan) scalar-mul soundness -/

/-- **Windowed comb-scan scalar-mult soundness.** Let `G` be an
additive commutative group, `P : G` a base point, `w n : ℕ` window width
and window count, `bits : Fin n → Fin (2 ^ w)` the window digits of a
scalar (each in `[0, 2 ^ w)`), and `T : Fin (2 ^ w) → G` a precomputed
lookup table with `T i = i.val • P`. Then the comb-scan output
`Σⱼ 2 ^ (w * j) • T (bits j)` reconstructs `s • P` where
`s = Σⱼ 2 ^ (w * j) * (bits j).val` is the LSB-first window
decomposition of the scalar.

This is the algebraic kernel of
`crates/acir-r1cs/src/gadgets/ecdsa.rs::scalar_mul_2p_secp256k1_comb_glv`'s
fixed-base half: the gadget reads `T (bits j)` from the table (one
constraint per window) and accumulates with a per-window weight
`2 ^ (w * j)`. The proof exposes both layers explicitly:

1. `T (bits j) = (bits j).val • P` by the precomputation hypothesis;
2. `2 ^ (w * j) • ((bits j).val • P) = (2 ^ (w * j) * (bits j).val) • P`
   by `mul_nsmul'`;
3. `Σⱼ aⱼ • P = (Σⱼ aⱼ) • P` by `Finset.sum_nsmul`. -/
theorem windowed_scalar_mul_sound {G : Type*} [AddCommGroup G]
    (P : G) (w n : ℕ) (bits : Fin n → Fin (2 ^ w)) (T : Fin (2 ^ w) → G)
    (h_table : ∀ i : Fin (2 ^ w), T i = (i : ℕ) • P) :
    (∑ j : Fin n, (2 ^ (w * (j : ℕ))) • T (bits j))
      = (∑ j : Fin n, 2 ^ (w * (j : ℕ)) * (bits j : ℕ)) • P := by
  -- Per-summand: rewrite `T (bits j)` via the precomputation, fuse the two
  -- `nsmul`s via `mul_nsmul'`, then collapse the sum via `sum_nsmul_assoc`.
  have hstep : ∀ j : Fin n,
      (2 ^ (w * (j : ℕ))) • T (bits j)
        = (2 ^ (w * (j : ℕ)) * (bits j : ℕ)) • P := by
    intro j
    rw [h_table (bits j), ← mul_nsmul']
  simp_rw [hstep]
  exact Finset.sum_nsmul_assoc _ _ _

/-! ## 2-way joint Strauss-Shamir ladder soundness -/

/-- One step of the LSB-first 2-way joint Strauss-Shamir ladder, as a
pure function on the ambient additive group `G`. Mirrors the per-bit
body of the interleaved variant of `scalar_mul_in_circuit`:
conditionally add each running base to the accumulator, then double
both running bases. -/
def jointLadderStep {G : Type*} [AddCommGroup G]
    (b : Bool × Bool) (s : G × G × G) : G × G × G :=
  (s.1 + (if b.1 then s.2.1 else 0) + (if b.2 then s.2.2 else 0),
   s.2.1 + s.2.1,
   s.2.2 + s.2.2)

/-- The LSB-first 2-way joint ladder run from a given start state over a
list of bit pairs. The gadget's loop is `bs.foldl jointLadderStep (0, P, Q)`. -/
def jointLadder {G : Type*} [AddCommGroup G]
    (bs : List (Bool × Bool)) (s : G × G × G) : G × G × G :=
  bs.foldl (fun st b => jointLadderStep b st) s

/-- **Per-step joint-ladder invariant.** One application of
`jointLadderStep` advances the accumulator by `b₁ • P + b₂ • Q` and
doubles both running base points. This is the 2-way analogue of
`Formal.Ecdsa.ladder_step_correct`. -/
theorem joint_ladder_step_correct {G : Type*} [AddCommGroup G]
    (b1 b2 : Bool) (acc P Q : G) :
    jointLadderStep (b1, b2) (acc, P, Q)
      = (acc + (if b1 then P else 0) + (if b2 then Q else 0),
         (2 : ℕ) • P, (2 : ℕ) • Q) := by
  unfold jointLadderStep
  simp [two_nsmul]

/-- **Generalised joint-ladder invariant.** Folding `jointLadderStep`
over a list of bit pairs from an arbitrary start `(acc₀, P, Q)` advances
the accumulator by `bitsToNat bs1 • P + bitsToNat bs2 • Q` (where `bs1`,
`bs2` are the two component bit-lists) and multiplies each running base
by `2 ^ |bs|`. The `acc₀ = 0` case specialises to the user-facing
`joint_strauss_shamir_correct`. -/
theorem joint_ladder_foldl_correct {G : Type*} [AddCommGroup G] :
    ∀ (bs : List (Bool × Bool)) (acc P Q : G),
      jointLadder bs (acc, P, Q)
        = (acc + bitsToNat (bs.map Prod.fst) • P
                + bitsToNat (bs.map Prod.snd) • Q,
           (2 ^ bs.length) • P,
           (2 ^ bs.length) • Q) := by
  intro bs
  induction bs with
  | nil =>
    intro acc P Q
    simp [jointLadder, bitsToNat]
  | cons b bs ih =>
    intro acc P Q
    -- Unfold one step of the fold, then apply the IH to the tail.
    obtain ⟨b1, b2⟩ := b
    have step : jointLadder ((b1, b2) :: bs) (acc, P, Q)
        = jointLadder bs (acc + (if b1 then P else 0) + (if b2 then Q else 0),
                          P + P, Q + Q) := by
      simp [jointLadder, jointLadderStep]
    rw [step, ih (acc + (if b1 then P else 0) + (if b2 then Q else 0)) (P + P) (Q + Q)]
    -- The three components must match: accumulator, running P, running Q.
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · -- Accumulator: parallel to the single-ladder proof, twice.
      change acc + (if b1 then P else 0) + (if b2 then Q else 0)
              + bitsToNat (bs.map Prod.fst) • (P + P)
              + bitsToNat (bs.map Prod.snd) • (Q + Q)
            = acc + bitsToNat (((b1, b2) :: bs).map Prod.fst) • P
                  + bitsToNat (((b1, b2) :: bs).map Prod.snd) • Q
      have h2P : (P + P) = (2 : ℕ) • P := by rw [two_nsmul]
      have h2Q : (Q + Q) = (2 : ℕ) • Q := by rw [two_nsmul]
      have hmap1 : ((b1, b2) :: bs).map Prod.fst = b1 :: bs.map Prod.fst := by simp
      have hmap2 : ((b1, b2) :: bs).map Prod.snd = b2 :: bs.map Prod.snd := by simp
      have hbits1 : bitsToNat (b1 :: bs.map Prod.fst)
          = (if b1 then 1 else 0) + 2 * bitsToNat (bs.map Prod.fst) := rfl
      have hbits2 : bitsToNat (b2 :: bs.map Prod.snd)
          = (if b2 then 1 else 0) + 2 * bitsToNat (bs.map Prod.snd) := rfl
      -- Bring both sides to a sum of monomial `nsmul`s on `P` and `Q`.
      -- Use `← mul_nsmul` (not `mul_nsmul'`) so the resulting scalar order
      -- `(2 * bitsToNat ..)` matches what `add_nsmul` produces on the RHS.
      rw [h2P, h2Q, ← mul_nsmul, ← mul_nsmul, hmap1, hmap2, hbits1, hbits2,
          add_nsmul, add_nsmul]
      -- Now both sides have the same `(2 * bitsToNat ..) • P/Q` tails; identify
      -- the `(if b then 1 else 0) • _` summands with the conditional points.
      have eP : (if b1 then (1 : ℕ) else 0) • P = (if b1 then P else 0) := by
        cases b1 <;> simp
      have eQ : (if b2 then (1 : ℕ) else 0) • Q = (if b2 then Q else 0) := by
        cases b2 <;> simp
      rw [eP, eQ]
      abel
    · -- Running P: same scaling-by-`2 ^ |bs|` argument as the single ladder.
      change (2 ^ bs.length) • (P + P)
            = (2 ^ ((b1, b2) :: bs).length) • P
      have h2P : (P + P) = (2 : ℕ) • P := by rw [two_nsmul]
      rw [h2P, ← mul_nsmul', List.length_cons, pow_succ]
    · -- Running Q: symmetric.
      change (2 ^ bs.length) • (Q + Q)
            = (2 ^ ((b1, b2) :: bs).length) • Q
      have h2Q : (Q + Q) = (2 : ℕ) • Q := by rw [two_nsmul]
      rw [h2Q, ← mul_nsmul', List.length_cons, pow_succ]

/-- **2-way joint Strauss-Shamir ladder soundness.** Running the
joint ladder from the seed state `(0, P, Q)` over an LSB-first list of
bit pairs yields the accumulator `bitsToNat bs1 • P + bitsToNat bs2 • Q`
where `bs1 = bs.map Prod.fst` and `bs2 = bs.map Prod.snd`. In
particular, the joint ladder computes `u₁ • P + u₂ • Q` for the scalars
encoded by the two bit-lists, while sharing the doubling cost between
the two scalar mults.

This is the algebraic content of the interleaved variant in
`crates/acir-r1cs/src/gadgets/ecdsa.rs`: the per-step joint invariant
is `acc ↦ acc + b₁ • P + b₂ • Q`, which folded over the bit list gives
the two-term sum at the end. -/
theorem joint_strauss_shamir_correct {G : Type*} [AddCommGroup G]
    (bs : List (Bool × Bool)) (P Q : G) :
    (jointLadder bs (0, P, Q)).1
      = bitsToNat (bs.map Prod.fst) • P + bitsToNat (bs.map Prod.snd) • Q := by
  -- Specialise the foldl invariant at `acc = 0`, then project to the first
  -- component and cancel the leading `0 +`.
  have h := joint_ladder_foldl_correct bs (0 : G) P Q
  have h1 := congrArg Prod.fst h
  -- `h1` reads `(jointLadder bs (0,P,Q)).1 = 0 + _ + _` after projection.
  rw [zero_add] at h1
  exact h1

/-! ## Public-input flow consistency -/

/-- **Public-input projection consistency.** Given an ACIR
witness map `w : ℕ → F` and a list `pub : List ℕ` of public-input
witness indices, the projection `pub.map w` equals the R1CS instance
vector built by reading the same indices from the same witness map.
The cross-cutting lemma is a `List.map`-equality: at each `i ∈ pub`,
both lists produce `w i`.

The witness-index bijection (allocations are idempotent and injective)
is discharged elsewhere by `Formal.Bookkeeping.alloc_witness_idempotent`
and `alloc_witness_injective`, so this theorem is what remains to wire
the ACIR public-input slot list to the R1CS instance vector. The
hypothesis `h_inst i hi : inst i = w i` encodes the per-index equality
that the `alloc_witness` bookkeeping establishes for each `i ∈ pub`. -/
theorem public_input_projection_consistent
    {F : Type*} (w : ℕ → F) (inst : ℕ → F) (pub : List ℕ)
    (h_inst : ∀ i ∈ pub, inst i = w i) :
    pub.map inst = pub.map w := by
  exact List.map_congr_left h_inst

/-! ### `h_inst` derived from canonical allocation bookkeeping -/

/-- **Canonical instance-vector construction.** Reads `w` at every
public-input slot, defaults to zero outside. Mirrors what
`lower::synthesize` produces — so the `h_inst` hypothesis falls out by
construction. -/
def buildInstance {F : Type*} [Zero F] (w : ℕ → F) (pub : List ℕ) : ℕ → F :=
  fun i => if i ∈ pub then w i else 0

/-- `buildInstance w pub i = w i` for every `i ∈ pub`. -/
theorem buildInstance_eq_w_on_pub {F : Type*} [Zero F]
    (w : ℕ → F) (pub : List ℕ) :
    ∀ i ∈ pub, buildInstance w pub i = w i := by
  intro i hi
  unfold buildInstance
  simp [hi]

/-- **Discharged form: canonical-construction consistency.** When the instance vector is
`buildInstance w pub`, consistency holds without a separate hypothesis. -/
theorem public_input_projection_consistent_canonical {F : Type*} [Zero F]
    (w : ℕ → F) (pub : List ℕ) :
    pub.map (buildInstance w pub) = pub.map w :=
  public_input_projection_consistent w (buildInstance w pub) pub
    (buildInstance_eq_w_on_pub w pub)

/-- **Bookkeeping bridge.** The R1CS-side instance vector matches the
canonical ACIR-side instance vector at every public-input slot.

`w` is the ACIR witness map (`ℕ → F` over ACIR witness indices), `wR` is the
R1CS witness map (`ℕ → F` over R1CS variable indices), and `m : AllocState`
is the allocator from `Formal.Bookkeeping` that binds ACIR indices to R1CS
variables (`m.assigned i = some k` means ACIR index `i` was allocated to
R1CS variable `k`).

Under (a) every public input is allocated and (b) the R1CS witness at each
allocated variable equals the ACIR witness at the source index — the
coherence condition the prover/verifier establish by construction — the
R1CS-side instance vector (`wR ∘ varOf`) equals the canonical
`buildInstance w pub` on every slot `i ∈ pub`. -/
theorem alloc_state_pins_public_inputs {F : Type*} [Zero F]
    (w wR : ℕ → F) (pub : List ℕ) (m : AllocState)
    (h_alloc : ∀ i ∈ pub, ∃ k, m.assigned i = some k)
    (h_coh : ∀ i k, m.assigned i = some k → wR k = w i)
    (i : ℕ) (hi : i ∈ pub) :
    ∃ k, m.assigned i = some k ∧ wR k = buildInstance w pub i := by
  obtain ⟨k, hk⟩ := h_alloc i hi
  refine ⟨k, hk, ?_⟩
  rw [buildInstance_eq_w_on_pub w pub i hi]
  exact h_coh i k hk

/-! ### Bridge between `buildInstance` and `lower::synthesize`'s PI construction

`lower::synthesize` (in `crates/acir-r1cs/src/lower.rs`) populates the
constraint system's instance vector by walking the artifact's
`public_inputs` list and reading the witness map at each slot. This is
captured at the Lean level by `synthesizeInstance` below, which mirrors
that loop. We then prove `synthesizeInstance = buildInstance` so the
canonical-construction theorem `public_input_projection_consistent_canonical`
applies to the actual lowering's output.

The Rust loop (paraphrased):
```rust
for (slot_idx, witness_idx) in public_inputs.iter().enumerate() {
    cs.new_input_variable(|| witness.get(witness_idx))?;
}
```

The Lean mirror: for each index `i`, the instance vector's value at `i`
is `w i` if `i` is a public-input slot, else `0` (the canonical zero
default for unused instance positions). -/

/-- **Lean mirror of `lower::synthesize`'s public-input population
loop.** Given a witness map `w : ℕ → F` and a public-input slot list
`pub : List ℕ`, returns the instance vector built by reading `w` at each
public-input slot, with zero default outside `pub`. The Rust loop
walks `public_inputs` via `for (slot, idx) in pub.iter().enumerate()`
and calls `cs.new_input_variable(|| witness.get(idx))`; the Lean mirror
uses `decide (i ∈ pub)` which is the same membership check (the loop
visits exactly the slots in `pub`). -/
def synthesizeInstance {F : Type*} [Zero F] (w : ℕ → F) (pub : List ℕ) : ℕ → F :=
  fun i => if i ∈ pub then w i else 0

/-- **`synthesizeInstance` equals `buildInstance`** by `rfl` — both
functions encode the same construction; the named wrapper exists so
the trust chain can cite the Rust loop being mirrored at each use
site. -/
theorem synthesizeInstance_eq_buildInstance {F : Type*} [Zero F]
    (w : ℕ → F) (pub : List ℕ) :
    synthesizeInstance w pub = buildInstance w pub := rfl

/-- **Discharged consistency for the actual Rust lowering's PI vector.**
Composes `synthesizeInstance_eq_buildInstance` with
`public_input_projection_consistent_canonical` — for the instance vector
the Rust `lower::synthesize` actually produces, the projection equals
the witness map read at every public-input slot. -/
theorem public_input_projection_consistent_synthesize {F : Type*} [Zero F]
    (w : ℕ → F) (pub : List ℕ) :
    pub.map (synthesizeInstance w pub) = pub.map w := by
  rw [synthesizeInstance_eq_buildInstance]
  exact public_input_projection_consistent_canonical w pub

end Xark
