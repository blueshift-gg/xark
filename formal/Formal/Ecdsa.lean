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
# xark double-and-add ladder soundness — Layer B, mechanised in Lean 4 / mathlib

`crates/acir-r1cs/src/gadgets/curve.rs::scalar_mul_in_circuit` (and the
`msm_in_circuit` that calls it, plus the ECDSA verifier in
`crates/acir-r1cs/src/gadgets/ecdsa.rs`) computes `s · P` in-circuit by the
standard LSB-first **double-and-add** ladder:

    acc      := 0                       -- point at infinity
    running  := P
    for each bit b of s (LSB first):
        acc      := acc + (if b then running else 0)
        running  := running + running    -- doubling

We prove the *combinatorial* correctness of this loop, abstractly over any
additive commutative group `G`. The curve-arithmetic correctness of point
addition (closure of the addition law, slope determinism) lives separately in
`Formal.Curve`; here we only need the group structure. The two layers compose:
specialise `G` to the Grumpkin point group and the same theorem closes the
soundness story for `scalar_mul_in_circuit`.

* `ladder_step_correct` — the per-bit invariant: one application of the
  primitive sends `(acc, P) ↦ (acc + b·P, 2·P)`.
* `ladder_correct` — running the ladder from `(0, P)` over a bit-list `bs`
  produces accumulator `(∑ᵢ (if bs[i] then 2^i else 0)) • P` and running point
  `2^bs.length • P`. Equivalently, the accumulator is `bitsToNat bs • P`, the
  natural number encoded by the LSB-first bit-list.
* `ladder_determinism` — corollary: bit-vectors encoding the same scalar give
  the same ladder output. Combined with `bits_unique` from `Formal.Gadgets`,
  this closes the under-constraint story for the scalar-mul ladder: the
  in-circuit accumulator is a function of the *scalar*, not of the witness
  bit-vector chosen by the prover.

Scope: this file is group-theoretic only. It does not cover field/curve
correctness (see `Formal.Curve`), nor the `(lo, hi)` 128-bit limb concatenation
in `msm_in_circuit` — that is a trivial repackaging of the same bit list.
-/

namespace Xark

/-- One step of the LSB-first double-and-add ladder, as a pure function on the
ambient additive group `G`. Mirrors the per-bit body of
`scalar_mul_in_circuit`: conditionally add the running base to the
accumulator, then double the running base. -/
def ladderStep {G : Type*} [AddCommGroup G] (b : Bool) (s : G × G) : G × G :=
  (s.1 + (if b then s.2 else 0), s.2 + s.2)

/-- The LSB-first ladder run from a given start state over a bit-list. The
gadget's loop is `bs.foldl ladderStep (0, P)`. -/
def ladder {G : Type*} [AddCommGroup G] (bs : List Bool) (s : G × G) : G × G :=
  bs.foldl (fun st b => ladderStep b st) s

/-- LSB-first interpretation of a bit-list as a natural number:
`bitsToNat [b₀, b₁, …, bₙ₋₁] = b₀ + 2·b₁ + … + 2^(n-1)·bₙ₋₁`. -/
def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- **Per-step ladder invariant.** One application of `ladderStep` advances the
accumulator by `b·P` (i.e. by `P` when `b = true`, by `0` when `b = false`)
and doubles the running base point. This is exactly the per-bit behaviour of
`scalar_mul_in_circuit`; it seeds the induction for `ladder_correct`. -/
theorem ladder_step_correct {G : Type*} [AddCommGroup G] (b : Bool) (acc P : G) :
    ladderStep b (acc, P) = (acc + (if b then P else 0), (2 : ℕ) • P) := by
  unfold ladderStep
  simp [two_nsmul]

/-- **Generalised ladder invariant.** Folding `ladderStep` over a bit-list from
an arbitrary start `(acc₀, P)` advances the accumulator by the scalar encoded
by the bit-list times `P`, and multiplies the running base by `2 ^ |bs|`.
The `acc₀ = 0` case is `ladder_correct`. The generalisation is what makes the
list-induction go through (the inductive step changes `acc₀`). -/
theorem ladder_foldl_correct {G : Type*} [AddCommGroup G] :
    ∀ (bs : List Bool) (acc P : G),
      ladder bs (acc, P) = (acc + bitsToNat bs • P, (2 ^ bs.length) • P) := by
  intro bs
  induction bs with
  | nil =>
    intro acc P
    simp [ladder, bitsToNat]
  | cons b bs ih =>
    intro acc P
    -- Unfold one step of the fold, then apply the IH to the tail.
    have step : ladder (b :: bs) (acc, P)
        = ladder bs (acc + (if b then P else 0), P + P) := by
      simp [ladder, ladderStep]
    rw [step, ih (acc + (if b then P else 0)) (P + P)]
    -- The two components must match: accumulator scalar and base point scaling.
    refine Prod.ext ?_ ?_
    · -- Accumulator: `acc + b·P + bitsToNat bs • (2·P) = acc + bitsToNat (b::bs) • P`.
      change acc + (if b then P else 0) + bitsToNat bs • (P + P)
        = acc + bitsToNat (b :: bs) • P
      have h2P : (P + P) = (2 : ℕ) • P := by rw [two_nsmul]
      have hbits : bitsToNat (b :: bs) = (if b then 1 else 0) + 2 * bitsToNat bs := rfl
      rw [h2P, ← mul_nsmul', hbits, add_nsmul, add_assoc, mul_comm 2 (bitsToNat bs)]
      congr 1
      cases b <;> simp
    · -- Running base: `2 ^ bs.length • (P + P) = 2 ^ (bs.length + 1) • P`.
      change (2 ^ bs.length) • (P + P) = (2 ^ (b :: bs).length) • P
      have h2P : (P + P) = (2 : ℕ) • P := by rw [two_nsmul]
      rw [h2P, ← mul_nsmul', List.length_cons, pow_succ, Nat.mul_comm]

/-- **Ladder correctness (LSB-first double-and-add).** Running the ladder from
the seed state `(0, P)` over an LSB-first bit-list `bs` yields the accumulator
`bitsToNat bs • P` and running point `2 ^ bs.length • P`. In particular, the
final accumulator is `scalar • P` for the natural-number scalar encoded by
`bs`, matching the spec of `scalar_mul_in_circuit`. -/
theorem ladder_correct {G : Type*} [AddCommGroup G] (bs : List Bool) (P : G) :
    ladder bs (0, P) = (bitsToNat bs • P, (2 ^ bs.length) • P) := by
  have := ladder_foldl_correct bs (0 : G) P
  simpa using this

/-- **Ladder determinism / witness independence.** Two bit-lists of the same
length that encode the same scalar produce the same ladder output. Combined
with `bits_unique` in `Formal.Gadgets` (the bit-vector is pinned by the value
of the recomposition sum), this discharges under-constraint slack for the
scalar-mul gadget: the prover cannot witness an off-spec accumulator by
choosing a different bit-decomposition of the same scalar. -/
theorem ladder_determinism {G : Type*} [AddCommGroup G]
    (bs bs' : List Bool) (P : G)
    (hlen : bs.length = bs'.length) (hval : bitsToNat bs = bitsToNat bs') :
    ladder bs (0, P) = ladder bs' (0, P) := by
  rw [ladder_correct, ladder_correct, hlen, hval]

end Xark
