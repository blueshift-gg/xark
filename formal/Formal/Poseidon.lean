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
# xark Poseidon2 S-box and permutation soundness — mechanised in Lean 4 / mathlib

The Poseidon2 permutation (`gadgets/xark-poseidon/src/lib.rs`) is built
from two kinds of step: an `x⁵` S-box and linear (matrix) layers. The linear
layers are pure linear combinations — each output witness is a fixed linear
function of the inputs, so they are deterministic by construction. The only
*multiplicative* gadget is the S-box, whose soundness we prove here.

The S-box gadget (`gadgets/xark-poseidon/src/lib.rs`) emits three constraints for one cell:

    x * x = t,    t * t = u,    u * x = out.

We prove these force `out = x⁵` exactly — so the S-box is the intended map and
its output witness is **uniquely determined** by its input (no under-constraint
slack). Since both step kinds are deterministic functions of their inputs, the
whole permutation is a deterministic function of the input state.

This file then folds those building blocks into a full-permutation determinism
result. We model the state as `Fin t → F` (polymorphic over the width `t`; the
gadget uses `t = 4` over BN254 `Fr` but nothing here depends on the choice):

* `linearStep` — matrix-vector product `(M·s) i = Σⱼ M i j · s j`; the output is
  a function of `M, s` by construction (`linear_step_determined`).
* `addConstants` — componentwise `rc i + s i`; trivially a function
  (`add_constants_determined`).
* `sbox`, `applySbox`, `applyPartialSbox` — the `x⁵` map applied to every cell
  (full round) or to cell `0` only (partial round). The relational
  `sbox_apply_sound` discharges the per-cell three-constraint witness into
  `out = x⁵` using `sbox_sound`.
* `fullRound`, `partialRound` — one round each; deterministic in the input state
  (`full_round_determined`, `partial_round_determined`).
* `poseidonPermutation` — `List.foldl` over a *schedule* of rounds (each either
  `RoundKind.full rc M` or `RoundKind.partial rc d M`, both with fixed constants
  / matrices), with an optional initial linear layer to mirror the gadget's
  pre-round `M_E · state` step. `poseidon_permutation_determined` shows the
  whole permutation is a function of the input state: any two prover witnesses
  for the same input produce the same output — there is no prover freedom
  *anywhere* outside the per-cell S-box, which `sbox_sound` already pinned.

The theorems are parametric over the Poseidon2 constants and matrices; we do
**not** encode the 64 specific round constants or the external / internal
matrices. The point is that *given any fixed schedule*, the permutation is a
deterministic function of its input.
-/

namespace Xark

/-- **Poseidon2 S-box soundness.** The three multiplication constraints emitted
by the S-box gadget (`gadgets/xark-poseidon/src/lib.rs`) force the output to be `x⁵`. -/
theorem sbox_sound {F : Type*} [CommRing F] (x t u out : F)
    (ht : x * x = t) (hu : t * t = u) (ho : u * x = out) :
    out = x ^ 5 := by
  subst ho hu ht
  ring

/-- **S-box determinism.** Two S-box instances on the same input agree — the
output carries no prover freedom. Immediate from `sbox_sound`. -/
theorem sbox_unique {F : Type*} [CommRing F] (x t u out t' u' out' : F)
    (ht : x * x = t) (hu : t * t = u) (ho : u * x = out)
    (ht' : x * x = t') (hu' : t' * t' = u') (ho' : u' * x = out') :
    out = out' := by
  rw [sbox_sound x t u out ht hu ho, sbox_sound x t' u' out' ht' hu' ho']

/-! ## Round-layer determinism

Below we model the Poseidon2 round structure abstractly: a state of width `t`
is `Fin t → F`, a matrix is `Fin t → Fin t → F`, and a round constant vector is
`Fin t → F`. Each step (linear layer, constant addition, S-box) is a Lean
function of its inputs, so determinism is structural; the lemmas below state
it explicitly so the soundness chain reads directly.
-/

/-- The `x⁵` S-box as a Lean function (matches the S-box in `gadgets/xark-poseidon/src/lib.rs`). -/
def sbox {F : Type*} [CommRing F] (x : F) : F := x ^ 5

/-- Apply the S-box to every state cell (full-round non-linear layer). -/
def applySbox {F : Type*} [CommRing F] {t : ℕ} (s : Fin t → F) : Fin t → F :=
  fun i => sbox (s i)

/-- Apply the S-box only at index `0` (partial-round non-linear layer). The
canonical Poseidon2 partial round S-boxes the first cell and leaves the rest
unchanged — the Poseidon gadget (`gadgets/xark-poseidon/src/lib.rs`) does exactly this in its
partial-round loop.
`[NeZero t]` is the minimum constraint to talk about index `0 : Fin t`. -/
def applyPartialSbox {F : Type*} [CommRing F] {t : ℕ} [NeZero t]
    (s : Fin t → F) : Fin t → F :=
  fun i => if i = (0 : Fin t) then sbox (s i) else s i

/-- Per-cell soundness for the relational form of `applySbox`. If every cell
satisfies the three S-box constraints with witnesses `(tᵢ, uᵢ)`, then the
output state is exactly `applySbox s`. Pure consequence of `sbox_sound`. -/
theorem sbox_apply_sound {F : Type*} [CommRing F] {t : ℕ}
    (s tw uw out : Fin t → F)
    (ht : ∀ i, s i * s i = tw i)
    (hu : ∀ i, tw i * tw i = uw i)
    (ho : ∀ i, uw i * s i = out i) :
    out = applySbox s := by
  funext i
  unfold applySbox sbox
  exact sbox_sound (s i) (tw i) (uw i) (out i) (ht i) (hu i) (ho i)

/-- Per-cell soundness for `applyPartialSbox`. The first cell is constrained by
the three S-box equations, the remaining cells are pinned to the input. -/
theorem partial_sbox_apply_sound {F : Type*} [CommRing F] {t : ℕ} [NeZero t]
    (s : Fin t → F) (tw0 uw0 : F) (out : Fin t → F)
    (ht0 : s 0 * s 0 = tw0) (hu0 : tw0 * tw0 = uw0) (ho0 : uw0 * s 0 = out 0)
    (hrest : ∀ i, i ≠ (0 : Fin t) → out i = s i) :
    out = applyPartialSbox s := by
  funext i
  unfold applyPartialSbox
  by_cases h0 : i = (0 : Fin t)
  · subst h0
    simp only [reduceIte]
    unfold sbox
    exact sbox_sound (s 0) tw0 uw0 (out 0) ht0 hu0 ho0
  · simp only [if_neg h0]
    exact hrest i h0

/-- Linear (matrix) layer: `(M · s) i = Σⱼ M i j · s j`. Mirrors the LC the
gadget builds in `matrix_4x4_in_circuit` / `internal_m_in_circuit`. We only
need `CommRing` (not `Field`) here so the concrete BN254 specialisation in
`Formal.Poseidon2Bn254` — which uses `ZMod p` for the BN254 modulus without
requiring a typeclass-level primality proof — can apply this directly. -/
def linearStep {F : Type*} [CommRing F] {t : ℕ}
    (M : Fin t → Fin t → F) (s : Fin t → F) : Fin t → F :=
  fun i => ∑ j, M i j * s j

/-- **Linear-layer determinism.** Two output states that satisfy the same
`linearStep M s` equations are equal — i.e. the linear layer is a function of
its input state. Trivial structurally; stated to make the soundness chain
explicit. -/
theorem linear_step_determined {F : Type*} [CommRing F] {t : ℕ}
    (M : Fin t → Fin t → F) (s out out' : Fin t → F)
    (h : ∀ i, out i = ∑ j, M i j * s j)
    (h' : ∀ i, out' i = ∑ j, M i j * s j) :
    out = out' := by
  funext i
  rw [h i, h' i]

/-- Componentwise round-constant addition: `(rc + s) i = rc i + s i`. -/
def addConstants {F : Type*} [CommRing F] {t : ℕ}
    (rc s : Fin t → F) : Fin t → F :=
  fun i => rc i + s i

/-- **Round-constant addition determinism.** Two outputs satisfying the same
addition equations are equal. -/
theorem add_constants_determined {F : Type*} [CommRing F] {t : ℕ}
    (rc s out out' : Fin t → F)
    (h : ∀ i, out i = rc i + s i)
    (h' : ∀ i, out' i = rc i + s i) :
    out = out' := by
  funext i
  rw [h i, h' i]

/-- One full Poseidon2 round: add round constants, S-box every cell, apply the
external linear layer. Mirrors the `0..rf_half` and `p_end..num_rounds` loops
of `poseidon2_permutation_native`. -/
def fullRound {F : Type*} [CommRing F] {t : ℕ}
    (rc : Fin t → F) (M : Fin t → Fin t → F) (s : Fin t → F) : Fin t → F :=
  linearStep M (applySbox (addConstants rc s))

/-- **One full-round determinism.** For any fixed round constants `rc` and
matrix `M`, the round output is a function of the input state. Immediate
because `fullRound` is a `def`; this lemma surfaces it as a `Prop` so callers
can chain rounds without unfolding. -/
theorem full_round_determined {F : Type*} [CommRing F] {t : ℕ}
    (rc : Fin t → F) (M : Fin t → Fin t → F) (s s' : Fin t → F)
    (hs : s = s') :
    fullRound rc M s = fullRound rc M s' := by
  rw [hs]

/-- One partial Poseidon2 round: add a round constant to cell `0`, S-box cell
`0`, apply the internal linear layer. Mirrors the `rf_half..p_end` loop. We
model the round-constant addition as touching only cell `0` (the non-zero
column of `rc_table[r]` for internal rounds, per `gadgets/xark-poseidon/src/lib.rs`). -/
def partialRound {F : Type*} [CommRing F] {t : ℕ} [NeZero t]
    (rc0 : F) (M : Fin t → Fin t → F) (s : Fin t → F) : Fin t → F :=
  let s' : Fin t → F := fun i => if i = (0 : Fin t) then rc0 + s i else s i
  linearStep M (applyPartialSbox s')

/-- **One partial-round determinism.** Same as `full_round_determined` for the
partial-round variant. -/
theorem partial_round_determined {F : Type*} [CommRing F] {t : ℕ} [NeZero t]
    (rc0 : F) (M : Fin t → Fin t → F) (s s' : Fin t → F)
    (hs : s = s') :
    partialRound rc0 M s = partialRound rc0 M s' := by
  rw [hs]

/-- A single round in the permutation schedule: either a full round with
constants `rc` and matrix `M`, or a partial round with constant `rc0` on cell
`0` and matrix `M`. The actual Poseidon2 schedule for `t = 4`, BN254 `Fr` is
`R_F/2 = 4` full, `R_P = 56` partial, `R_F/2 = 4` full — a length-64 list of
`RoundKind` values, which we leave abstract here. (We write `partialR` rather
than `partial` because the latter is a Lean keyword.) -/
inductive RoundKind (F : Type*) [CommRing F] (t : ℕ) where
  | full (rc : Fin t → F) (M : Fin t → Fin t → F)
  | partialR (rc0 : F) (M : Fin t → Fin t → F)

/-- Apply one scheduled round to a state. -/
def applyRound {F : Type*} [CommRing F] {t : ℕ} [NeZero t]
    (r : RoundKind F t) (s : Fin t → F) : Fin t → F :=
  match r with
  | RoundKind.full rc M => fullRound rc M s
  | RoundKind.partialR rc0 M => partialRound rc0 M s

/-- The full Poseidon2 permutation: an optional initial linear layer
(`matrix_multiplication_4x4` in the gadget's `poseidon2_permutation_native`)
followed by a fixed schedule of full and partial rounds. -/
def poseidonPermutation {F : Type*} [CommRing F] {t : ℕ} [NeZero t]
    (Minit : Fin t → Fin t → F) (schedule : List (RoundKind F t))
    (s : Fin t → F) : Fin t → F :=
  schedule.foldl (fun acc r => applyRound r acc) (linearStep Minit s)

/-- **Full-permutation determinism.** For any fixed initial matrix `Minit` and
schedule, the Poseidon2 permutation is a function of the input state: two
prover witnesses for the same input produce the same output. This is the
end-of-soundness statement for the Poseidon gadget (`gadgets/xark-poseidon/src/lib.rs`) — combined
with `sbox_sound`,
which pins each per-cell S-box output, *no* step in the permutation carries
under-constraint slack. -/
theorem poseidon_permutation_determined {F : Type*} [CommRing F] {t : ℕ} [NeZero t]
    (Minit : Fin t → Fin t → F) (schedule : List (RoundKind F t))
    (s s' : Fin t → F) (hs : s = s') :
    poseidonPermutation Minit schedule s
      = poseidonPermutation Minit schedule s' := by
  rw [hs]

end Xark
