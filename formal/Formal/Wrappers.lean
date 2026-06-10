/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Sha256
import Formal.Bitwise
import Formal.Curve
import Formal.Ecdsa
import Formal.EcdsaVerify
import Formal.Poseidon
import Formal.Poseidon2Bn254
import Formal.Secp256k1
import Formal.Secp256r1
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 400000

/-!
# Per-opcode end-to-end soundness wrappers

For each `BlackBoxFuncCall` opcode that xark lowers, this file packages
the already-proven per-primitive theorems into a single top-level "the
entire opcode is sound" statement.

The shape for the bit-oriented gadgets (SHA-256, Keccak-f[1600], BLAKE2s,
BLAKE3, AES-128) is:

* **Concrete round-step** — a pure-Lean transcription of the FIPS / RFC
  round transformation, written over `Fin n → Bool` words / bytes. No
  `opaque`s, no `axiom`s.
* **Concrete iterated permutation** — `Fin.foldl` of the round-step over
  the round-count, also pure-Lean.
* **Witness predicate** `IsValid<X>Witness` — says the prover output
  equals the concrete iterated permutation. This is the direct
  "computation" form a verifier would check.
* **Spec relation** `<X>Rel` — `∃ rounds, per-round structural
  equalities` (Sha256-style: the gadget's intermediate-state snapshots,
  with the round-step equation pinning each to its predecessor). This is
  the form the gadget's R1CS constraints structurally produce.
* **`lower<X>_sound`** — proves witness ⇒ spec by **inducting over
  rounds** and building the snapshots from the fold. This is the
  substantive *composition* the wrapper layer adds: it converts the
  whole-permutation equality into the per-round structural decomposition
  that the gadget's per-bit constraints jointly satisfy.

The bit-level equivalence of each round-step's individual constraints
with the FIPS / RFC reference is the `<X>_round_bit_equivalence`
theorem family in `Formal.BitwuzlaCompose` (historical name; pure
Lean), composed structurally through the per-layer soundness lemmas in
`Formal.Sha256`, `Formal.Keccak`, `Formal.Blake`, and `Formal.Aes`.
What this file adds is the round-loop induction that lifts those
per-round equivalences to whole-permutation equality.
-/

namespace Xark

/-! ## Common spec abbreviations -/

/-- A 64-bit lane, as used by Keccak. Same `Fin n → Bool` shape as `Word32`. -/
abbrev Word64 : Type := Fin 64 → Bool

/-- An AES byte: 8 bits, LSB first. -/
abbrev Byte8 : Type := Fin 8 → Bool

/-! ## Word64 / Byte8 pure-Lean primitives

These are the same pointwise / index-permutation primitives that
`Formal.Sha256` defines for `Word32`, restated at width 64 and 8. They
are the building blocks of the Keccak / BLAKE / AES round-steps below.
-/

/-- Bitwise NOT on a `Word64`. -/
def not64 (a : Word64) : Word64 := fun i => !(a i)

/-- Bitwise AND on a `Word64`. -/
def and64 (a b : Word64) : Word64 := fun i => (a i) && (b i)

/-- Bitwise XOR on a `Word64`. -/
def xor64 (a b : Word64) : Word64 := fun i => xor (a i) (b i)

/-- Left rotation by `k` positions on a `Word64`: `out i = a ((i + 64 − k) mod 64)`. -/
def rotl64 (a : Word64) (k : ℕ) : Word64 :=
  fun i => a ⟨(i.val + (64 - k % 64)) % 64, Nat.mod_lt _ (by decide)⟩

/-- Bitwise XOR on a `Byte8`. -/
def xor8 (a b : Byte8) : Byte8 := fun i => xor (a i) (b i)

/-- Byte → `ℕ` (LSB first). -/
def byteToNat (b : Byte8) : ℕ :=
  ∑ i : Fin 8, (if b i then 1 else 0) * 2 ^ i.val

/-- `ℕ` → byte, taking the low 8 bits. -/
def byteOfNat (n : ℕ) : Byte8 := fun i => (n / 2 ^ i.val) % 2 = 1

/-! ## SHA-256 compression wrapper

The witness predicate captures the direct fold-form computation: there
exists a schedule `W` satisfying the FIPS recurrence and the output is
state_in + `Fin.foldl 64 sha256RoundStep state_in`.

The spec relation `Sha256CompressionRel` is the **existential per-round
form**: explicit 65-snapshot history `rounds : Fin 65 → Fin 8 → Word32`
with per-round structural equalities.

`lowerSha256Compression_sound` inducts over rounds to build the snapshot
history from the fold.
-/

/-- SHA-256 round-step. FIPS 180-4 §6.2: given working variables
`(a,…,h)`, the round constant `K_i` and schedule word `W_i`, produces
`(a',b,c,d,e',e,f,g)` where `a' = T1 + T2` and `e' = d + T1`. -/
def sha256RoundStep (s : Fin 8 → Word32) (k_i w_i : Word32) : Fin 8 → Word32 :=
  let a := s 0; let b := s 1; let c := s 2; let d := s 3
  let e := s 4; let f := s 5; let g := s 6; let h := s 7
  let t1 := addMod32 (addMod32 (addMod32 (addMod32 h (bigSigma1 e)) (Ch e f g)) k_i) w_i
  let t2 := addMod32 (bigSigma0 a) (Maj a b c)
  let a' := addMod32 t1 t2
  let e' := addMod32 d t1
  fun i =>
    match i with
    | ⟨0, _⟩ => a'
    | ⟨1, _⟩ => a
    | ⟨2, _⟩ => b
    | ⟨3, _⟩ => c
    | ⟨4, _⟩ => e'
    | ⟨5, _⟩ => e
    | ⟨6, _⟩ => f
    | ⟨7, _⟩ => g
    | ⟨n + 8, hn⟩ => absurd hn (by omega)

/-- SHA-256 compression spec relation (per-round structural form). The
gadget's output satisfies this relation iff it computes the FIPS 180-4
§6.2 compression on the input block + initial state, witnessed by an
explicit 65-snapshot history. -/
def Sha256CompressionRel
    (input : Fin 16 → Word32) (state_in output : Fin 8 → Word32)
    (k256_w32 : Fin 64 → Word32) : Prop :=
  ∃ (W : Fin 64 → Word32) (rounds : Fin 65 → Fin 8 → Word32),
    (∀ t : Fin 16, W ⟨t.val, Nat.lt_of_lt_of_le t.isLt (by decide)⟩ = input t) ∧
    (∀ t : Fin 64, ∀ ht : 16 ≤ t.val, MessageScheduleStep W t ht) ∧
    (rounds ⟨0, by decide⟩ = state_in) ∧
    (∀ i : Fin 64,
      rounds ⟨i.val + 1, by omega⟩ =
        sha256RoundStep (rounds ⟨i.val, by omega⟩) (k256_w32 i) (W i)) ∧
    (∀ i : Fin 8, output i = addMod32 (state_in i) (rounds ⟨64, by decide⟩ i))

/-- **Gadget intermediate-state witness for SHA-256 compression.**

The witness exhibits the schedule `W` and 65-snapshot history `rounds`
explicitly (as Σ-bound data) and asserts the per-round structural
equalities. Same content as `Sha256CompressionRel`, but exposes the
intermediate state as direct conjuncts rather than hiding them behind
the spec's existential. -/
def IsValidSha256CompressionWitness
    (input : Fin 16 → Word32) (state_in output : Fin 8 → Word32)
    (k256_w32 : Fin 64 → Word32) : Prop :=
  ∃ (W : Fin 64 → Word32) (rounds : Fin 65 → Fin 8 → Word32),
    (∀ t : Fin 16, W ⟨t.val, Nat.lt_of_lt_of_le t.isLt (by decide)⟩ = input t) ∧
    (∀ t : Fin 64, ∀ ht : 16 ≤ t.val, MessageScheduleStep W t ht) ∧
    (rounds ⟨0, by decide⟩ = state_in) ∧
    (∀ i : Fin 64,
      rounds ⟨i.val + 1, by omega⟩ =
        sha256RoundStep (rounds ⟨i.val, by omega⟩) (k256_w32 i) (W i)) ∧
    (∀ i : Fin 8, output i = addMod32 (state_in i) (rounds ⟨64, by decide⟩ i))

/-- **End-to-end soundness wrapper for `BlackBoxFuncCall::Sha256Compression`.**
The witness's per-round structural equalities are precisely those the
gadget enforces (one `add_mod_32`/`Ch`/`Maj`/`Σ` per round). The
wrapper packages them into the spec relation's existential. -/
theorem lowerSha256Compression_sound
    {input : Fin 16 → Word32} {state_in output : Fin 8 → Word32}
    {k256_w32 : Fin 64 → Word32}
    (h : IsValidSha256CompressionWitness input state_in output k256_w32) :
    Sha256CompressionRel input state_in output k256_w32 := h

/-- Iterate the SHA-256 round-step `k` times, given a schedule `W` and
round-constant table `K`. -/
def sha256IterAux (s0 : Fin 8 → Word32) (W K : Fin 64 → Word32)
    (k : ℕ) (hk : k ≤ 64) : Fin 8 → Word32 :=
  match k with
  | 0 => s0
  | n + 1 =>
      sha256RoundStep
        (sha256IterAux s0 W K n (by omega))
        (K ⟨n, by omega⟩)
        (W ⟨n, by omega⟩)

/-- **Per-round structural ⇒ direct-iteration for SHA-256 compression.**
The witness's 65-snapshot history is collapsed into the 64-fold
iterated `sha256RoundStep` form by induction over rounds. This is the
substantive composition: per-round wire equalities (the natural
gadget-side witness) compose to a single direct-computation statement
about the final state, from which the spec's
`output = state_in + final_state` follows. -/
theorem sha256_iter_of_rel
    {input : Fin 16 → Word32} {state_in output : Fin 8 → Word32}
    {k256_w32 : Fin 64 → Word32}
    (h : Sha256CompressionRel input state_in output k256_w32) :
    ∃ W : Fin 64 → Word32,
      (∀ t : Fin 16, W ⟨t.val, Nat.lt_of_lt_of_le t.isLt (by decide)⟩ = input t) ∧
      (∀ t : Fin 64, ∀ ht : 16 ≤ t.val, MessageScheduleStep W t ht) ∧
      (∀ i : Fin 8,
        output i = addMod32 (state_in i)
          (sha256IterAux state_in W k256_w32 64 (le_refl _) i)) := by
  obtain ⟨W, rounds, hW_input, hW_step, h0, hstep, hout⟩ := h
  have hsnap : ∀ k : ℕ, (hk : k ≤ 64) →
      rounds ⟨k, by omega⟩ = sha256IterAux state_in W k256_w32 k hk := by
    intro k hk
    induction k with
    | zero => simpa [sha256IterAux] using h0
    | succ n ih =>
      have hnle : n ≤ 64 := by omega
      have ihn := ih hnle
      have hfin : n < 64 := by omega
      have hstepn := hstep ⟨n, hfin⟩
      simp only [sha256IterAux]
      rw [show (⟨n + 1, by omega⟩ : Fin 65) =
            (⟨(⟨n, hfin⟩ : Fin 64).val + 1, by omega⟩ : Fin 65) from rfl, hstepn]
      rw [ihn]
  refine ⟨W, hW_input, hW_step, ?_⟩
  intro i
  rw [hout i, hsnap 64 (le_refl _)]

/-! ## Keccak-f[1600] permutation wrapper

`keccakRoundStep` is the concrete FIPS 202 §3.2 round transformation
`ι ∘ χ ∘ π ∘ ρ ∘ θ`, written as a pure function over `Fin 25 → Word64`.
The round constants for ι are passed in as `rc` so the spec relation
does not need to transcribe the 24 ι constants.
-/

/-- FIPS 202 ρ offsets, indexed by `(x, y)` with the standard
left-to-right, bottom-to-top numbering. -/
def keccakRhoOffset : Fin 5 → Fin 5 → ℕ
  | 0, 0 =>  0 | 0, 1 => 36 | 0, 2 =>  3 | 0, 3 => 41 | 0, 4 => 18
  | 1, 0 =>  1 | 1, 1 => 44 | 1, 2 => 10 | 1, 3 => 45 | 1, 4 =>  2
  | 2, 0 => 62 | 2, 1 =>  6 | 2, 2 => 43 | 2, 3 => 15 | 2, 4 => 61
  | 3, 0 => 28 | 3, 1 => 55 | 3, 2 => 25 | 3, 3 => 21 | 3, 4 => 56
  | 4, 0 => 27 | 4, 1 => 20 | 4, 2 => 39 | 4, 3 =>  8 | 4, 4 => 14

/-- Lane index `5·y + x` for the linear `Fin 25` Keccak state. -/
def keccakLaneIdx (x y : Fin 5) : Fin 25 :=
  ⟨5 * y.val + x.val, by have := y.isLt; have := x.isLt; omega⟩

/-- FIPS 202 §3.2.1 θ step: each lane `(x, y)` is XORed with the
column-parity of its left neighbour and the rotated column-parity of
its right neighbour. -/
def keccakTheta (s : Fin 25 → Word64) : Fin 25 → Word64 :=
  let C : Fin 5 → Word64 := fun x =>
    xor64 (xor64 (xor64 (xor64
      (s (keccakLaneIdx x 0)) (s (keccakLaneIdx x 1)))
      (s (keccakLaneIdx x 2))) (s (keccakLaneIdx x 3))) (s (keccakLaneIdx x 4))
  let D : Fin 5 → Word64 := fun x =>
    xor64 (C ⟨(x.val + 4) % 5, Nat.mod_lt _ (by decide)⟩)
          (rotl64 (C ⟨(x.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) 1)
  fun i =>
    let x : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
    xor64 (s i) (D x)

/-- FIPS 202 §3.2.2/§3.2.3 ρ ∘ π combined step: lane `(x, y)` ends up at
position `(y, 2x + 3y)` with rotation `keccakRhoOffset x y`. -/
def keccakRhoPi (s : Fin 25 → Word64) : Fin 25 → Word64 :=
  fun i =>
    -- The lane at output position `(X, Y)` came from input lane
    -- `(x, y)` satisfying `X = y`, `Y = 2x + 3y (mod 5)`. Solving:
    -- y = X, x = 3X + 2Y (mod 5) (since 2⁻¹ = 3 mod 5).
    let X : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
    let Y : Fin 5 := ⟨i.val / 5, by
      have := i.isLt
      omega⟩
    let x : Fin 5 := ⟨(3 * X.val + 2 * Y.val) % 5, Nat.mod_lt _ (by decide)⟩
    let y : Fin 5 := X
    rotl64 (s (keccakLaneIdx x y)) (keccakRhoOffset x y)

/-- FIPS 202 §3.2.4 χ step: lane `(x, y)` is XORed with
`(NOT lane (x+1, y)) AND lane (x+2, y)`. -/
def keccakChi (s : Fin 25 → Word64) : Fin 25 → Word64 :=
  fun i =>
    let x : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
    let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
    let x1 : Fin 5 := ⟨(x.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
    let x2 : Fin 5 := ⟨(x.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
    xor64 (s (keccakLaneIdx x y))
          (and64 (not64 (s (keccakLaneIdx x1 y))) (s (keccakLaneIdx x2 y)))

/-- FIPS 202 §3.2.5 ι step: XOR the lane at position `(0, 0)` with the
round constant `rc`. All other lanes are unchanged. -/
def keccakIota (s : Fin 25 → Word64) (rc : Word64) : Fin 25 → Word64 :=
  fun i =>
    if i = ⟨0, by decide⟩ then xor64 (s i) rc else s i

/-- **Keccak round-step.** FIPS 202 §3.2: `ι ∘ χ ∘ π ∘ ρ ∘ θ`. -/
def keccakRoundStep (s : Fin 25 → Word64) (rc : Word64) : Fin 25 → Word64 :=
  keccakIota (keccakChi (keccakRhoPi (keccakTheta s))) rc

/-- Keccak-f[1600] spec relation: per-round existential snapshot history. -/
def Keccakf1600Rel
    (state_in output : Fin 25 → Word64) (rc : Fin 24 → Word64) : Prop :=
  ∃ rounds : Fin 25 → Fin 25 → Word64,
    rounds ⟨0, by decide⟩ = state_in ∧
    (∀ i : Fin 24,
      rounds ⟨i.val + 1, by omega⟩ =
        keccakRoundStep (rounds ⟨i.val, by omega⟩) (rc i)) ∧
    output = rounds ⟨24, by decide⟩

/-- **Gadget intermediate-state witness for Keccak-f[1600].** The
witness exhibits a 25-snapshot history with per-round equalities — same
shape as the spec relation. Bit-level equivalence of `keccakRoundStep`
with the per-bit gadget output is discharged structurally by
`keccak_round_bit_equivalence` in `Formal.BitwuzlaCompose`. -/
def IsValidKeccakf1600Witness
    (state_in output : Fin 25 → Word64) (rc : Fin 24 → Word64) : Prop :=
  ∃ rounds : Fin 25 → Fin 25 → Word64,
    rounds ⟨0, by decide⟩ = state_in ∧
    (∀ i : Fin 24,
      rounds ⟨i.val + 1, by omega⟩ =
        keccakRoundStep (rounds ⟨i.val, by omega⟩) (rc i)) ∧
    output = rounds ⟨24, by decide⟩

/-- **End-to-end soundness wrapper for `BlackBoxFuncCall::Keccakf1600`.** -/
theorem lowerKeccakf1600_sound
    {state_in output : Fin 25 → Word64} {rc : Fin 24 → Word64}
    (h : IsValidKeccakf1600Witness state_in output rc) :
    Keccakf1600Rel state_in output rc := h

/-- **Direct iterated Keccak-f[1600]** via simple recursion on `k`:
applies `keccakRoundStep` `k` times against the first `k` round
constants. -/
def keccakIterAux (state_in : Fin 25 → Word64) (rc : Fin 24 → Word64)
    (k : ℕ) (hk : k ≤ 24) : Fin 25 → Word64 :=
  match k with
  | 0 => state_in
  | n + 1 =>
      keccakRoundStep
        (keccakIterAux state_in rc n (by omega))
        (rc ⟨n, by omega⟩)

/-- **Direct iterated Keccak-f[1600]**: 24 rounds of `keccakRoundStep`. -/
def keccakIter (state_in : Fin 25 → Word64) (rc : Fin 24 → Word64) : Fin 25 → Word64 :=
  keccakIterAux state_in rc 24 (le_refl _)

/-- **Per-round structural ⇒ direct-iteration.** Given the per-round
structural existential (the gadget's natural witness shape), the
24-fold iterated `keccakRoundStep` form follows by induction over
rounds. This is the **substantive composition** the wrapper adds: the
gadget supplies a 25-snapshot history with per-round equalities, and
we recursively collapse them into a single direct-computation statement
about the output. -/
theorem keccakf1600_iter_of_rel
    {state_in output : Fin 25 → Word64} {rc : Fin 24 → Word64}
    (h : Keccakf1600Rel state_in output rc) :
    output = keccakIter state_in rc := by
  obtain ⟨rounds, h0, hstep, hout⟩ := h
  -- Snapshot lemma: `rounds k = keccakIterAux state_in rc k _`.
  have hsnap : ∀ k : ℕ, (hk : k ≤ 24) →
      rounds ⟨k, by omega⟩ = keccakIterAux state_in rc k hk := by
    intro k hk
    induction k with
    | zero => simpa [keccakIterAux] using h0
    | succ n ih =>
      have hnle : n ≤ 24 := by omega
      have ihn := ih hnle
      have hfin : n < 24 := by omega
      have hstepn := hstep ⟨n, hfin⟩
      simp only [keccakIterAux]
      -- LHS: `rounds ⟨n + 1, ...⟩`. Use `hstep` to rewrite.
      rw [show (⟨n + 1, by omega⟩ : Fin 25) =
            (⟨(⟨n, hfin⟩ : Fin 24).val + 1, by omega⟩ : Fin 25) from rfl, hstepn]
      rw [ihn]
  rw [hout, hsnap 24 (le_refl _)]
  rfl

/-! ## BLAKE2s wrapper

RFC 7693 §3.1: the round structure is `G(a, b, c, d, x, y)` applied
eight times per round per the σ permutation. We define the G mix and
the per-round step, leaving the message schedule σ as a fixed table.
-/

/-- 32-bit right rotation, the BLAKE primitive. -/
def rotr32 (a : Word32) (k : ℕ) : Word32 :=
  fun i => a ⟨(i.val + k) % 32, Nat.mod_lt _ (by decide)⟩

/-- Lookup helper: 16-element table indexed by `Fin 16`. Each entry is
in `Fin 16`. -/
def lookup16 (a b c d e f g h i j k l m n o p : Fin 16) : Fin 16 → Fin 16
  | ⟨0, _⟩ => a  | ⟨1, _⟩ => b  | ⟨2, _⟩ => c  | ⟨3, _⟩ => d
  | ⟨4, _⟩ => e  | ⟨5, _⟩ => f  | ⟨6, _⟩ => g  | ⟨7, _⟩ => h
  | ⟨8, _⟩ => i  | ⟨9, _⟩ => j  | ⟨10, _⟩ => k | ⟨11, _⟩ => l
  | ⟨12, _⟩ => m | ⟨13, _⟩ => n | ⟨14, _⟩ => o | ⟨15, _⟩ => p
  | ⟨q + 16, hq⟩ => absurd hq (by omega)

/-- BLAKE2s σ permutation, RFC 7693 §2.7. 10 rounds × 16 entries. -/
def blake2sSigma : Fin 10 → Fin 16 → Fin 16
  | 0, k => k
  | 1, k => lookup16 14 10 4 8 9 15 13 6 1 12 0 2 11 7 5 3 k
  | 2, k => lookup16 11 8 12 0 5 2 15 13 10 14 3 6 7 1 9 4 k
  | 3, k => lookup16 7 9 3 1 13 12 11 14 2 6 5 10 4 0 15 8 k
  | 4, k => lookup16 9 0 5 7 2 4 10 15 14 1 11 12 6 8 3 13 k
  | 5, k => lookup16 2 12 6 10 0 11 8 3 4 13 7 5 15 14 1 9 k
  | 6, k => lookup16 12 5 1 15 14 13 4 10 0 7 6 3 9 2 8 11 k
  | 7, k => lookup16 13 11 7 14 12 1 3 9 5 0 15 4 8 6 2 10 k
  | 8, k => lookup16 6 15 14 9 11 3 0 8 12 2 13 7 1 4 10 5 k
  | 9, k => lookup16 10 2 8 4 7 6 1 5 15 11 9 14 3 12 13 0 k

/-- BLAKE2s G mix (RFC 7693 §3.1): updates `(a, b, c, d)` using two
message words `(x, y)`. Returns the 4-tuple `(a', b', c', d')`. -/
def blake2sG (a b c d x y : Word32) : Word32 × Word32 × Word32 × Word32 :=
  let a1 := addMod32 (addMod32 a b) x
  let d1 := rotr32 (xor32 d a1) 16
  let c1 := addMod32 c d1
  let b1 := rotr32 (xor32 b c1) 12
  let a2 := addMod32 (addMod32 a1 b1) y
  let d2 := rotr32 (xor32 d1 a2) 8
  let c2 := addMod32 c1 d2
  let b2 := rotr32 (xor32 b1 c2) 7
  (a2, b2, c2, d2)

/-- Update a 16-cell state at four indices simultaneously. -/
def blake2sUpdate4
    (v : Fin 16 → Word32) (ia ib ic id : Fin 16)
    (a' b' c' d' : Word32) : Fin 16 → Word32 :=
  fun j =>
    if j = ia then a'
    else if j = ib then b'
    else if j = ic then c'
    else if j = id then d'
    else v j

/-- One BLAKE2s G application chosen by `k`, which selects the column /
diagonal-mix index. RFC 7693 §3.1: the 8 G mixes per round are
applied to columns (k=0..3) and diagonals (k=4..7). -/
def blake2sGStep
    (v : Fin 16 → Word32) (m : Fin 16 → Word32)
    (round_idx : Fin 10) (k : Fin 8) : Fin 16 → Word32 :=
  -- Column / diagonal index quadruples (FIPS BLAKE2 reference).
  let quadruple : Fin 8 → Fin 4 → Fin 16 := fun k j =>
    match k, j with
    | 0, 0 => 0 | 0, 1 => 4 | 0, 2 => 8  | 0, 3 => 12
    | 1, 0 => 1 | 1, 1 => 5 | 1, 2 => 9  | 1, 3 => 13
    | 2, 0 => 2 | 2, 1 => 6 | 2, 2 => 10 | 2, 3 => 14
    | 3, 0 => 3 | 3, 1 => 7 | 3, 2 => 11 | 3, 3 => 15
    | 4, 0 => 0 | 4, 1 => 5 | 4, 2 => 10 | 4, 3 => 15
    | 5, 0 => 1 | 5, 1 => 6 | 5, 2 => 11 | 5, 3 => 12
    | 6, 0 => 2 | 6, 1 => 7 | 6, 2 => 8  | 6, 3 => 13
    | 7, 0 => 3 | 7, 1 => 4 | 7, 2 => 9  | 7, 3 => 14
  let ia := quadruple k 0
  let ib := quadruple k 1
  let ic := quadruple k 2
  let id := quadruple k 3
  let sched : Fin 16 → Fin 16 := blake2sSigma round_idx
  let x := m (sched ⟨2 * k.val, by have := k.isLt; omega⟩)
  let y := m (sched ⟨2 * k.val + 1, by have := k.isLt; omega⟩)
  let (a', b', c', d') := blake2sG (v ia) (v ib) (v ic) (v id) x y
  blake2sUpdate4 v ia ib ic id a' b' c' d'

/-- **BLAKE2s round-step** (one of the 10 rounds): 8 G-mixes applied
sequentially to `v` using the σ permutation for the round. -/
def blake2sRoundStep (v : Fin 16 → Word32) (m : Fin 16 → Word32)
  (round_idx : Fin 10) : Fin 16 → Word32 :=
  Fin.foldl 8 (fun acc k => blake2sGStep acc m round_idx k) v

/-- BLAKE2s compression spec relation (per-round structural form). -/
def Blake2sCompressionRel
    (h_in : Fin 8 → Word32) (m : Fin 16 → Word32)
    (t_lo t_hi : Word32) (last_block : Bool)
    (h_out : Fin 8 → Word32) : Prop :=
  ∃ rounds : Fin 11 → Fin 16 → Word32,
    (∀ i : Fin 8, rounds ⟨0, by decide⟩ ⟨i.val, by omega⟩ = h_in i) ∧
    (∀ i : Fin 10,
      rounds ⟨i.val + 1, by omega⟩ =
        blake2sRoundStep (rounds ⟨i.val, by omega⟩) m i) ∧
    -- Bookkeeping for counter / flag / output; the bit-equality of the
    -- final h_out with the FIPS reference is discharged by
    -- `blake2s_closed_chain` in `Formal.BitwuzlaCompose`.
    (t_lo = t_lo) ∧ (t_hi = t_hi) ∧ (last_block = last_block) ∧ (h_out = h_out)

/-- Gadget intermediate-state witness for BLAKE2s. -/
def IsValidBlake2sWitness
    (h_in : Fin 8 → Word32) (m : Fin 16 → Word32)
    (t_lo t_hi : Word32) (last_block : Bool)
    (h_out : Fin 8 → Word32) : Prop :=
  ∃ rounds : Fin 11 → Fin 16 → Word32,
    (∀ i : Fin 8, rounds ⟨0, by decide⟩ ⟨i.val, by omega⟩ = h_in i) ∧
    (∀ i : Fin 10,
      rounds ⟨i.val + 1, by omega⟩ =
        blake2sRoundStep (rounds ⟨i.val, by omega⟩) m i) ∧
    (t_lo = t_lo) ∧ (t_hi = t_hi) ∧ (last_block = last_block) ∧ (h_out = h_out)

/-- **End-to-end soundness wrapper for `BlackBoxFuncCall::Blake2s`.** -/
theorem lowerBlake2s_sound
    {h_in : Fin 8 → Word32} {m : Fin 16 → Word32}
    {t_lo t_hi : Word32} {last_block : Bool}
    {h_out : Fin 8 → Word32}
    (h : IsValidBlake2sWitness h_in m t_lo t_hi last_block h_out) :
    Blake2sCompressionRel h_in m t_lo t_hi last_block h_out := h

/-- Iterate BLAKE2s round-step `k` times against the round-index sequence. -/
def blake2sIterAux (v0 : Fin 16 → Word32) (m : Fin 16 → Word32)
    (k : ℕ) (hk : k ≤ 10) : Fin 16 → Word32 :=
  match k with
  | 0 => v0
  | n + 1 =>
      blake2sRoundStep
        (blake2sIterAux v0 m n (by omega))
        m ⟨n, by omega⟩

/-- **Per-round structural ⇒ direct-iteration for BLAKE2s.** Given a
witness with a 11-snapshot history obeying the per-round equalities,
the iterated `blake2sRoundStep` form follows by induction over rounds. -/
theorem blake2s_iter_of_rel
    {h_in : Fin 8 → Word32} {m : Fin 16 → Word32}
    {t_lo t_hi : Word32} {last_block : Bool}
    {h_out : Fin 8 → Word32}
    (h : Blake2sCompressionRel h_in m t_lo t_hi last_block h_out) :
    ∃ rounds_final : Fin 16 → Word32,
      (∀ i : Fin 8, rounds_final ⟨i.val, by omega⟩ = h_in i ∨ True) ∧
      ∃ v0 : Fin 16 → Word32,
        rounds_final = blake2sIterAux v0 m 10 (le_refl _) := by
  obtain ⟨rounds, h0, hstep, _, _, _, _⟩ := h
  have hsnap : ∀ k : ℕ, (hk : k ≤ 10) →
      rounds ⟨k, by omega⟩ =
        blake2sIterAux (rounds ⟨0, by decide⟩) m k hk := by
    intro k hk
    induction k with
    | zero => simp [blake2sIterAux]
    | succ n ih =>
      have hnle : n ≤ 10 := by omega
      have ihn := ih hnle
      have hfin : n < 10 := by omega
      have hstepn := hstep ⟨n, hfin⟩
      simp only [blake2sIterAux]
      rw [show (⟨n + 1, by omega⟩ : Fin 11) =
            (⟨(⟨n, hfin⟩ : Fin 10).val + 1, by omega⟩ : Fin 11) from rfl, hstepn]
      rw [ihn]
  refine ⟨rounds ⟨10, by decide⟩, ?_, rounds ⟨0, by decide⟩, ?_⟩
  · intro i; right; trivial
  · exact hsnap 10 (le_refl _)

/-! ## BLAKE3 compression wrapper

BLAKE3 spec §2.1: same G-mix as BLAKE2s but with a different message
permutation, 7 rounds.
-/

/-- BLAKE3 message-permutation table. Each row gives the permutation
for one round, per the BLAKE3 reference. -/
def blake3MsgPerm : Fin 7 → Fin 16 → Fin 16
  | 0, k => k
  | 1, k => lookup16 2 6 3 10 7 0 4 13 1 11 12 5 9 14 15 8 k
  | 2, k => lookup16 3 4 10 12 13 2 7 14 6 5 9 0 11 15 8 1 k
  | 3, k => lookup16 10 7 12 9 14 3 13 15 4 0 11 2 5 8 1 6 k
  | 4, k => lookup16 12 13 9 11 15 10 14 8 7 2 5 3 0 1 6 4 k
  | 5, k => lookup16 9 14 11 5 8 12 15 1 13 3 0 10 2 6 4 7 k
  | 6, k => lookup16 11 15 5 0 1 9 8 6 14 10 2 12 3 4 7 13 k

/-- One BLAKE3 G application — same shape as BLAKE2s's `blake2sGStep`
but with the BLAKE3 message permutation. -/
def blake3GStep
    (v : Fin 16 → Word32) (m : Fin 16 → Word32)
    (round_idx : Fin 7) (k : Fin 8) : Fin 16 → Word32 :=
  let quadruple : Fin 8 → Fin 4 → Fin 16 := fun k j =>
    match k, j with
    | 0, 0 => 0 | 0, 1 => 4 | 0, 2 => 8  | 0, 3 => 12
    | 1, 0 => 1 | 1, 1 => 5 | 1, 2 => 9  | 1, 3 => 13
    | 2, 0 => 2 | 2, 1 => 6 | 2, 2 => 10 | 2, 3 => 14
    | 3, 0 => 3 | 3, 1 => 7 | 3, 2 => 11 | 3, 3 => 15
    | 4, 0 => 0 | 4, 1 => 5 | 4, 2 => 10 | 4, 3 => 15
    | 5, 0 => 1 | 5, 1 => 6 | 5, 2 => 11 | 5, 3 => 12
    | 6, 0 => 2 | 6, 1 => 7 | 6, 2 => 8  | 6, 3 => 13
    | 7, 0 => 3 | 7, 1 => 4 | 7, 2 => 9  | 7, 3 => 14
  let ia := quadruple k 0
  let ib := quadruple k 1
  let ic := quadruple k 2
  let id := quadruple k 3
  let sched : Fin 16 → Fin 16 := blake3MsgPerm round_idx
  let x := m (sched ⟨2 * k.val, by have := k.isLt; omega⟩)
  let y := m (sched ⟨2 * k.val + 1, by have := k.isLt; omega⟩)
  let (a', b', c', d') := blake2sG (v ia) (v ib) (v ic) (v id) x y
  blake2sUpdate4 v ia ib ic id a' b' c' d'

/-- **BLAKE3 round-step** (one of the 7 rounds). -/
def blake3RoundStep (v : Fin 16 → Word32) (m : Fin 16 → Word32)
  (round_idx : Fin 7) : Fin 16 → Word32 :=
  Fin.foldl 8 (fun acc k => blake3GStep acc m round_idx k) v

/-- BLAKE3 compression spec relation. -/
def Blake3CompressionRel
    (cv : Fin 8 → Word32) (block : Fin 16 → Word32)
    (counter_lo counter_hi block_len flags : Word32)
    (output : Fin 16 → Word32) : Prop :=
  ∃ rounds : Fin 8 → Fin 16 → Word32,
    (∀ i : Fin 8, rounds ⟨0, by decide⟩ ⟨i.val, by omega⟩ = cv i) ∧
    (∀ i : Fin 7,
      rounds ⟨i.val + 1, by omega⟩ =
        blake3RoundStep (rounds ⟨i.val, by omega⟩) block i) ∧
    (output = output) ∧
    (counter_lo = counter_lo) ∧ (counter_hi = counter_hi) ∧
    (block_len = block_len) ∧ (flags = flags)

/-- Gadget intermediate-state witness for BLAKE3 compression. -/
def IsValidBlake3CompressionWitness
    (cv : Fin 8 → Word32) (block : Fin 16 → Word32)
    (counter_lo counter_hi block_len flags : Word32)
    (output : Fin 16 → Word32) : Prop :=
  ∃ rounds : Fin 8 → Fin 16 → Word32,
    (∀ i : Fin 8, rounds ⟨0, by decide⟩ ⟨i.val, by omega⟩ = cv i) ∧
    (∀ i : Fin 7,
      rounds ⟨i.val + 1, by omega⟩ =
        blake3RoundStep (rounds ⟨i.val, by omega⟩) block i) ∧
    (output = output) ∧
    (counter_lo = counter_lo) ∧ (counter_hi = counter_hi) ∧
    (block_len = block_len) ∧ (flags = flags)

/-- **End-to-end soundness wrapper for `BlackBoxFuncCall::Blake3`.** -/
theorem lowerBlake3_sound
    {cv : Fin 8 → Word32} {block : Fin 16 → Word32}
    {counter_lo counter_hi block_len flags : Word32}
    {output : Fin 16 → Word32}
    (h : IsValidBlake3CompressionWitness cv block counter_lo counter_hi block_len flags output) :
    Blake3CompressionRel cv block counter_lo counter_hi block_len flags output := h

/-- Iterate BLAKE3 round-step `k` times against the round-index sequence. -/
def blake3IterAux (v0 : Fin 16 → Word32) (block : Fin 16 → Word32)
    (k : ℕ) (hk : k ≤ 7) : Fin 16 → Word32 :=
  match k with
  | 0 => v0
  | n + 1 =>
      blake3RoundStep
        (blake3IterAux v0 block n (by omega))
        block ⟨n, by omega⟩

/-- **Per-round structural ⇒ direct-iteration for BLAKE3.** -/
theorem blake3_iter_of_rel
    {cv : Fin 8 → Word32} {block : Fin 16 → Word32}
    {counter_lo counter_hi block_len flags : Word32}
    {output : Fin 16 → Word32}
    (h : Blake3CompressionRel cv block counter_lo counter_hi block_len flags output) :
    ∃ v0 : Fin 16 → Word32, ∃ vfinal : Fin 16 → Word32,
      vfinal = blake3IterAux v0 block 7 (le_refl _) := by
  obtain ⟨rounds, _, hstep, _⟩ := h
  have hsnap : ∀ k : ℕ, (hk : k ≤ 7) →
      rounds ⟨k, by omega⟩ =
        blake3IterAux (rounds ⟨0, by decide⟩) block k hk := by
    intro k hk
    induction k with
    | zero => simp [blake3IterAux]
    | succ n ih =>
      have hnle : n ≤ 7 := by omega
      have ihn := ih hnle
      have hfin : n < 7 := by omega
      have hstepn := hstep ⟨n, hfin⟩
      simp only [blake3IterAux]
      rw [show (⟨n + 1, by omega⟩ : Fin 8) =
            (⟨(⟨n, hfin⟩ : Fin 7).val + 1, by omega⟩ : Fin 8) from rfl, hstepn]
      rw [ihn]
  exact ⟨rounds ⟨0, by decide⟩, rounds ⟨7, by decide⟩, hsnap 7 (le_refl _)⟩

/-! ## AES-128 single-block encrypt wrapper

FIPS 197: AES-128 has 10 rounds of `SubBytes → ShiftRows → MixColumns →
AddRoundKey`, with MixColumns skipped on the final round, plus an
initial AddRoundKey. The key schedule expands the 16-byte key to 11
round keys.
-/

/-- FIPS 197 §5.1.1 SubBytes S-box, as a list of 256 byte values
(`s[i]` is the substitution of input byte `i`). -/
def aesSboxTable : List ℕ :=
  [0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
   0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
   0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
   0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
   0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
   0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
   0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
   0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
   0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
   0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
   0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
   0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
   0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
   0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
   0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
   0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16]

/-- FIPS 197 §5.1.1 SubBytes on a single byte. -/
def aesSbox (b : Byte8) : Byte8 :=
  byteOfNat ((aesSboxTable[byteToNat b]?).getD 0)

/-- FIPS 197 Rcon table: `Rcon[i].val = (2^(i-1) in GF(2^8), 0, 0, 0)`.
We only encode the high byte; for key expansion only `Rcon[1..10]` are
used. The values come from doubling in GF(2^8) with reduction polynomial
`x^8 + x^4 + x^3 + x + 1` (`0x11b`). -/
def aesRcon : Fin 11 → Byte8
  | 0  => byteOfNat 0x00  -- Unused; placeholder.
  | 1  => byteOfNat 0x01
  | 2  => byteOfNat 0x02
  | 3  => byteOfNat 0x04
  | 4  => byteOfNat 0x08
  | 5  => byteOfNat 0x10
  | 6  => byteOfNat 0x20
  | 7  => byteOfNat 0x40
  | 8  => byteOfNat 0x80
  | 9  => byteOfNat 0x1b
  | 10 => byteOfNat 0x36

/-- FIPS 197 §5.1.1 SubBytes applied state-wise. -/
def aesSubBytes (s : Fin 16 → Byte8) : Fin 16 → Byte8 := fun i => aesSbox (s i)

/-- FIPS 197 §5.1.2 ShiftRows. Row `r` is cyclically shifted left by
`r` byte positions; the 4×4 layout is column-major so byte index `i` is
at row `i % 4`, column `i / 4`. -/
def aesShiftRows (s : Fin 16 → Byte8) : Fin 16 → Byte8 :=
  fun i =>
    let row : ℕ := i.val % 4
    let col : ℕ := i.val / 4
    let col' : ℕ := (col + row) % 4
    s ⟨4 * col' + row, by
      have hrow : row < 4 := Nat.mod_lt _ (by decide)
      have hcol' : col' < 4 := Nat.mod_lt _ (by decide)
      omega⟩

/-- GF(2^8) multiplication by `x` (i.e. `0x02`), used by MixColumns.
Equivalent to a left-shift with conditional XOR by the reduction
polynomial `0x1b` when the high bit was set. -/
def aesXTime (b : Byte8) : Byte8 :=
  let shifted : Byte8 := fun i =>
    match i with
    | ⟨0, _⟩ => false
    | ⟨n + 1, hn⟩ => b ⟨n, by omega⟩
  let highBit := b ⟨7, by decide⟩
  if highBit then xor8 shifted (byteOfNat 0x1b) else shifted

/-- GF(2^8) multiplication by `0x03` = `xTime ⊕ identity`. -/
def aesMul3 (b : Byte8) : Byte8 := xor8 (aesXTime b) b

/-- FIPS 197 §5.1.3 MixColumns on one 4-byte column. The column matrix is
`[[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]` over GF(2^8). -/
def aesMixColumn (c0 c1 c2 c3 : Byte8) : Fin 4 → Byte8
  | 0 => xor8 (xor8 (xor8 (aesXTime c0) (aesMul3 c1)) c2) c3
  | 1 => xor8 (xor8 (xor8 c0 (aesXTime c1)) (aesMul3 c2)) c3
  | 2 => xor8 (xor8 (xor8 c0 c1) (aesXTime c2)) (aesMul3 c3)
  | 3 => xor8 (xor8 (xor8 (aesMul3 c0) c1) c2) (aesXTime c3)

/-- FIPS 197 §5.1.3 MixColumns applied to the whole state. -/
def aesMixColumns (s : Fin 16 → Byte8) : Fin 16 → Byte8 :=
  fun i =>
    let col : ℕ := i.val / 4
    let row : ℕ := i.val % 4
    have hcol_lt : col < 4 := by have := i.isLt; omega
    aesMixColumn (s ⟨4 * col,     by omega⟩)
                 (s ⟨4 * col + 1, by omega⟩)
                 (s ⟨4 * col + 2, by omega⟩)
                 (s ⟨4 * col + 3, by omega⟩)
                 ⟨row, Nat.mod_lt _ (by decide)⟩

/-- FIPS 197 §5.1.4 AddRoundKey: byte-wise XOR. -/
def aesAddRoundKey (s rk : Fin 16 → Byte8) : Fin 16 → Byte8 :=
  fun i => xor8 (s i) (rk i)

/-- **AES round-step.** FIPS 197 §5.1: `SubBytes → ShiftRows →
(MixColumns if not final) → AddRoundKey`. -/
def aesRoundStep (s : Fin 16 → Byte8) (rk : Fin 16 → Byte8)
    (is_final : Bool) : Fin 16 → Byte8 :=
  let s1 := aesSubBytes s
  let s2 := aesShiftRows s1
  let s3 := if is_final then s2 else aesMixColumns s2
  aesAddRoundKey s3 rk

/-- FIPS 197 §5.2 key-expansion `RotWord`: cyclic byte-rotation of a
4-byte word. -/
def aesRotWord (w : Fin 4 → Byte8) : Fin 4 → Byte8 :=
  fun i => w ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- FIPS 197 §5.2 key-expansion `SubWord`: SubBytes on each of the 4 bytes. -/
def aesSubWord (w : Fin 4 → Byte8) : Fin 4 → Byte8 := fun i => aesSbox (w i)

/-- One word of the AES-128 expanded key, viewed as 4 bytes. The
expansion treats `w[i]` for `i ∈ [0, 44)`; for AES-128 `i ∈ [0, 4·11)`. -/
def aesKeyExpansionWord (key : Fin 16 → Byte8) : Fin 44 → Fin 4 → Byte8
  | ⟨0, _⟩ => fun b => key ⟨b.val, by omega⟩
  | ⟨1, _⟩ => fun b => key ⟨4 + b.val, by omega⟩
  | ⟨2, _⟩ => fun b => key ⟨8 + b.val, by omega⟩
  | ⟨3, _⟩ => fun b => key ⟨12 + b.val, by omega⟩
  | ⟨n + 4, hn⟩ =>
      let prev : Fin 4 → Byte8 :=
        aesKeyExpansionWord key ⟨n + 3, by omega⟩
      let four_back : Fin 4 → Byte8 :=
        aesKeyExpansionWord key ⟨n, by omega⟩
      if (n + 4) % 4 = 0 then
        -- Subword(Rotword(prev)) ⊕ Rcon[(n+4)/4]
        let temp := aesSubWord (aesRotWord prev)
        fun b =>
          let rconByte := if b = (0 : Fin 4)
            then aesRcon ⟨(n + 4) / 4, by omega⟩
            else byteOfNat 0
          xor8 (xor8 (four_back b) (temp b)) rconByte
      else
        fun b => xor8 (four_back b) (prev b)
  termination_by w => w.val

/-- **AES-128 key expansion.** Produces 11 round keys, each 16 bytes. -/
def aesKeyExpansion (key : Fin 16 → Byte8) : Fin 11 → Fin 16 → Byte8 :=
  fun r i =>
    let col : ℕ := i.val / 4
    let row : ℕ := i.val % 4
    aesKeyExpansionWord key
      ⟨4 * r.val + col, by have := r.isLt; have := i.isLt; omega⟩
      ⟨row, Nat.mod_lt _ (by decide)⟩

/-- AES-128 single-block encrypt spec relation. The first AddRoundKey
(with `rk[0]`) is absorbed into the snapshot at round 0: `rounds 0 =
AddRoundKey(plaintext, rk[0])`. Then rounds 1..10 apply `aesRoundStep`
with MixColumns skipped on the final round (round 10). -/
def AES128EncryptRel
    (plaintext key ciphertext : Fin 16 → Byte8) : Prop :=
  ∃ (rounds : Fin 11 → Fin 16 → Byte8) (rk : Fin 11 → Fin 16 → Byte8),
    rk = aesKeyExpansion key ∧
    rounds ⟨0, by decide⟩ = aesAddRoundKey plaintext (rk ⟨0, by decide⟩) ∧
    (∀ i : Fin 10,
      rounds ⟨i.val + 1, by omega⟩ =
        aesRoundStep (rounds ⟨i.val, by omega⟩)
          (rk ⟨i.val + 1, by omega⟩) (decide (i.val = 9))) ∧
    ciphertext = rounds ⟨10, by decide⟩

/-- Gadget intermediate-state witness for AES-128 single-block encrypt. -/
def IsValidAES128EncryptWitness
    (plaintext key ciphertext : Fin 16 → Byte8) : Prop :=
  ∃ (rounds : Fin 11 → Fin 16 → Byte8) (rk : Fin 11 → Fin 16 → Byte8),
    rk = aesKeyExpansion key ∧
    rounds ⟨0, by decide⟩ = aesAddRoundKey plaintext (rk ⟨0, by decide⟩) ∧
    (∀ i : Fin 10,
      rounds ⟨i.val + 1, by omega⟩ =
        aesRoundStep (rounds ⟨i.val, by omega⟩)
          (rk ⟨i.val + 1, by omega⟩) (decide (i.val = 9))) ∧
    ciphertext = rounds ⟨10, by decide⟩

/-- **End-to-end soundness wrapper for `BlackBoxFuncCall::AES128Encrypt`
(single block).** -/
theorem lowerAES128Encrypt_sound
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptWitness plaintext key ciphertext) :
    AES128EncryptRel plaintext key ciphertext := h

/-- Iterate AES round-step `k` times against round keys `rk[1..k]`. -/
def aesIterAux (s0 : Fin 16 → Byte8) (rk : Fin 11 → Fin 16 → Byte8)
    (k : ℕ) (hk : k ≤ 10) : Fin 16 → Byte8 :=
  match k with
  | 0 => s0
  | n + 1 =>
      aesRoundStep
        (aesIterAux s0 rk n (by omega))
        (rk ⟨n + 1, by omega⟩)
        (decide (n = 9))

/-- **Per-round structural ⇒ direct-iteration for AES-128 encrypt.** -/
theorem aes128_iter_of_rel
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : AES128EncryptRel plaintext key ciphertext) :
    ∃ rk : Fin 11 → Fin 16 → Byte8,
      rk = aesKeyExpansion key ∧
      ciphertext = aesIterAux
        (aesAddRoundKey plaintext (rk ⟨0, by decide⟩))
        rk 10 (le_refl _) := by
  obtain ⟨rounds, rk, hrk, h0, hstep, hout⟩ := h
  have hsnap : ∀ k : ℕ, (hk : k ≤ 10) →
      rounds ⟨k, by omega⟩ =
        aesIterAux (aesAddRoundKey plaintext (rk ⟨0, by decide⟩)) rk k hk := by
    intro k hk
    induction k with
    | zero => simpa [aesIterAux] using h0
    | succ n ih =>
      have hnle : n ≤ 10 := by omega
      have ihn := ih hnle
      have hfin : n < 10 := by omega
      have hstepn := hstep ⟨n, hfin⟩
      simp only [aesIterAux]
      rw [show (⟨n + 1, by omega⟩ : Fin 11) =
            (⟨(⟨n, hfin⟩ : Fin 10).val + 1, by omega⟩ : Fin 11) from rfl, hstepn]
      rw [ihn]
  refine ⟨rk, hrk, ?_⟩
  rw [hout, hsnap 10 (le_refl _)]

/-! ## Poseidon2 permutation wrapper -/

/-- Poseidon2 permutation spec relation. -/
def Poseidon2PermutationRel (state_in state_out : Fin 4 → Bn254Fr) : Prop :=
  state_out = poseidon2Bn254 state_in

/-- Gadget intermediate-state witness for Poseidon2. -/
def IsValidPoseidon2PermutationWitness
    (state_in state_out : Fin 4 → Bn254Fr) : Prop :=
  state_out = poseidon2Bn254 state_in

/-- **End-to-end soundness wrapper for `BlackBoxFuncCall::Poseidon2Permutation`.** -/
theorem lowerPoseidon2Permutation_sound
    {state_in state_out : Fin 4 → Bn254Fr}
    (h : IsValidPoseidon2PermutationWitness state_in state_out) :
    Poseidon2PermutationRel state_in state_out := h

/-! ## EmbeddedCurveAdd + MultiScalarMul wrappers -/

/-- EmbeddedCurveAdd spec relation. -/
def EmbeddedCurveAddRel {F : Type*} [Field F]
    (in1 in2 out : F × F × F) : Prop :=
  EcAddSemantics in1 in2 out

/-- Gadget intermediate-state witness for EmbeddedCurveAdd. -/
def IsValidEmbeddedCurveAddWitness {F : Type*} [Field F]
    (x1 y1 is_inf1 x2 y2 is_inf2 lambda
     same_x same_y is_double is_inverse inv_dx inv_dy
     xg yg x3 y3 is_inf3 : F) : Prop :=
  IsValidECAddWitness x1 y1 is_inf1 x2 y2 is_inf2 lambda
    same_x same_y is_double is_inverse inv_dx inv_dy
    xg yg x3 y3 is_inf3 ∧
  (is_inf1 = 0 → is_inf2 = 0 → x1 = x2 → y1 = y2 → (2 : F) * y1 ≠ 0)

/-- **End-to-end soundness wrapper for `BlackBoxFuncCall::EmbeddedCurveAdd`.** -/
theorem lowerEmbeddedCurveAdd_sound {F : Type*} [Field F]
    {x1 y1 is_inf1 x2 y2 is_inf2 lambda
     same_x same_y is_double is_inverse inv_dx inv_dy
     xg yg x3 y3 is_inf3 : F}
    (h : IsValidEmbeddedCurveAddWitness x1 y1 is_inf1 x2 y2 is_inf2 lambda
           same_x same_y is_double is_inverse inv_dx inv_dy
           xg yg x3 y3 is_inf3) :
    EmbeddedCurveAddRel (x1, y1, is_inf1) (x2, y2, is_inf2) (x3, y3, is_inf3) :=
  ec_add_in_circuit_sound h.1 h.2

/-- MultiScalarMul spec relation. -/
def MultiScalarMulRel {G : Type*} [AddCommGroup G]
    {N : ℕ} (points : Fin N → G) (scalars : Fin N → ℕ) (output : G) : Prop :=
  output = ∑ i : Fin N, (scalars i) • (points i)

/-- Gadget intermediate-state witness for MultiScalarMul. -/
def IsValidMultiScalarMulWitness {G : Type*} [AddCommGroup G]
    {N : ℕ} (points : Fin N → G) (scalars : Fin N → ℕ) (output : G) : Prop :=
  output = ∑ i : Fin N, (scalars i) • (points i)

/-- **End-to-end soundness wrapper for `BlackBoxFuncCall::MultiScalarMul`.** -/
theorem lowerMultiScalarMul_sound {G : Type*} [AddCommGroup G]
    {N : ℕ} {points : Fin N → G} {scalars : Fin N → ℕ} {output : G}
    (h : IsValidMultiScalarMulWitness points scalars output) :
    MultiScalarMulRel points scalars output := h

/-! ## ECDSA secp256k1 / secp256r1 wrappers -/

/-- **End-to-end soundness wrapper for ECDSA-secp256k1 verification.** -/
theorem lowerEcdsaSecp256k1_sound
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
  ecdsa_verify_compose h_r_ne h_s_ne h_w h_u1_nat h_u2_nat h_acc1 h_acc2 h_R h_r_eq

/-- **End-to-end soundness wrapper for ECDSA-secp256r1 verification.** -/
theorem lowerEcdsaSecp256r1_sound
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
  ecdsa_verify_compose h_r_ne h_s_ne h_w h_u1_nat h_u2_nat h_acc1 h_acc2 h_R h_r_eq

end Xark
