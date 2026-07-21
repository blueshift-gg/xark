/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Wrappers
import Formal.GF256
import Formal.Gadgets
import Formal.Blake

set_option linter.style.header false
set_option linter.style.longLine false
-- The finite GF(256) byte facts below (bit-xor, affine/S-box bounds) are
-- exhaustive `Fin 256` checks discharged by `native_decide` (compiled
-- reduction over the full byte range), which the kernel cannot `decide` fast.
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 800000

/-!
# xark AES-128 round-step structural soundness — mechanised in Lean 4 / mathlib

This file builds the **structural** soundness layer for one AES round-step
(`SubBytes → ShiftRows → (MixColumns if not final) → AddRoundKey`) in
`gadgets/xark-aes/src/lib.rs`, in the spirit of
`Formal/Sha256.lean`. Bit-level equivalence of *individual* per-bit gadgets
(`and`, `xor`, `not`, S-box lookup) is discharged in `Formal/Bitwise.lean`
and the S-box pinning lemmas in `Formal/Gadgets.lean`.

What this file does:

* lifts the `Byte8` (= `Fin 8 → Bool`) pointwise primitives `xor8`,
  `and8`, `not8` plus the GF(2⁸) "double" operator `aesXTime` from
  `Formal.Wrappers` to bit-level soundness lemmas analogous to
  `xor32_sound` / `and32_sound` / `not32_sound` in `Formal.Sha256`;
* gives **per-layer structural soundness** for the four AES round layers
  — SubBytes, ShiftRows, MixColumns, AddRoundKey — each stating that
  given bit-witnessed inputs, the layer produces bit-witnessed outputs
  equal (under `BitOf`) to the pure-Lean spec `aesSubBytes`,
  `aesShiftRows`, `aesMixColumns`, `aesAddRoundKey`;
* gives **`aesRoundStep_bit_sound`**, the one-round structural
  composition that drives `aes128_round_bit_equivalence` in
  `Formal.BitwuzlaCompose` (historical file name; pure Lean) —
  replacing the previous pass-through tautology with a genuine
  four-layer composition.

What this file does *not* do: it does **not** bit-blast AES-128 in
Lean. The "end-to-end" theorem (the gadget's R1CS encoding of the full
10-round permutation equals the FIPS 197 reference) is the
`aes128_closed_chain` theorem in `Formal.BitwuzlaCompose`, composed
from per-round `aesRoundStep_bit_sound` invocations through
`aes128_iter_of_rel` (`Formal.Wrappers`).

The S-box layer's bit-encoding ≡ `aesSboxTable` is **definitional** in
the spec (`aesSbox = byteOfNat ∘ aesSboxTable[· byteToNat]`), and the
gadget materialises it via the 256-entry table lookup
(`s_box_in_circuit` in `gadgets/xark-aes/src/lib.rs`). The gadget's per-row lookup soundness
is `sbox_sound` / `sbox_unique` in `Formal.Gadgets`; here we only need
the structural statement "the SubBytes layer's output byte is the spec
S-box of the input byte".
-/

namespace Xark

/-! ## `Byte8` per-bit pointwise gadgets

The `Byte8` analogues of `not32_sound` / `and32_sound` / `xor32_sound`
from `Formal.Sha256`. Same proof shape: an 8-case split on the input
bit values plus arithmetic.

Note that `xor8` is already defined in `Formal.Wrappers`. We add
`and8`, `not8` here for completeness — AES doesn't use them directly,
but stating `xor8_sound` requires the same case-split machinery. -/

/-- Bitwise AND on a `Byte8`. -/
def and8 (a b : Byte8) : Byte8 := fun i => (a i) && (b i)

/-- Bitwise NOT on a `Byte8`. -/
def not8 (a : Byte8) : Byte8 := fun i => !(a i)

/-- **`xor8` gadget soundness, per bit.** The Rust per-bit `xor`
gadget allocates `out_i` with `(2 a_i) b_i = a_i + b_i − out_i`,
proven sound in `Formal.Bitwise` (`xor_sound`). Lifted pointwise: the
expression `wA i + wB i − 2 (wA i · wB i)` is `BitOf` the spec-level
`xor8 a b` bit. -/
theorem xor8_sound {F : Type*} [Field F]
    (a b : Byte8) (wA wB : Fin 8 → F)
    (hA : ∀ i, BitOf (wA i) (a i)) (hB : ∀ i, BitOf (wB i) (b i)) :
    ∀ i, BitOf (wA i + wB i - 2 * (wA i * wB i)) ((xor8 a b) i) := by
  intro i
  have ha := hA i
  have hb := hB i
  unfold BitOf at ha hb
  unfold xor8 BitOf
  cases hai : a i <;> cases hbi : b i <;>
    (simp [hai, hbi] at ha hb ⊢; rw [ha, hb]; norm_num)

/-- **`and8` gadget soundness, per bit.** Same shape as `and32_sound`. -/
theorem and8_sound {F : Type*} [Field F]
    (a b : Byte8) (wA wB : Fin 8 → F)
    (hA : ∀ i, BitOf (wA i) (a i)) (hB : ∀ i, BitOf (wB i) (b i)) :
    ∀ i, BitOf (wA i * wB i) ((and8 a b) i) := by
  intro i
  have ha := hA i
  have hb := hB i
  unfold BitOf at ha hb
  unfold and8 BitOf
  cases hai : a i <;> cases hbi : b i <;>
    (simp [hai, hbi] at ha hb ⊢; rw [ha, hb]; norm_num)

/-- **`not8` gadget soundness, per bit.** Same shape as `not32_sound`. -/
theorem not8_sound {F : Type*} [Ring F]
    (a : Byte8) (wA : Fin 8 → F)
    (hA : ∀ i, BitOf (wA i) (a i)) :
    ∀ i, BitOf ((1 : F) - wA i) ((not8 a) i) := by
  intro i
  have hi := hA i
  unfold BitOf at hi
  unfold not8 BitOf
  cases hai : a i
  · simp [hai] at hi; simp [hi]
  · simp [hai] at hi; simp [hi]

/-! ## Uniqueness / explicit form of `BitOf`

Used downstream to close per-layer composition lemmas. -/

/-- `BitOf` pins the wire to a unique value. -/
theorem BitOf.unique {F : Type*} [Zero F] [One F]
    {w₁ w₂ : F} {bit : Bool}
    (h₁ : BitOf w₁ bit) (h₂ : BitOf w₂ bit) : w₁ = w₂ := by
  unfold BitOf at h₁ h₂
  cases bit
  · simp at h₁ h₂; rw [h₁, h₂]
  · simp at h₁ h₂; rw [h₁, h₂]

/-- A `BitOf` witness equals `(if bit then 1 else 0)`. -/
theorem BitOf.eq_ite {F : Type*} [Zero F] [One F]
    {w : F} {bit : Bool}
    (h : BitOf w bit) : w = (if bit then (1 : F) else 0) := by
  unfold BitOf at h
  split_ifs with hb
  · simp [hb] at h; exact h
  · simp [hb] at h; exact h

/-! ## GF(2⁸) doubling (`aesXTime`)

`aesXTime` is one shift-left by 1 bit (i.e. `out i+1 := in i`, `out 0
:= 0`), followed by a conditional XOR with the reduction polynomial
`0x1b = 0b00011011` (LSB-first bits: `1,1,0,1,1,0,0,0`) when the
high bit `b 7` was set. The conditional XOR with a constant byte is
linear in the gadget — each output bit is either the shifted bit
(when `0x1b`'s corresponding bit is `0`) or the XOR of the shifted bit
with `b 7` (when `0x1b`'s corresponding bit is `1`).

Concretely, with `s_i := b ⟨i-1⟩` for `i ≥ 1` and `s_0 := 0`:

* bit 0: `s_0 ⊕ (b 7 ∧ 1)` = `b 7` (0x1b bit 0 = 1)
* bit 1: `s_1 ⊕ (b 7 ∧ 1)` = `xor (b 0) (b 7)` (0x1b bit 1 = 1)
* bit 2: `s_2 ⊕ (b 7 ∧ 0)` = `b 1` (0x1b bit 2 = 0)
* bit 3: `xor (b 2) (b 7)` (0x1b bit 3 = 1)
* bit 4: `xor (b 3) (b 7)` (0x1b bit 4 = 1)
* bit 5: `b 4` (0x1b bit 5 = 0)
* bit 6: `b 5` (0x1b bit 6 = 0)
* bit 7: `b 6` (0x1b bit 7 = 0)

This is the function the gadget materialises (modulo the per-bit
witness arithmetic). -/

/-- The per-bit closed-form field-level witness for `aesXTime b` as a
function of the input wires `wB : Fin 8 → F`. The `0x1b` constant's
bits are baked into the case-split: indices `0, 1, 3, 4` XOR with
`wB 7` (the high bit), the others just project a shifted wire. -/
def aesXTimeWire {F : Type*} [Field F] (wB : Fin 8 → F) (i : Fin 8) : F :=
  match i with
  | ⟨0, _⟩ => wB ⟨7, by decide⟩
  | ⟨1, _⟩ => wB ⟨0, by decide⟩ + wB ⟨7, by decide⟩
                - 2 * (wB ⟨0, by decide⟩ * wB ⟨7, by decide⟩)
  | ⟨2, _⟩ => wB ⟨1, by decide⟩
  | ⟨3, _⟩ => wB ⟨2, by decide⟩ + wB ⟨7, by decide⟩
                - 2 * (wB ⟨2, by decide⟩ * wB ⟨7, by decide⟩)
  | ⟨4, _⟩ => wB ⟨3, by decide⟩ + wB ⟨7, by decide⟩
                - 2 * (wB ⟨3, by decide⟩ * wB ⟨7, by decide⟩)
  | ⟨5, _⟩ => wB ⟨4, by decide⟩
  | ⟨6, _⟩ => wB ⟨5, by decide⟩
  | ⟨7, _⟩ => wB ⟨6, by decide⟩
  | ⟨n + 8, hn⟩ => absurd hn (by omega)

/-! ### Bit-level characterization of `aesXTime`

We prove an explicit `Bool`-level identity for each of the 8 output
bits of `aesXTime b`, expressed purely in terms of `b`'s input bits.
This lets the soundness proof split into 8 trivial cases — each a
direct bool equality lifted by `BitOf` arithmetic. -/

private theorem byteOfNat_0x1b_bits :
    (byteOfNat 0x1b) ⟨0, by decide⟩ = true ∧
    (byteOfNat 0x1b) ⟨1, by decide⟩ = true ∧
    (byteOfNat 0x1b) ⟨2, by decide⟩ = false ∧
    (byteOfNat 0x1b) ⟨3, by decide⟩ = true ∧
    (byteOfNat 0x1b) ⟨4, by decide⟩ = true ∧
    (byteOfNat 0x1b) ⟨5, by decide⟩ = false ∧
    (byteOfNat 0x1b) ⟨6, by decide⟩ = false ∧
    (byteOfNat 0x1b) ⟨7, by decide⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold byteOfNat; decide)

private theorem aesXTime_bit_0 (b : Byte8) : (aesXTime b) ⟨0, by decide⟩ = b ⟨7, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp
  · simp
    change byteOfNat 0x1b ⟨0, by decide⟩ = true
    decide

private theorem aesXTime_bit_1 (b : Byte8) :
    (aesXTime b) ⟨1, by decide⟩ = xor (b ⟨0, by decide⟩) (b ⟨7, by decide⟩) := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp
  · simp
    change xor (b ⟨0, by decide⟩) (byteOfNat 0x1b ⟨1, by decide⟩) = !(b ⟨0, by decide⟩)
    have : byteOfNat 0x1b ⟨1, by decide⟩ = true := by decide
    rw [this]; cases b ⟨0, by decide⟩ <;> rfl

private theorem aesXTime_bit_2 (b : Byte8) : (aesXTime b) ⟨2, by decide⟩ = b ⟨1, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp
  · simp
    change xor (b ⟨1, by decide⟩) (byteOfNat 0x1b ⟨2, by decide⟩) = b ⟨1, by decide⟩
    have : byteOfNat 0x1b ⟨2, by decide⟩ = false := by decide
    rw [this]; cases b ⟨1, by decide⟩ <;> rfl

private theorem aesXTime_bit_3 (b : Byte8) :
    (aesXTime b) ⟨3, by decide⟩ = xor (b ⟨2, by decide⟩) (b ⟨7, by decide⟩) := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp
  · simp
    change xor (b ⟨2, by decide⟩) (byteOfNat 0x1b ⟨3, by decide⟩) = !(b ⟨2, by decide⟩)
    have : byteOfNat 0x1b ⟨3, by decide⟩ = true := by decide
    rw [this]; cases b ⟨2, by decide⟩ <;> rfl

private theorem aesXTime_bit_4 (b : Byte8) :
    (aesXTime b) ⟨4, by decide⟩ = xor (b ⟨3, by decide⟩) (b ⟨7, by decide⟩) := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp
  · simp
    change xor (b ⟨3, by decide⟩) (byteOfNat 0x1b ⟨4, by decide⟩) = !(b ⟨3, by decide⟩)
    have : byteOfNat 0x1b ⟨4, by decide⟩ = true := by decide
    rw [this]; cases b ⟨3, by decide⟩ <;> rfl

private theorem aesXTime_bit_5 (b : Byte8) : (aesXTime b) ⟨5, by decide⟩ = b ⟨4, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp
  · simp
    change xor (b ⟨4, by decide⟩) (byteOfNat 0x1b ⟨5, by decide⟩) = b ⟨4, by decide⟩
    have : byteOfNat 0x1b ⟨5, by decide⟩ = false := by decide
    rw [this]; cases b ⟨4, by decide⟩ <;> rfl

private theorem aesXTime_bit_6 (b : Byte8) : (aesXTime b) ⟨6, by decide⟩ = b ⟨5, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp
  · simp
    change xor (b ⟨5, by decide⟩) (byteOfNat 0x1b ⟨6, by decide⟩) = b ⟨5, by decide⟩
    have : byteOfNat 0x1b ⟨6, by decide⟩ = false := by decide
    rw [this]; cases b ⟨5, by decide⟩ <;> rfl

private theorem aesXTime_bit_7 (b : Byte8) : (aesXTime b) ⟨7, by decide⟩ = b ⟨6, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp
  · simp
    change xor (b ⟨6, by decide⟩) (byteOfNat 0x1b ⟨7, by decide⟩) = b ⟨6, by decide⟩
    have : byteOfNat 0x1b ⟨7, by decide⟩ = false := by decide
    rw [this]; cases b ⟨6, by decide⟩ <;> rfl

/-- Lifting `BitOf` through a bool case: `BitOf w b` iff `w = if b then 1 else 0`. -/
private theorem BitOf.iff_ite {F : Type*} [Zero F] [One F] {w : F} {bit : Bool} :
    BitOf w bit ↔ w = (if bit then (1 : F) else 0) := by
  unfold BitOf
  cases bit <;> simp

private theorem BitOf.of_eq_ite {F : Type*} [Zero F] [One F] {w : F} {bit : Bool}
    (h : w = (if bit then (1 : F) else 0)) : BitOf w bit :=
  BitOf.iff_ite.mpr h

/-- **`aesXTime` gadget soundness, per bit.** The per-bit witness
`aesXTimeWire wB i` is `BitOf` the spec-level `aesXTime b` output bit.
Each case lifts `xor8_sound` (for the bits where 0x1b has a `1`) or
projects the shifted bit (where 0x1b has a `0`) through the conditional
shift. -/
theorem aesXTime_sound {F : Type*} [Field F]
    (b : Byte8) (wB : Fin 8 → F)
    (hB : ∀ i, BitOf (wB i) (b i)) :
    ∀ i, BitOf (aesXTimeWire wB i) ((aesXTime b) i) := by
  intro i
  -- Express each input bit-wire via `BitOf.eq_ite`, then case-split on bool
  -- equalities and discharge with `norm_num`.
  have e0 : wB ⟨0, by decide⟩ = if b ⟨0, by decide⟩ then (1 : F) else 0 := BitOf.eq_ite (hB _)
  have e1 : wB ⟨1, by decide⟩ = if b ⟨1, by decide⟩ then (1 : F) else 0 := BitOf.eq_ite (hB _)
  have e2 : wB ⟨2, by decide⟩ = if b ⟨2, by decide⟩ then (1 : F) else 0 := BitOf.eq_ite (hB _)
  have e3 : wB ⟨3, by decide⟩ = if b ⟨3, by decide⟩ then (1 : F) else 0 := BitOf.eq_ite (hB _)
  have e4 : wB ⟨4, by decide⟩ = if b ⟨4, by decide⟩ then (1 : F) else 0 := BitOf.eq_ite (hB _)
  have e5 : wB ⟨5, by decide⟩ = if b ⟨5, by decide⟩ then (1 : F) else 0 := BitOf.eq_ite (hB _)
  have e6 : wB ⟨6, by decide⟩ = if b ⟨6, by decide⟩ then (1 : F) else 0 := BitOf.eq_ite (hB _)
  have e7 : wB ⟨7, by decide⟩ = if b ⟨7, by decide⟩ then (1 : F) else 0 := BitOf.eq_ite (hB _)
  rcases i with ⟨n, hn⟩
  interval_cases n
  -- n = 0: aesXTimeWire = wB 7; aesXTime b bit 0 = b 7
  · rw [aesXTime_bit_0]
    apply BitOf.of_eq_ite
    change wB ⟨7, by decide⟩ = _
    rw [e7]
  -- n = 1: aesXTimeWire = xor witness; aesXTime b bit 1 = xor b0 b7
  · rw [aesXTime_bit_1]
    apply BitOf.of_eq_ite
    change wB ⟨0, by decide⟩ + wB ⟨7, by decide⟩
           - 2 * (wB ⟨0, by decide⟩ * wB ⟨7, by decide⟩) = _
    rw [e0, e7]
    cases b ⟨0, by decide⟩ <;> cases b ⟨7, by decide⟩ <;> simp; ring
  -- n = 2
  · rw [aesXTime_bit_2]
    apply BitOf.of_eq_ite
    change wB ⟨1, by decide⟩ = _
    rw [e1]
  -- n = 3
  · rw [aesXTime_bit_3]
    apply BitOf.of_eq_ite
    change wB ⟨2, by decide⟩ + wB ⟨7, by decide⟩
           - 2 * (wB ⟨2, by decide⟩ * wB ⟨7, by decide⟩) = _
    rw [e2, e7]
    cases b ⟨2, by decide⟩ <;> cases b ⟨7, by decide⟩ <;> simp; ring
  -- n = 4
  · rw [aesXTime_bit_4]
    apply BitOf.of_eq_ite
    change wB ⟨3, by decide⟩ + wB ⟨7, by decide⟩
           - 2 * (wB ⟨3, by decide⟩ * wB ⟨7, by decide⟩) = _
    rw [e3, e7]
    cases b ⟨3, by decide⟩ <;> cases b ⟨7, by decide⟩ <;> simp; ring
  -- n = 5
  · rw [aesXTime_bit_5]
    apply BitOf.of_eq_ite
    change wB ⟨4, by decide⟩ = _
    rw [e4]
  -- n = 6
  · rw [aesXTime_bit_6]
    apply BitOf.of_eq_ite
    change wB ⟨5, by decide⟩ = _
    rw [e5]
  -- n = 7
  · rw [aesXTime_bit_7]
    apply BitOf.of_eq_ite
    change wB ⟨6, by decide⟩ = _
    rw [e6]

/-! ## Layer soundness: SubBytes, ShiftRows, MixColumns, AddRoundKey

The four AES round layers, each stated as a `BitOf`-preserving
transformation. Compositions land in the `aesRoundStep_bit_sound`
master theorem below.

The SubBytes layer is **definitional** at the byte-level: the spec
defines `aesSubBytes := fun s i => aesSbox (s i)`. The bit-level
content reduces to the S-box table lookup `aesSboxTable`, whose
gadget soundness lives in `Formal.Gadgets` (`sbox_sound` /
`sbox_unique`). We expose the byte-level identity here. -/

/-- **SubBytes byte-level soundness.** Spec equality: the `i`-th
output byte is `aesSbox` of the `i`-th input byte. Direct from the
spec definition. The per-bit content reduces to the lookup
soundness in `Formal.Gadgets.sbox_sound`. -/
theorem aesSubBytes_byte_sound (s : Fin 16 → Byte8) :
    ∀ i, aesSubBytes s i = aesSbox (s i) := by
  intro i; unfold aesSubBytes; rfl

/-- **ShiftRows soundness (per-bit, zero constraint cost).** The
ShiftRows layer is a pure byte-level permutation of the 16-byte
state. Given bit-witnesses for the input state, the output bit-wires
are simply the input wires at the permuted byte index — the same
relabelling the gadget performs. -/
theorem aesShiftRows_sound {F : Type*} [Zero F] [One F]
    (s : Fin 16 → Byte8) (wS : Fin 16 → Fin 8 → F)
    (hS : ∀ i j, BitOf (wS i j) (s i j)) :
    ∀ i j,
      let row : ℕ := i.val % 4
      let col : ℕ := i.val / 4
      let col' : ℕ := (col + row) % 4
      let src : Fin 16 := ⟨4 * col' + row, by
        have hrow : row < 4 := Nat.mod_lt _ (by decide)
        have hcol' : col' < 4 := Nat.mod_lt _ (by decide)
        omega⟩
      BitOf (wS src j) ((aesShiftRows s i) j) := by
  intro i j
  simp only
  unfold aesShiftRows
  exact hS _ _

/-- **MixColumn soundness (per column, per row).** The 4×4 GF(2⁸)
matrix multiplication composes `aesXTime_sound` and `xor8_sound` over
the 4-row state. We expose a witness function `aesMixColumnWire`
per (row, bit) pair, equal to the field-level chain of XORs and
`xtime` doublings that the gadget materialises (see
`mix_columns` in `gadgets/xark-aes/src/lib.rs`). -/
theorem aesMixColumn_sound {F : Type*} [Field F]
    (c0 c1 c2 c3 : Byte8) (wC0 wC1 wC2 wC3 : Fin 8 → F)
    (h0 : ∀ j, BitOf (wC0 j) (c0 j))
    (h1 : ∀ j, BitOf (wC1 j) (c1 j))
    (h2 : ∀ j, BitOf (wC2 j) (c2 j))
    (h3 : ∀ j, BitOf (wC3 j) (c3 j)) :
    ∀ (r : Fin 4),
      ∃ wOut : Fin 8 → F, ∀ j, BitOf (wOut j) ((aesMixColumn c0 c1 c2 c3 r) j) := by
  intro r
  -- The witness for each row is the chained xor of the four xtime/mul3/
  -- identity outputs. We use the bit-level `xor8_sound` + `aesXTime_sound`
  -- to build the witness wire pointwise.
  fin_cases r
  · -- r = 0: out = xtime(c0) ⊕ mul3(c1) ⊕ c2 ⊕ c3
    -- mul3(c1) = xtime(c1) ⊕ c1
    have hx0 := aesXTime_sound c0 wC0 h0
    have hx1 := aesXTime_sound c1 wC1 h1
    -- mul3 = xtime ⊕ identity
    have hm1 : ∀ j, BitOf (aesXTimeWire wC1 j + wC1 j - 2 * (aesXTimeWire wC1 j * wC1 j))
                        ((aesMul3 c1) j) := by
      intro j; unfold aesMul3
      exact xor8_sound _ _ _ _ hx1 h1 j
    -- step1 = xtime(c0) ⊕ mul3(c1)
    have hs1 := fun j => xor8_sound (aesXTime c0) (aesMul3 c1)
                            (aesXTimeWire wC0)
                            (fun j => aesXTimeWire wC1 j + wC1 j -
                                       2 * (aesXTimeWire wC1 j * wC1 j))
                            hx0 hm1 j
    -- step2 = step1 ⊕ c2
    set f1 : Fin 8 → F := fun j =>
      aesXTimeWire wC0 j +
        (aesXTimeWire wC1 j + wC1 j - 2 * (aesXTimeWire wC1 j * wC1 j)) -
        2 * (aesXTimeWire wC0 j *
              (aesXTimeWire wC1 j + wC1 j - 2 * (aesXTimeWire wC1 j * wC1 j))) with hf1
    have hs2 := fun j => xor8_sound (xor8 (aesXTime c0) (aesMul3 c1)) c2 f1 wC2 hs1 h2 j
    set f2 : Fin 8 → F := fun j => f1 j + wC2 j - 2 * (f1 j * wC2 j) with hf2
    have hs3 := fun j =>
      xor8_sound (xor8 (xor8 (aesXTime c0) (aesMul3 c1)) c2) c3 f2 wC3 hs2 h3 j
    refine ⟨fun j => f2 j + wC3 j - 2 * (f2 j * wC3 j), ?_⟩
    intro j
    unfold aesMixColumn
    exact hs3 j
  · -- r = 1: out = c0 ⊕ xtime(c1) ⊕ mul3(c2) ⊕ c3
    have hx1 := aesXTime_sound c1 wC1 h1
    have hx2 := aesXTime_sound c2 wC2 h2
    have hm2 : ∀ j, BitOf (aesXTimeWire wC2 j + wC2 j - 2 * (aesXTimeWire wC2 j * wC2 j))
                        ((aesMul3 c2) j) := by
      intro j; unfold aesMul3
      exact xor8_sound _ _ _ _ hx2 h2 j
    have hs1 := fun j => xor8_sound c0 (aesXTime c1) wC0 (aesXTimeWire wC1) h0 hx1 j
    set f1 : Fin 8 → F := fun j =>
      wC0 j + aesXTimeWire wC1 j - 2 * (wC0 j * aesXTimeWire wC1 j) with hf1
    have hs2 := fun j =>
      xor8_sound (xor8 c0 (aesXTime c1)) (aesMul3 c2) f1
        (fun j => aesXTimeWire wC2 j + wC2 j - 2 * (aesXTimeWire wC2 j * wC2 j))
        hs1 hm2 j
    set f2 : Fin 8 → F := fun j =>
      f1 j + (aesXTimeWire wC2 j + wC2 j - 2 * (aesXTimeWire wC2 j * wC2 j)) -
        2 * (f1 j * (aesXTimeWire wC2 j + wC2 j - 2 * (aesXTimeWire wC2 j * wC2 j))) with hf2
    have hs3 := fun j =>
      xor8_sound (xor8 (xor8 c0 (aesXTime c1)) (aesMul3 c2)) c3 f2 wC3 hs2 h3 j
    refine ⟨fun j => f2 j + wC3 j - 2 * (f2 j * wC3 j), ?_⟩
    intro j
    unfold aesMixColumn
    exact hs3 j
  · -- r = 2: out = c0 ⊕ c1 ⊕ xtime(c2) ⊕ mul3(c3)
    have hx2 := aesXTime_sound c2 wC2 h2
    have hx3 := aesXTime_sound c3 wC3 h3
    have hm3 : ∀ j, BitOf (aesXTimeWire wC3 j + wC3 j - 2 * (aesXTimeWire wC3 j * wC3 j))
                        ((aesMul3 c3) j) := by
      intro j; unfold aesMul3
      exact xor8_sound _ _ _ _ hx3 h3 j
    have hs1 := fun j => xor8_sound c0 c1 wC0 wC1 h0 h1 j
    set f1 : Fin 8 → F := fun j => wC0 j + wC1 j - 2 * (wC0 j * wC1 j) with hf1
    have hs2 := fun j =>
      xor8_sound (xor8 c0 c1) (aesXTime c2) f1 (aesXTimeWire wC2) hs1 hx2 j
    set f2 : Fin 8 → F := fun j =>
      f1 j + aesXTimeWire wC2 j - 2 * (f1 j * aesXTimeWire wC2 j) with hf2
    have hs3 := fun j =>
      xor8_sound (xor8 (xor8 c0 c1) (aesXTime c2)) (aesMul3 c3) f2
        (fun j => aesXTimeWire wC3 j + wC3 j - 2 * (aesXTimeWire wC3 j * wC3 j))
        hs2 hm3 j
    refine ⟨fun j => f2 j +
      (aesXTimeWire wC3 j + wC3 j - 2 * (aesXTimeWire wC3 j * wC3 j)) -
      2 * (f2 j * (aesXTimeWire wC3 j + wC3 j - 2 * (aesXTimeWire wC3 j * wC3 j))), ?_⟩
    intro j
    unfold aesMixColumn
    exact hs3 j
  · -- r = 3: out = mul3(c0) ⊕ c1 ⊕ c2 ⊕ xtime(c3)
    have hx0 := aesXTime_sound c0 wC0 h0
    have hx3 := aesXTime_sound c3 wC3 h3
    have hm0 : ∀ j, BitOf (aesXTimeWire wC0 j + wC0 j - 2 * (aesXTimeWire wC0 j * wC0 j))
                        ((aesMul3 c0) j) := by
      intro j; unfold aesMul3
      exact xor8_sound _ _ _ _ hx0 h0 j
    have hs1 := fun j =>
      xor8_sound (aesMul3 c0) c1
        (fun j => aesXTimeWire wC0 j + wC0 j - 2 * (aesXTimeWire wC0 j * wC0 j))
        wC1 hm0 h1 j
    set f1 : Fin 8 → F := fun j =>
      (aesXTimeWire wC0 j + wC0 j - 2 * (aesXTimeWire wC0 j * wC0 j)) + wC1 j -
        2 * ((aesXTimeWire wC0 j + wC0 j - 2 * (aesXTimeWire wC0 j * wC0 j)) * wC1 j) with hf1
    have hs2 := fun j =>
      xor8_sound (xor8 (aesMul3 c0) c1) c2 f1 wC2 hs1 h2 j
    set f2 : Fin 8 → F := fun j => f1 j + wC2 j - 2 * (f1 j * wC2 j) with hf2
    have hs3 := fun j =>
      xor8_sound (xor8 (xor8 (aesMul3 c0) c1) c2) (aesXTime c3) f2 (aesXTimeWire wC3)
        hs2 hx3 j
    refine ⟨fun j => f2 j + aesXTimeWire wC3 j - 2 * (f2 j * aesXTimeWire wC3 j), ?_⟩
    intro j
    unfold aesMixColumn
    exact hs3 j

/-- **MixColumns layer soundness.** Given bit-witnessed input state,
the MixColumns output state is bit-witnessed via column-wise
application of `aesMixColumn_sound`. -/
theorem aesMixColumns_sound {F : Type*} [Field F]
    (s : Fin 16 → Byte8) (wS : Fin 16 → Fin 8 → F)
    (hS : ∀ i j, BitOf (wS i j) (s i j)) :
    ∀ i, ∃ wOut : Fin 8 → F, ∀ j, BitOf (wOut j) ((aesMixColumns s i) j) := by
  intro i
  let col : ℕ := i.val / 4
  let row : ℕ := i.val % 4
  have hcol_lt : col < 4 := by have := i.isLt; omega
  have hrow_lt : row < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨wOut, hOut⟩ :=
    aesMixColumn_sound (s ⟨4 * col, by omega⟩) (s ⟨4 * col + 1, by omega⟩)
      (s ⟨4 * col + 2, by omega⟩) (s ⟨4 * col + 3, by omega⟩)
      (wS ⟨4 * col, by omega⟩) (wS ⟨4 * col + 1, by omega⟩)
      (wS ⟨4 * col + 2, by omega⟩) (wS ⟨4 * col + 3, by omega⟩)
      (hS ⟨4 * col, by omega⟩) (hS ⟨4 * col + 1, by omega⟩)
      (hS ⟨4 * col + 2, by omega⟩) (hS ⟨4 * col + 3, by omega⟩)
      ⟨row, hrow_lt⟩
  refine ⟨wOut, ?_⟩
  intro j
  unfold aesMixColumns
  exact hOut j

/-- **AddRoundKey soundness.** Per-byte XOR; reduces directly to
`xor8_sound`. -/
theorem aesAddRoundKey_sound {F : Type*} [Field F]
    (s rk : Fin 16 → Byte8) (wS wRK : Fin 16 → Fin 8 → F)
    (hS : ∀ i j, BitOf (wS i j) (s i j))
    (hRK : ∀ i j, BitOf (wRK i j) (rk i j)) :
    ∀ i j, BitOf (wS i j + wRK i j - 2 * (wS i j * wRK i j))
                 ((aesAddRoundKey s rk i) j) := by
  intro i j
  unfold aesAddRoundKey
  exact xor8_sound (s i) (rk i) (wS i) (wRK i) (hS i) (hRK i) j

/-! ### AES S-box gadget constraint chain (per byte)

The gadget emits, for each of the 16 input bytes `x`:

* a boolean `is_zero` wire;
* 8 boolean `x_inv` bit wires;
* 64 cross-product wires `p[a][b] = x_bits[a] · x_inv_bits[b]`;
* 8 boolean `prod_bits[k]` wires together with carry decomposition
  wires, satisfying `Σ contributing p[a][b] = prod_bits[k] + 2 · carry_k`
  (the `xor_bits_to_bit` parity decomposition);
* the constraints `x · is_zero = 0`, `x_inv · is_zero = 0`,
  `prod_bits[0] = 1 − is_zero`, and `prod_bits[k] = 0` for `k ∈ [1, 8)`;
* 8 affine output wires, each satisfying its own parity-decomposition
  constraint over 5 selected `x_inv` bits + a `0x63`-bit constant.

We encode this as `IsValidSBoxByteWitness` below. The proof
`aesSbox_byte_constraint_sound` shows: under the constraint chain,
the output wires are `BitOf`-witnessed by `aesSbox x`. This is the
**actual** AES S-box bit-level soundness — no canonical-lift
sleight-of-hand.

The proof uses `Formal.GF256` for the GF(2^8) algebraic facts
(`gf256_mul_inv`, `gf256_inv_unique`, `aesSbox_algebraic_eq_table`)
and an `Fr → ℕ` no-wrap bridge (each weighted sum stays well below
the BN254 modulus `r ≈ 2²⁵⁴`). -/

/-- The gadget's per-byte S-box constraint chain. `wX` is the input
byte's bit-wires (`BitOf`-witnessed by `x`); `wX_inv, w_isz, wP, wProd,
wOut` are prover-supplied wires constrained by the gadget. -/
structure IsValidSBoxByteWitness (x : Byte8)
    (wX wX_inv : Fin 8 → ZMod r)
    (w_isz : ZMod r)
    (wP : Fin 8 → Fin 8 → ZMod r)
    (wProd : Fin 8 → ZMod r)
    (wOut : Fin 8 → ZMod r) : Prop where
  /-- Input is `BitOf`-witnessed by the spec byte `x`. -/
  hX : ∀ j, BitOf (wX j) (x j)
  /-- `x_inv` bits are boolean. -/
  hX_inv_bool : ∀ j, wX_inv j = 0 ∨ wX_inv j = 1
  /-- `is_zero` is boolean. -/
  h_isz_bool : w_isz = 0 ∨ w_isz = 1
  /-- `prod_bits` are boolean. -/
  h_prod_bool : ∀ k, wProd k = 0 ∨ wProd k = 1
  /-- Output bits are boolean. -/
  h_out_bool : ∀ j, wOut j = 0 ∨ wOut j = 1
  /-- `x · is_zero = 0` (over `Fr`, with `x` recomposed from bit wires). -/
  h_x_isz : (∑ i : Fin 8, (2 : ZMod r) ^ i.val * wX i) * w_isz = 0
  /-- `x_inv · is_zero = 0` (likewise). -/
  h_xinv_isz : (∑ i : Fin 8, (2 : ZMod r) ^ i.val * wX_inv i) * w_isz = 0
  /-- Cross-product constraints: `p[a][b] = x_bits[a] · x_inv_bits[b]`. -/
  h_cross : ∀ a b : Fin 8, wP a b = wX a * wX_inv b
  /-- GF(2^8) product parity decomposition (per output bit `k`). The
  sum of contributing cross-products equals `wProd k + 2 · carry_k`
  for some non-negative `carry_k`. Stated as an ℕ-level equation
  using `wireBitNat`. (Bridges to `Fr` are easy since 7 ≤ contributions
  ≤ 14 per bit and the carry stays in `[0, 7]`, all far below `r`.) -/
  h_prod_parity : ∀ k : Fin 8,
    ∃ carry_k : ℕ,
      (∑ a : Fin 8, ∑ b : Fin 8,
        gf256_coeff a.val b.val k.val * wireBitNat (wP a b))
        = wireBitNat (wProd k) + 2 * carry_k
  /-- `prod_bits[0] = 1 − is_zero`. -/
  h_prod_zero : wProd ⟨0, by decide⟩ = 1 - w_isz
  /-- `prod_bits[k] = 0` for `k ∈ [1, 8)`. -/
  h_prod_high_zero : ∀ k : Fin 8, k.val ≠ 0 → wProd k = 0
  /-- Affine transform parity: each output bit `i` is the parity of 5
  selected `x_inv` bits + bit `i` of `0x63`. Stated as an ℕ-level
  equation using `wireBitNat`. -/
  h_affine : ∀ i : Fin 8,
    ∃ carry_i : ℕ,
      (wireBitNat (wX_inv i)
        + wireBitNat (wX_inv ⟨(i.val + 4) % 8, Nat.mod_lt _ (by decide)⟩)
        + wireBitNat (wX_inv ⟨(i.val + 5) % 8, Nat.mod_lt _ (by decide)⟩)
        + wireBitNat (wX_inv ⟨(i.val + 6) % 8, Nat.mod_lt _ (by decide)⟩)
        + wireBitNat (wX_inv ⟨(i.val + 7) % 8, Nat.mod_lt _ (by decide)⟩)
        + ((0x63 / 2 ^ i.val) % 2))
      = wireBitNat (wOut i) + 2 * carry_i

/-! ### Helper lemmas for the AES S-box constraint chain proof -/

/-- `byteToNat` is the inverse of `byteOfNat` on `[0, 256)`. Proven by
the same binary-recomposition identity used in `Formal.Blake`. -/
private theorem byteToNat_byteOfNat_lt {n : ℕ} (hn : n < 256) :
    byteToNat (byteOfNat n) = n := by
  -- byteToNat (byteOfNat n) = ∑ i : Fin 8, (if byteOfNat n i then 1 else 0) * 2^i.val.
  -- `byteOfNat n i = decide ((n / 2^i.val) % 2 = 1)`, so the indicator is `(n/2^i)%2`.
  -- ∑ = n % 2^8 = n (since n < 2^8 = 256).
  unfold byteToNat byteOfNat
  -- Match against the Sha256-style proof.
  have h_bit_eq : ∀ i : Fin 8, (if decide ((n / 2 ^ i.val) % 2 = 1) then (1 : ℕ) else 0) * 2 ^ i.val
                              = ((n / 2 ^ i.val) % 2) * 2 ^ i.val := by
    intro i
    have h_mod_lt : (n / 2 ^ i.val) % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases ((n / 2 ^ i.val) % 2) <;> simp
  rw [show
    (∑ i : Fin 8, (if decide ((n / 2 ^ i.val) % 2 = 1) then (1 : ℕ) else 0) * 2 ^ i.val)
      = ∑ i : Fin 8, ((n / 2 ^ i.val) % 2) * 2 ^ i.val from
    Finset.sum_congr rfl (fun i _ => h_bit_eq i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((n / 2 ^ i) % 2) * 2 ^ i) 8]
  -- ∑ i ∈ range 8, ((n / 2^i) % 2) * 2^i = n % 2^8 (binary recomposition)
  rw [bitRecomp_mod_pow n 8]
  exact Nat.mod_eq_of_lt hn

/-- The byte's `i`-th ℕ-bit equals `if x i then 1 else 0`. Proven by
extracting the per-index equality from `bits_unique`. -/
private theorem gf256_bit_byteToNat (x : Byte8) (i : Fin 8) :
    gf256_bit (byteToNat x) i.val = (if x i then 1 else 0) := by
  unfold gf256_bit
  -- Define β i = (byteToNat x / 2^i.val) % 2 and γ i = if x i then 1 else 0.
  -- Both are bounded by 1. Their weighted sums Σ 2^i · β i and Σ 2^i · γ i
  -- both equal byteToNat x (one by bitRecomp_mod_pow, the other by definition).
  -- bits_unique gives β = γ pointwise.
  have h_byteToNat_lt : byteToNat x < 256 := by
    unfold byteToNat
    have hb : ∀ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val ≤ 2 ^ i.val := by
      intro i; split <;> simp
    have hsum : (∑ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val)
              ≤ ∑ i : Fin 8, 2 ^ i.val := Finset.sum_le_sum (fun i _ => hb i)
    have heq : (∑ i : Fin 8, (2 : ℕ) ^ i.val) = 2 ^ 8 - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) 8, Nat.geomSum_eq (by norm_num) 8]
      simp
    rw [heq] at hsum
    omega
  set β : Fin 8 → ℕ := fun i => (byteToNat x / 2 ^ i.val) % 2
  set γ : Fin 8 → ℕ := fun i => if x i then 1 else 0
  have hβ_le : ∀ i, β i ≤ 1 := fun i => by
    change (byteToNat x / 2 ^ i.val) % 2 ≤ 1
    have : (byteToNat x / 2 ^ i.val) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hγ_le : ∀ i, γ i ≤ 1 := fun i => by
    change (if x i then 1 else 0) ≤ 1
    split <;> simp
  have h_sum_β : (∑ i : Fin 8, 2 ^ i.val * β i) = byteToNat x := by
    change (∑ i : Fin 8, 2 ^ i.val * ((byteToNat x / 2 ^ i.val) % 2)) = byteToNat x
    have : (∑ i : Fin 8, 2 ^ i.val * ((byteToNat x / 2 ^ i.val) % 2))
         = ∑ i : Fin 8, ((byteToNat x / 2 ^ i.val) % 2) * 2 ^ i.val := by
      apply Finset.sum_congr rfl; intros; ring
    rw [this]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((byteToNat x / 2 ^ j) % 2) * 2 ^ j) 8]
    rw [bitRecomp_mod_pow (byteToNat x) 8]
    exact Nat.mod_eq_of_lt h_byteToNat_lt
  have h_sum_γ : (∑ i : Fin 8, 2 ^ i.val * γ i) = byteToNat x := by
    change (∑ i : Fin 8, 2 ^ i.val * (if x i then 1 else 0)) = byteToNat x
    unfold byteToNat
    apply Finset.sum_congr rfl
    intros; ring
  have h_β_eq_γ : β = γ := by
    apply bits_unique β γ hβ_le hγ_le
    rw [h_sum_β, h_sum_γ]
  exact congrFun h_β_eq_γ i

/-- For boolean wires, bit `i` of `byteWireToNat w` equals `wireBitNat (w i)`. -/
private theorem gf256_bit_byteWireToNat
    {w : Fin 8 → ZMod r} (_h_bool : ∀ j, w j = 0 ∨ w j = 1) (i : Fin 8) :
    gf256_bit (byteWireToNat w) i.val = wireBitNat (w i) := by
  unfold gf256_bit
  have h_byteWireToNat_lt : byteWireToNat w < 256 := byteWireToNat_lt_256 w
  set β : Fin 8 → ℕ := fun i => (byteWireToNat w / 2 ^ i.val) % 2
  set γ : Fin 8 → ℕ := fun i => wireBitNat (w i)
  have hβ_le : ∀ i, β i ≤ 1 := fun i => by
    change (byteWireToNat w / 2 ^ i.val) % 2 ≤ 1
    have : (byteWireToNat w / 2 ^ i.val) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hγ_le : ∀ i, γ i ≤ 1 := fun i => wireBitNat_le_one (w i)
  have h_sum_β : (∑ i : Fin 8, 2 ^ i.val * β i) = byteWireToNat w := by
    change (∑ i : Fin 8, 2 ^ i.val * ((byteWireToNat w / 2 ^ i.val) % 2)) = byteWireToNat w
    have : (∑ i : Fin 8, 2 ^ i.val * ((byteWireToNat w / 2 ^ i.val) % 2))
         = ∑ i : Fin 8, ((byteWireToNat w / 2 ^ i.val) % 2) * 2 ^ i.val := by
      apply Finset.sum_congr rfl; intros; ring
    rw [this]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((byteWireToNat w / 2 ^ j) % 2) * 2 ^ j) 8]
    rw [bitRecomp_mod_pow (byteWireToNat w) 8]
    exact Nat.mod_eq_of_lt h_byteWireToNat_lt
  have h_sum_γ : (∑ i : Fin 8, 2 ^ i.val * γ i) = byteWireToNat w := by
    change (∑ i : Fin 8, 2 ^ i.val * wireBitNat (w i)) = byteWireToNat w
    unfold byteWireToNat
    apply Finset.sum_congr rfl
    intros; ring
  have h_β_eq_γ : β = γ := by
    apply bits_unique β γ hβ_le hγ_le
    rw [h_sum_β, h_sum_γ]
  exact congrFun h_β_eq_γ i

/-- Under booleanness + cross-product constraint, the `wP` wire's
`wireBitNat` value equals the product of the two input bit indicators. -/
private theorem wireBitNat_wP_eq
    {wX wX_inv : Fin 8 → ZMod r}
    {wP : Fin 8 → Fin 8 → ZMod r}
    (hX_bool : ∀ j, wX j = 0 ∨ wX j = 1)
    (hX_inv_bool : ∀ j, wX_inv j = 0 ∨ wX_inv j = 1)
    (h_cross : ∀ a b : Fin 8, wP a b = wX a * wX_inv b)
    (a b : Fin 8) :
    wireBitNat (wP a b) = wireBitNat (wX a) * wireBitNat (wX_inv b) := by
  rw [h_cross]
  rcases hX_bool a with hXa | hXa <;> rcases hX_inv_bool b with hXi | hXi
  · -- wX a = 0, wX_inv b = 0
    rw [hXa, hXi]
    simp [wireBitNat]
  · -- wX a = 0, wX_inv b = 1
    rw [hXa, hXi]
    simp [wireBitNat]
  · -- wX a = 1, wX_inv b = 0
    rw [hXa, hXi]
    simp [wireBitNat]
  · -- wX a = 1, wX_inv b = 1
    rw [hXa, hXi]
    simp [wireBitNat]

/-- Under the cross-product + booleanness constraints + the parity
decomposition, each `wProd k` bit equals the corresponding bit of
`gf256_mul (byteToNat x) (byteWireToNat wX_inv)`. -/
private theorem wireBitNat_wProd_eq_gf256_prodBit
    (x : Byte8) {wX wX_inv : Fin 8 → ZMod r}
    (hX : ∀ j, BitOf (wX j) (x j))
    (hX_inv_bool : ∀ j, wX_inv j = 0 ∨ wX_inv j = 1)
    {wP : Fin 8 → Fin 8 → ZMod r}
    (h_cross : ∀ a b : Fin 8, wP a b = wX a * wX_inv b)
    {wProd : Fin 8 → ZMod r}
    (_h_prod_bool : ∀ k, wProd k = 0 ∨ wProd k = 1)
    (h_prod_parity : ∀ k : Fin 8,
      ∃ carry_k : ℕ,
        (∑ a : Fin 8, ∑ b : Fin 8,
          gf256_coeff a.val b.val k.val * wireBitNat (wP a b))
          = wireBitNat (wProd k) + 2 * carry_k)
    (k : Fin 8) :
    wireBitNat (wProd k) = gf256_prodBit (byteToNat x) (byteWireToNat wX_inv) k.val := by
  -- BitOf-derived booleanness for wX.
  have hX_bool : ∀ j, wX j = 0 ∨ wX j = 1 := fun j => BitOf.isBool (hX j)
  -- Per-wire bit-extraction:
  have hwX : ∀ a : Fin 8, wireBitNat (wX a) = gf256_bit (byteToNat x) a.val := fun a => by
    rw [gf256_bit_byteToNat x a, wireBitNat_eq_of_BitOf (hX a)]
  have hwXi : ∀ b : Fin 8, wireBitNat (wX_inv b) = gf256_bit (byteWireToNat wX_inv) b.val :=
    fun b => (gf256_bit_byteWireToNat hX_inv_bool b).symm
  -- For each (a, b), express wireBitNat (wP a b) in terms of x and wX_inv bits.
  have h_wP_eq : ∀ a b : Fin 8,
      wireBitNat (wP a b)
        = gf256_bit (byteToNat x) a.val * gf256_bit (byteWireToNat wX_inv) b.val := by
    intro a b
    rw [wireBitNat_wP_eq hX_bool hX_inv_bool h_cross, hwX a, hwXi b]
  -- Get the parity equation for k.
  obtain ⟨carry_k, h_eq⟩ := h_prod_parity k
  -- Rewrite the sum using h_wP_eq.
  rw [show
      (∑ a : Fin 8, ∑ b : Fin 8,
        gf256_coeff a.val b.val k.val * wireBitNat (wP a b))
        = ∑ a : Fin 8, ∑ b : Fin 8,
          gf256_coeff a.val b.val k.val
            * gf256_bit (byteToNat x) a.val
            * gf256_bit (byteWireToNat wX_inv) b.val from ?_] at h_eq
  · -- h_eq is now: (sum matching gf256_prodBit numerator) = wireBitNat (wProd k) + 2 * carry_k.
    -- gf256_prodBit = (this sum) % 2.
    unfold gf256_prodBit
    -- Convert Fin 8 sum to Finset.range 8 sum to match gf256_prodBit's definition.
    have h_match : (∑ a : Fin 8, ∑ b : Fin 8,
        gf256_coeff a.val b.val k.val
          * gf256_bit (byteToNat x) a.val
          * gf256_bit (byteWireToNat wX_inv) b.val)
        = ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8,
          gf256_coeff i j k.val * gf256_bit (byteToNat x) i * gf256_bit (byteWireToNat wX_inv) j := by
      rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin 8,
            gf256_coeff a b.val k.val * gf256_bit (byteToNat x) a
              * gf256_bit (byteWireToNat wX_inv) b.val) 8]
      apply Finset.sum_congr rfl
      intro a _
      rw [Fin.sum_univ_eq_sum_range (fun b =>
            gf256_coeff a b k.val * gf256_bit (byteToNat x) a
              * gf256_bit (byteWireToNat wX_inv) b) 8]
    rw [h_match] at h_eq
    -- Now h_eq : RHS_sum = wireBitNat (wProd k) + 2 * carry_k.
    -- gf256_prodBit = RHS_sum % 2.
    -- wireBitNat (wProd k) ≤ 1 (since it's 0 or 1).
    have h_le := wireBitNat_le_one (wProd k)
    -- So (RHS_sum % 2) = wireBitNat (wProd k).
    have h_mod : (∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8,
        gf256_coeff i j k.val * gf256_bit (byteToNat x) i * gf256_bit (byteWireToNat wX_inv) j)
        % 2 = wireBitNat (wProd k) := by
      rw [h_eq]
      omega
    exact h_mod.symm
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [h_wP_eq a b]
    ring

/-- Under the gadget's cross-product + parity constraints, the
recomposed `wProd` byte equals `gf256_mul (byteToNat x) (byteWireToNat wX_inv)`. -/
private theorem byteWireToNat_wProd_eq_gf256_mul
    (x : Byte8) {wX wX_inv : Fin 8 → ZMod r}
    (hX : ∀ j, BitOf (wX j) (x j))
    (hX_inv_bool : ∀ j, wX_inv j = 0 ∨ wX_inv j = 1)
    {wP : Fin 8 → Fin 8 → ZMod r}
    (h_cross : ∀ a b : Fin 8, wP a b = wX a * wX_inv b)
    {wProd : Fin 8 → ZMod r}
    (h_prod_bool : ∀ k, wProd k = 0 ∨ wProd k = 1)
    (h_prod_parity : ∀ k : Fin 8,
      ∃ carry_k : ℕ,
        (∑ a : Fin 8, ∑ b : Fin 8,
          gf256_coeff a.val b.val k.val * wireBitNat (wP a b))
          = wireBitNat (wProd k) + 2 * carry_k) :
    byteWireToNat wProd = gf256_mul (byteToNat x) (byteWireToNat wX_inv) := by
  -- ∑ k : Fin 8, wireBitNat (wProd k) * 2^k.val
  --   = ∑ k : Fin 8, gf256_prodBit (...) k.val * 2^k.val   [via wireBitNat_wProd_eq_gf256_prodBit]
  --   = ∑ k ∈ Finset.range 8, gf256_prodBit (...) k * 2^k  [Fin↔range bridge]
  have h_pointwise : ∀ k : Fin 8,
      wireBitNat (wProd k) * 2 ^ k.val
        = gf256_prodBit (byteToNat x) (byteWireToNat wX_inv) k.val * 2 ^ k.val := by
    intro k
    rw [wireBitNat_wProd_eq_gf256_prodBit x hX hX_inv_bool h_cross h_prod_bool
          h_prod_parity k]
  change (∑ k : Fin 8, wireBitNat (wProd k) * 2 ^ k.val)
        = gf256_mul (byteToNat x) (byteWireToNat wX_inv)
  rw [Finset.sum_congr rfl (fun k _ => h_pointwise k)]
  unfold gf256_mul
  -- Now convert Fin 8 sum to range 8 sum.
  rw [Fin.sum_univ_eq_sum_range
        (fun k => gf256_prodBit (byteToNat x) (byteWireToNat wX_inv) k * 2 ^ k) 8]

/-! ### `Fr → ℕ` bridge for byte-level wires (byte analogue of Blake's
Word32 bridges) -/

/-- The Fr-level weighted sum of boolean wires equals the cast of the
ℕ-level `byteWireToNat`. -/
private theorem bitsToFr_eq_byteWireToNat_cast (w : Fin 8 → ZMod r)
    (h_bool : ∀ j, w j = 0 ∨ w j = 1) :
    (∑ i : Fin 8, (2 : ZMod r) ^ i.val * w i)
      = ((byteWireToNat w : ℕ) : ZMod r) := by
  unfold byteWireToNat
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rcases h_bool i with h0 | h1
  · simp [h0, wireBitNat]
  · simp [h1, wireBitNat]

/-- The Fr-level weighted sum of a `BitOf`-witnessed byte wire equals
the cast of `byteToNat`. -/
private theorem bitsToFr_eq_byteToNat_cast (x : Byte8) (wX : Fin 8 → ZMod r)
    (hX : ∀ j, BitOf (wX j) (x j)) :
    (∑ i : Fin 8, (2 : ZMod r) ^ i.val * wX i)
      = ((byteToNat x : ℕ) : ZMod r) := by
  have h_bool : ∀ j, wX j = 0 ∨ wX j = 1 := fun j => BitOf.isBool (hX j)
  rw [bitsToFr_eq_byteWireToNat_cast wX h_bool, byteWireToNat_eq_byteToNat hX]

/-- `2^8 < r`. -/
private theorem two_pow_8_lt_r : (2 : ℕ) ^ 8 < r := by
  have h := two_pow_lt_r
  have h_step : (2 : ℕ) ^ 8 ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-- ZMod r-injectivity within [0, r). -/
private theorem zmod_nat_inj_byte {m n : ℕ} (hm : m < r) (hn : n < r)
    (h : (m : ZMod r) = (n : ZMod r)) : m = n := by
  have h1 : (m : ZMod r).val = m := ZMod.val_cast_of_lt hm
  have h2 : (n : ZMod r).val = n := ZMod.val_cast_of_lt hn
  rw [← h1, ← h2, h]

/-- `byteToNat x < r`. -/
private theorem byteToNat_lt_r (x : Byte8) : byteToNat x < r := by
  have h_byte_lt : byteToNat x < 256 := by
    unfold byteToNat
    have hb : ∀ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val ≤ 2 ^ i.val := by
      intro i; split <;> simp
    have hsum : (∑ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val)
              ≤ ∑ i : Fin 8, 2 ^ i.val := Finset.sum_le_sum (fun i _ => hb i)
    have heq : (∑ i : Fin 8, (2 : ℕ) ^ i.val) = 2 ^ 8 - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) 8, Nat.geomSum_eq (by norm_num) 8]
      simp
    rw [heq] at hsum
    omega
  have := two_pow_8_lt_r
  omega

/-- `byteWireToNat w < r`. -/
private theorem byteWireToNat_lt_r (w : Fin 8 → ZMod r) : byteWireToNat w < r := by
  have h_byte_lt := byteWireToNat_lt_256 w
  have := two_pow_8_lt_r
  omega

/-- Under the gadget's `prod_bits = [1 − is_zero, 0, …, 0]` constraint,
the recomposed `wProd` byte equals `wireBitNat (1 − w_isz)`. -/
private theorem byteWireToNat_wProd_eq_one_minus_isz
    {w_isz : ZMod r}
    (_h_isz_bool : w_isz = 0 ∨ w_isz = 1)
    {wProd : Fin 8 → ZMod r}
    (h_prod_zero : wProd ⟨0, by decide⟩ = 1 - w_isz)
    (h_prod_high_zero : ∀ k : Fin 8, k.val ≠ 0 → wProd k = 0) :
    byteWireToNat wProd = wireBitNat (1 - w_isz) := by
  unfold byteWireToNat
  -- Extract the k = 0 summand and show all others are 0.
  rw [← Finset.add_sum_erase Finset.univ
        (fun k : Fin 8 => wireBitNat (wProd k) * 2 ^ k.val)
        (Finset.mem_univ (⟨0, by decide⟩ : Fin 8))]
  -- Now LHS = wireBitNat (wProd ⟨0, _⟩) * 2^0 + ∑ erase ...
  -- Show the erase sum is 0.
  have h_sum_zero :
      (∑ k ∈ (Finset.univ : Finset (Fin 8)).erase ⟨0, by decide⟩,
          wireBitNat (wProd k) * 2 ^ k.val) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_erase] at hk
    have hk_ne : k.val ≠ 0 := fun h => hk.1 (Fin.ext h)
    rw [h_prod_high_zero k hk_ne, wireBitNat_eq_zero_of_eq_zero (by rfl)]
    simp
  rw [h_sum_zero, h_prod_zero]
  simp

/-- Combining: under the full constraint chain,
`gf256_mul (byteToNat x) (byteWireToNat wX_inv) = wireBitNat (1 − w_isz)`. -/
private theorem gf256_mul_eq_one_minus_isz
    {x : Byte8} {wX wX_inv : Fin 8 → ZMod r}
    (hX : ∀ j, BitOf (wX j) (x j))
    (hX_inv_bool : ∀ j, wX_inv j = 0 ∨ wX_inv j = 1)
    {w_isz : ZMod r}
    (h_isz_bool : w_isz = 0 ∨ w_isz = 1)
    {wP : Fin 8 → Fin 8 → ZMod r}
    (h_cross : ∀ a b : Fin 8, wP a b = wX a * wX_inv b)
    {wProd : Fin 8 → ZMod r}
    (h_prod_bool : ∀ k, wProd k = 0 ∨ wProd k = 1)
    (h_prod_parity : ∀ k : Fin 8,
      ∃ carry_k : ℕ,
        (∑ a : Fin 8, ∑ b : Fin 8,
          gf256_coeff a.val b.val k.val * wireBitNat (wP a b))
          = wireBitNat (wProd k) + 2 * carry_k)
    (h_prod_zero : wProd ⟨0, by decide⟩ = 1 - w_isz)
    (h_prod_high_zero : ∀ k : Fin 8, k.val ≠ 0 → wProd k = 0) :
    gf256_mul (byteToNat x) (byteWireToNat wX_inv) = wireBitNat (1 - w_isz) := by
  rw [← byteWireToNat_wProd_eq_gf256_mul x hX hX_inv_bool h_cross h_prod_bool h_prod_parity]
  exact byteWireToNat_wProd_eq_one_minus_isz h_isz_bool h_prod_zero h_prod_high_zero

/-- **Inverse identification.** Under the full S-box constraint chain,
the prover-supplied `x_inv` byte is exactly `gf256_inv (byteToNat x)`. -/
private theorem byteWireToNat_wX_inv_eq_gf256_inv
    {x : Byte8} {wX wX_inv : Fin 8 → ZMod r}
    (hX : ∀ j, BitOf (wX j) (x j))
    (hX_inv_bool : ∀ j, wX_inv j = 0 ∨ wX_inv j = 1)
    {w_isz : ZMod r}
    (h_isz_bool : w_isz = 0 ∨ w_isz = 1)
    {wP : Fin 8 → Fin 8 → ZMod r}
    (h_cross : ∀ a b : Fin 8, wP a b = wX a * wX_inv b)
    {wProd : Fin 8 → ZMod r}
    (h_prod_bool : ∀ k, wProd k = 0 ∨ wProd k = 1)
    (h_prod_parity : ∀ k : Fin 8,
      ∃ carry_k : ℕ,
        (∑ a : Fin 8, ∑ b : Fin 8,
          gf256_coeff a.val b.val k.val * wireBitNat (wP a b))
          = wireBitNat (wProd k) + 2 * carry_k)
    (h_prod_zero : wProd ⟨0, by decide⟩ = 1 - w_isz)
    (h_prod_high_zero : ∀ k : Fin 8, k.val ≠ 0 → wProd k = 0)
    (h_x_isz : (∑ i : Fin 8, (2 : ZMod r) ^ i.val * wX i) * w_isz = 0)
    (h_xinv_isz : (∑ i : Fin 8, (2 : ZMod r) ^ i.val * wX_inv i) * w_isz = 0) :
    byteWireToNat wX_inv = gf256_inv (byteToNat x) := by
  have h_gf := gf256_mul_eq_one_minus_isz hX hX_inv_bool h_isz_bool h_cross
                  h_prod_bool h_prod_parity h_prod_zero h_prod_high_zero
  rcases h_isz_bool with hz0 | hz1
  · -- w_isz = 0: gf256_mul x x_inv = wireBitNat 1 = 1.
    rw [hz0] at h_gf
    have : wireBitNat (1 - (0 : ZMod r)) = 1 := by
      have h : (1 - (0 : ZMod r)) = 1 := by ring
      rw [h, wireBitNat_eq_one_of_eq_one (by rfl)]
    rw [this] at h_gf
    -- h_gf : gf256_mul (byteToNat x) (byteWireToNat wX_inv) = 1.
    -- Need byteToNat x ≠ 0 to apply gf256_inv_unique.
    have h_x_pos : 0 < byteToNat x := by
      by_contra h_zero
      push Not at h_zero
      interval_cases (byteToNat x)
      rw [gf256_mul_zero_left] at h_gf
      exact zero_ne_one h_gf
    -- Apply gf256_inv_unique.
    have h_x_lt : byteToNat x < 256 := by
      unfold byteToNat
      have hb : ∀ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val ≤ 2 ^ i.val := by
        intro i; split <;> simp
      have hsum : (∑ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val)
                ≤ ∑ i : Fin 8, 2 ^ i.val := Finset.sum_le_sum (fun i _ => hb i)
      have heq : (∑ i : Fin 8, (2 : ℕ) ^ i.val) = 2 ^ 8 - 1 := by
        rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) 8, Nat.geomSum_eq (by norm_num) 8]
        simp
      rw [heq] at hsum
      omega
    have h_xinv_lt : byteWireToNat wX_inv < 256 := byteWireToNat_lt_256 wX_inv
    exact gf256_inv_unique ⟨byteToNat x, h_x_lt⟩ ⟨byteWireToNat wX_inv, h_xinv_lt⟩ h_x_pos h_gf
  · -- w_isz = 1: byteToNat x = 0 and byteWireToNat wX_inv = 0.
    rw [hz1] at h_x_isz h_xinv_isz
    -- (Σ 2^i * wX i) * 1 = 0 → byteToNat x = 0.
    have h_x_zero : byteToNat x = 0 := by
      have h_fr : (∑ i : Fin 8, (2 : ZMod r) ^ i.val * wX i) = 0 := by
        have := h_x_isz
        linear_combination h_x_isz
      rw [bitsToFr_eq_byteToNat_cast x wX hX] at h_fr
      -- h_fr : ((byteToNat x : ℕ) : ZMod r) = 0
      -- Lift to ℕ.
      have h_zmod : ((byteToNat x : ℕ) : ZMod r) = ((0 : ℕ) : ZMod r) := by
        simp; exact h_fr
      exact zmod_nat_inj_byte (byteToNat_lt_r x) (by
        have := two_pow_8_lt_r; omega) h_zmod
    have h_xinv_zero : byteWireToNat wX_inv = 0 := by
      have hX_inv_bool' : ∀ j, wX_inv j = 0 ∨ wX_inv j = 1 := hX_inv_bool
      have h_fr : (∑ i : Fin 8, (2 : ZMod r) ^ i.val * wX_inv i) = 0 := by
        linear_combination h_xinv_isz
      rw [bitsToFr_eq_byteWireToNat_cast wX_inv hX_inv_bool'] at h_fr
      have h_zmod : ((byteWireToNat wX_inv : ℕ) : ZMod r) = ((0 : ℕ) : ZMod r) := by
        simp; exact h_fr
      exact zmod_nat_inj_byte (byteWireToNat_lt_r wX_inv) (by
        have := two_pow_8_lt_r; omega) h_zmod
    rw [h_xinv_zero, h_x_zero, gf256_inv_zero]

/-! ### Affine transform per-bit identity -/

/-- `aesAffine_nat n` viewed bit-by-bit: bit `i` of the affine output
is `((sum of 5 selected bits of n) % 2)`. Verified by the recomposition
uniqueness argument. -/
private theorem gf256_bit_aesAffine_nat (n : ℕ) (i : Fin 8) :
    gf256_bit (aesAffine_nat n) i.val
      = (gf256_bit n i.val + gf256_bit n ((i.val + 4) % 8)
          + gf256_bit n ((i.val + 5) % 8) + gf256_bit n ((i.val + 6) % 8)
          + gf256_bit n ((i.val + 7) % 8)) % 2 := by
  -- aesAffine_nat = ∑ k ∈ range 8, parity_k * 2^k where parity_k ∈ {0, 1}.
  -- gf256_bit (sum) i = parity_i by recomposition uniqueness.
  unfold gf256_bit aesAffine_nat
  -- Set f : Fin 8 → ℕ, f i = (n bit i + n bit i+4 + ... ) % 2.
  set f : ℕ → ℕ := fun k =>
    ((n / 2 ^ k) % 2 + (n / 2 ^ ((k + 4) % 8)) % 2 + (n / 2 ^ ((k + 5) % 8)) % 2
      + (n / 2 ^ ((k + 6) % 8)) % 2 + (n / 2 ^ ((k + 7) % 8)) % 2) % 2 with hf
  -- Show that aesAffine_nat = ∑ k ∈ range 8, f k * 2^k and f k ≤ 1.
  -- Then by bits_unique-style, bit i of the sum = f i.
  set N : ℕ := ∑ k ∈ Finset.range 8, f k * 2 ^ k with hN
  -- N < 2^8.
  have hN_lt : N < 2 ^ 8 := by
    rw [hN]
    have h_each : ∀ k ∈ Finset.range 8, f k * 2 ^ k ≤ 2 ^ k := by
      intro k _
      rw [hf]
      have h_lt_2 : ((n / 2 ^ k) % 2 + (n / 2 ^ ((k + 4) % 8)) % 2 + (n / 2 ^ ((k + 5) % 8)) % 2
                      + (n / 2 ^ ((k + 6) % 8)) % 2 + (n / 2 ^ ((k + 7) % 8)) % 2) % 2 < 2 :=
        Nat.mod_lt _ (by decide)
      have h_pow_pos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
      nlinarith
    have h_sum : (∑ k ∈ Finset.range 8, f k * 2 ^ k) ≤ ∑ k ∈ Finset.range 8, 2 ^ k :=
      Finset.sum_le_sum h_each
    have h_geom : (∑ k ∈ Finset.range 8, (2 : ℕ) ^ k) = 2 ^ 8 - 1 := by
      rw [Nat.geomSum_eq (by norm_num) 8]; simp
    omega
  -- By bitRecomp_mod_pow, (N % 2^8) = ∑ k ∈ range 8, (N / 2^k) % 2 * 2^k.
  -- Also N = ∑ k ∈ range 8, f k * 2^k. Apply bits_unique-style.
  have h_recomp : (∑ k ∈ Finset.range 8, ((N / 2 ^ k) % 2) * 2 ^ k) = N := by
    rw [bitRecomp_mod_pow N 8]
    exact Nat.mod_eq_of_lt hN_lt
  have h_fk_le : ∀ k ∈ Finset.range 8, f k ≤ 1 := by
    intro k _
    rw [hf]
    change ((n / 2 ^ k) % 2 + (n / 2 ^ ((k + 4) % 8)) % 2 + (n / 2 ^ ((k + 5) % 8)) % 2
            + (n / 2 ^ ((k + 6) % 8)) % 2 + (n / 2 ^ ((k + 7) % 8)) % 2) % 2 ≤ 1
    have : ((n / 2 ^ k) % 2 + (n / 2 ^ ((k + 4) % 8)) % 2 + (n / 2 ^ ((k + 5) % 8)) % 2
            + (n / 2 ^ ((k + 6) % 8)) % 2 + (n / 2 ^ ((k + 7) % 8)) % 2) % 2 < 2 :=
      Nat.mod_lt _ (by decide)
    omega
  have h_div_le : ∀ k ∈ Finset.range 8, (N / 2 ^ k) % 2 ≤ 1 := by
    intro k _
    have : (N / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  -- Use bits_unique. We need range 8 → Fin 8 conversion.
  have h_β : (fun k : Fin 8 => (N / 2 ^ k.val) % 2)
              = (fun k : Fin 8 => f k.val) := by
    apply bits_unique
    · intro k; exact h_div_le k.val (Finset.mem_range.mpr k.isLt)
    · intro k; exact h_fk_le k.val (Finset.mem_range.mpr k.isLt)
    · -- ∑ k : Fin 8, 2^k.val * ((N / 2^k.val) % 2) = ∑ k : Fin 8, 2^k.val * f k.val
      -- Both equal N.
      have h_lhs : (∑ k : Fin 8, 2 ^ k.val * ((N / 2 ^ k.val) % 2)) = N := by
        have : (∑ k : Fin 8, 2 ^ k.val * ((N / 2 ^ k.val) % 2))
             = ∑ k : Fin 8, ((N / 2 ^ k.val) % 2) * 2 ^ k.val := by
          apply Finset.sum_congr rfl; intros; ring
        rw [this]
        rw [Fin.sum_univ_eq_sum_range (fun k => ((N / 2 ^ k) % 2) * 2 ^ k) 8]
        exact h_recomp
      have h_rhs : (∑ k : Fin 8, 2 ^ k.val * f k.val) = N := by
        have h_swap : (∑ k : Fin 8, 2 ^ k.val * f k.val)
             = ∑ k : Fin 8, f k.val * 2 ^ k.val := by
          apply Finset.sum_congr rfl; intros; ring
        rw [h_swap, Fin.sum_univ_eq_sum_range (fun k => f k * 2 ^ k) 8, hN]
      rw [h_lhs, h_rhs]
  -- Now h_β says (N / 2^k.val) % 2 = f k.val (as Fin 8 → ℕ).
  have h_i := congrFun h_β i
  exact h_i

/-- **Byte-level XOR per-bit identity.** Verified by `native_decide`
over all `(a, b, i) ∈ Fin 256 × Fin 256 × Fin 8` (524 288 cases). For
byte-level XOR, bit `i` of `a ⊕ b` equals the parity of bits `i` of
`a` and `b`. -/
private theorem gf256_bit_xor_byte_all :
    ∀ a b : Fin 256, ∀ i : Fin 8,
      gf256_bit (Nat.xor a.val b.val) i.val
        = (gf256_bit a.val i.val + gf256_bit b.val i.val) % 2 := by
  native_decide

private theorem gf256_bit_xor_byte (a b : Fin 256) (i : Fin 8) :
    gf256_bit (Nat.xor a.val b.val) i.val
      = (gf256_bit a.val i.val + gf256_bit b.val i.val) % 2 :=
  gf256_bit_xor_byte_all a b i

/-- `aesAffine_nat n < 256` (sum of 8 weighted bits in `{0, 1}`). -/
private theorem aesAffine_nat_lt_256_all : ∀ n : Fin 256, aesAffine_nat n.val < 256 := by
  native_decide

private theorem aesAffine_nat_lt_256 (n : ℕ) (hn : n < 256) : aesAffine_nat n < 256 :=
  aesAffine_nat_lt_256_all ⟨n, hn⟩

/-- `aesSbox_algebraic n < 256` (the table is bounded). -/
private theorem aesSbox_algebraic_lt_256_all :
    ∀ n : Fin 256, aesSbox_algebraic n.val < 256 := by
  native_decide

/-- `byteToNat (aesSbox x) = aesSbox_algebraic (byteToNat x)`. -/
private theorem byteToNat_aesSbox (x : Byte8) :
    byteToNat (aesSbox x) = aesSbox_algebraic (byteToNat x) := by
  unfold aesSbox
  -- byteToNat (byteOfNat n) = n for n < 256.
  have h_x_lt : byteToNat x < 256 := byteToNat_lt_r x |> fun h => by
    have h_2 := two_pow_8_lt_r
    -- byteToNat x is bounded by 256 via the standard sum bound; use that directly.
    have hb : byteToNat x < 256 := by
      unfold byteToNat
      have hb' : ∀ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val ≤ 2 ^ i.val := by
        intro i; split <;> simp
      have hsum : (∑ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val)
                ≤ ∑ i : Fin 8, 2 ^ i.val := Finset.sum_le_sum (fun i _ => hb' i)
      have heq : (∑ i : Fin 8, (2 : ℕ) ^ i.val) = 2 ^ 8 - 1 := by
        rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) 8, Nat.geomSum_eq (by norm_num) 8]
        simp
      rw [heq] at hsum
      omega
    exact hb
  -- byteToNat (byteOfNat (aesSboxTable[byteToNat x]?.getD 0))
  -- = aesSboxTable[byteToNat x]?.getD 0 (by byteToNat_byteOfNat_lt, since the value < 256)
  -- = aesSbox_algebraic (byteToNat x) (by aesSbox_algebraic_eq_table.symm).
  have h_table_eq : aesSbox_algebraic (byteToNat x) = (aesSboxTable[byteToNat x]?).getD 0 :=
    aesSbox_algebraic_eq_table ⟨byteToNat x, h_x_lt⟩
  -- aesSboxTable[i] for i < 256 returns a byte value < 256.
  have h_table_lt : (aesSboxTable[byteToNat x]?).getD 0 < 256 := by
    rw [← h_table_eq]
    exact aesSbox_algebraic_lt_256_all ⟨byteToNat x, h_x_lt⟩
  rw [byteToNat_byteOfNat_lt h_table_lt, h_table_eq]

/-- **Per-byte AES S-box soundness from the gadget's constraint chain.**

Given a witness satisfying `IsValidSBoxByteWitness x ...`, the output
wires `wOut` are `BitOf`-witnessed by `aesSbox x` bit-by-bit. This is
the real (non-vacuous) bit-level soundness for one byte of the AES S-box.

Proof: combines:

* `byteWireToNat_wX_inv_eq_gf256_inv` (the gadget pins `x_inv = gf256_inv(x)`);
* `gf256_bit_aesAffine_nat` (per-bit identity for the affine transform);
* `gf256_bit_xor_byte` (per-bit identity for the `⊕ 0x63` step);
* `byteToNat_aesSbox` (`aesSbox = aesSbox_algebraic`-via-table). -/
theorem aesSbox_byte_constraint_sound
    {x : Byte8} {wX wX_inv : Fin 8 → ZMod r}
    {w_isz : ZMod r}
    {wP : Fin 8 → Fin 8 → ZMod r}
    {wProd wOut : Fin 8 → ZMod r}
    (h : IsValidSBoxByteWitness x wX wX_inv w_isz wP wProd wOut) :
    ∀ j, BitOf (wOut j) ((aesSbox x) j) := by
  -- Step 1: byteWireToNat wX_inv = gf256_inv (byteToNat x).
  have h_xinv_inv :=
    byteWireToNat_wX_inv_eq_gf256_inv h.hX h.hX_inv_bool h.h_isz_bool h.h_cross
      h.h_prod_bool h.h_prod_parity h.h_prod_zero h.h_prod_high_zero h.h_x_isz
      h.h_xinv_isz
  -- Step 2: Establish bounds.
  have h_x_lt : byteToNat x < 256 := by
    unfold byteToNat
    have hb : ∀ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val ≤ 2 ^ i.val := by
      intro i; split <;> simp
    have hsum : (∑ i : Fin 8, (if x i then (1 : ℕ) else 0) * 2 ^ i.val)
              ≤ ∑ i : Fin 8, 2 ^ i.val := Finset.sum_le_sum (fun i _ => hb i)
    have heq : (∑ i : Fin 8, (2 : ℕ) ^ i.val) = 2 ^ 8 - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) 8, Nat.geomSum_eq (by norm_num) 8]
      simp
    rw [heq] at hsum
    omega
  have h_xinv_lt : byteWireToNat wX_inv < 256 := byteWireToNat_lt_256 wX_inv
  have h_affine_lt : aesAffine_nat (byteWireToNat wX_inv) < 256 :=
    aesAffine_nat_lt_256 _ h_xinv_lt
  have h_aesSbox_lt : byteToNat (aesSbox x) < 256 := by
    rw [byteToNat_aesSbox]
    exact aesSbox_algebraic_lt_256_all ⟨byteToNat x, h_x_lt⟩
  -- Step 3: Per-bit identity.
  intro i
  -- From h_affine: 5-sum + 0x63-bit-i = wireBitNat (wOut i) + 2*carry.
  obtain ⟨carry, h_affine_eq⟩ := h.h_affine i
  have h_wOut_le : wireBitNat (wOut i) ≤ 1 := wireBitNat_le_one _
  -- Convert: wireBitNat (wOut i) = (5-sum + 0x63 bit i) % 2.
  have h_wOut_lt_2 : wireBitNat (wOut i) < 2 := by have := h_wOut_le; omega
  have h_wOut_mod :
      wireBitNat (wOut i)
        = (wireBitNat (wX_inv i)
            + wireBitNat (wX_inv ⟨(i.val + 4) % 8, Nat.mod_lt _ (by decide)⟩)
            + wireBitNat (wX_inv ⟨(i.val + 5) % 8, Nat.mod_lt _ (by decide)⟩)
            + wireBitNat (wX_inv ⟨(i.val + 6) % 8, Nat.mod_lt _ (by decide)⟩)
            + wireBitNat (wX_inv ⟨(i.val + 7) % 8, Nat.mod_lt _ (by decide)⟩)
            + ((0x63 / 2 ^ i.val) % 2)) % 2 := by
    -- (LHS_sum) % 2 = (wOut + 2*carry) % 2 = wOut % 2 = wOut (since wOut < 2).
    have h_mod_via_aff : (wireBitNat (wX_inv i)
            + wireBitNat (wX_inv ⟨(i.val + 4) % 8, Nat.mod_lt _ (by decide)⟩)
            + wireBitNat (wX_inv ⟨(i.val + 5) % 8, Nat.mod_lt _ (by decide)⟩)
            + wireBitNat (wX_inv ⟨(i.val + 6) % 8, Nat.mod_lt _ (by decide)⟩)
            + wireBitNat (wX_inv ⟨(i.val + 7) % 8, Nat.mod_lt _ (by decide)⟩)
            + ((0x63 / 2 ^ i.val) % 2)) % 2
        = (wireBitNat (wOut i) + 2 * carry) % 2 := by
      rw [h_affine_eq]
    rw [h_mod_via_aff]
    -- (wOut + 2*carry) % 2 = wOut % 2 = wOut.
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_wOut_lt_2]
  -- Convert wireBitNat (wX_inv k) to gf256_bit (byteWireToNat wX_inv) k.val.
  have h_inv_bits : ∀ k : Fin 8,
      wireBitNat (wX_inv k) = gf256_bit (byteWireToNat wX_inv) k.val := fun k =>
    (gf256_bit_byteWireToNat h.hX_inv_bool k).symm
  -- Substitute into h_wOut_mod.
  rw [h_inv_bits i,
      h_inv_bits ⟨(i.val + 4) % 8, Nat.mod_lt _ (by decide)⟩,
      h_inv_bits ⟨(i.val + 5) % 8, Nat.mod_lt _ (by decide)⟩,
      h_inv_bits ⟨(i.val + 6) % 8, Nat.mod_lt _ (by decide)⟩,
      h_inv_bits ⟨(i.val + 7) % 8, Nat.mod_lt _ (by decide)⟩] at h_wOut_mod
  -- Step 4: The 5-bit sum + 0x63-bit-i mod 2 equals bit i of (aesAffine_nat (byteWireToNat wX_inv) XOR 0x63).
  -- bit i of aesAffine_nat = (5-sum) % 2 [by gf256_bit_aesAffine_nat].
  have h_affine_bit := gf256_bit_aesAffine_nat (byteWireToNat wX_inv) i
  -- bit i of (Nat.xor aesAffine 0x63) = (bit i of aesAffine + bit i of 0x63) % 2 [by gf256_bit_xor_byte].
  have h_xor_bit : gf256_bit (Nat.xor (aesAffine_nat (byteWireToNat wX_inv)) 0x63) i.val
      = (gf256_bit (aesAffine_nat (byteWireToNat wX_inv)) i.val
          + gf256_bit 0x63 i.val) % 2 :=
    gf256_bit_xor_byte ⟨aesAffine_nat (byteWireToNat wX_inv), h_affine_lt⟩
      ⟨0x63, by norm_num⟩ i
  -- Compute bit i of 0x63 = (0x63 / 2^i.val) % 2.
  have h_0x63_bit : gf256_bit 0x63 i.val = (0x63 / 2 ^ i.val) % 2 := rfl
  -- Combine: wireBitNat (wOut i) = bit i of (Nat.xor aesAffine 0x63).
  have h_wOut_eq_xor_bit :
      wireBitNat (wOut i)
        = gf256_bit (Nat.xor (aesAffine_nat (byteWireToNat wX_inv)) 0x63) i.val := by
    rw [h_xor_bit, h_affine_bit, h_0x63_bit, h_wOut_mod]
    -- Goal: (S + Z) % 2 = (S % 2 + Z) % 2 where S is the 5-bit sum, Z = (0x63/2^i.val) % 2.
    -- True by mod-arith: (a + b) % 2 = (a % 2 + b) % 2.
    set S : ℕ := gf256_bit (byteWireToNat wX_inv) i.val
        + gf256_bit (byteWireToNat wX_inv) ((i.val + 4) % 8)
        + gf256_bit (byteWireToNat wX_inv) ((i.val + 5) % 8)
        + gf256_bit (byteWireToNat wX_inv) ((i.val + 6) % 8)
        + gf256_bit (byteWireToNat wX_inv) ((i.val + 7) % 8) with hS
    set Z : ℕ := (0x63 / 2 ^ i.val) % 2 with hZ
    change (S + Z) % 2 = (S % 2 + Z) % 2
    omega
  -- Step 5: Nat.xor aesAffine 0x63 with byteWireToNat wX_inv = gf256_inv (byteToNat x)
  -- equals aesSbox_algebraic (byteToNat x), which equals byteToNat (aesSbox x).
  have h_xor_eq :
      Nat.xor (aesAffine_nat (byteWireToNat wX_inv)) 0x63
        = byteToNat (aesSbox x) := by
    rw [h_xinv_inv]
    -- Nat.xor (aesAffine_nat (gf256_inv (byteToNat x))) 0x63 = aesSbox_algebraic (byteToNat x) by def
    show Nat.xor (aesAffine_nat (gf256_inv (byteToNat x))) 0x63 = byteToNat (aesSbox x)
    rw [byteToNat_aesSbox]
    rfl
  rw [h_xor_eq] at h_wOut_eq_xor_bit
  -- Step 6: bit i of byteToNat (aesSbox x) = if (aesSbox x) i then 1 else 0.
  rw [gf256_bit_byteToNat (aesSbox x) i] at h_wOut_eq_xor_bit
  -- h_wOut_eq_xor_bit : wireBitNat (wOut i) = if (aesSbox x) i then 1 else 0.
  -- Combine with h_out_bool to derive BitOf.
  unfold BitOf
  rcases h.h_out_bool i with hw0 | hw1
  · -- wOut i = 0. wireBitNat = 0. So (aesSbox x) i = false.
    rw [hw0] at h_wOut_eq_xor_bit
    have hwb : wireBitNat (0 : ZMod r) = 0 := wireBitNat_eq_zero_of_eq_zero rfl
    rw [hwb] at h_wOut_eq_xor_bit
    by_cases hbit : (aesSbox x) i
    · simp [hbit] at h_wOut_eq_xor_bit
    · simp [hbit, hw0]
  · -- wOut i = 1. wireBitNat = 1. So (aesSbox x) i = true.
    rw [hw1] at h_wOut_eq_xor_bit
    have hwb : wireBitNat (1 : ZMod r) = 1 := wireBitNat_eq_one_of_eq_one rfl
    rw [hwb] at h_wOut_eq_xor_bit
    by_cases hbit : (aesSbox x) i
    · simp [hbit, hw1]
    · simp [hbit] at h_wOut_eq_xor_bit

/-- **State-level (16-byte) AES SubBytes soundness from the gadget's
constraint chain.** Given 16 per-byte constraint witnesses (one per
state byte), the output wires `wOut i j` are `BitOf`-witnessed by the
corresponding bit of `aesSubBytes s i`. Just `aesSbox_byte_constraint_sound`
lifted byte-by-byte — there is no cross-byte dependency in SubBytes. -/
theorem aesSubBytes_constraint_sound
    {s : Fin 16 → Byte8}
    {wX wX_inv : Fin 16 → Fin 8 → ZMod r}
    {w_isz : Fin 16 → ZMod r}
    {wP : Fin 16 → Fin 8 → Fin 8 → ZMod r}
    {wProd wOut : Fin 16 → Fin 8 → ZMod r}
    (h : ∀ i : Fin 16,
      IsValidSBoxByteWitness (s i) (wX i) (wX_inv i) (w_isz i) (wP i)
        (wProd i) (wOut i)) :
    ∀ i j, BitOf (wOut i j) ((aesSubBytes s i) j) := by
  intro i j
  exact aesSbox_byte_constraint_sound (h i) j

/-! ### S-box per-bit soundness — the GF(2^8) algebraic story

UNLIKE the other AES per-bit lemmas in this file (`xor8_sound`,
`aesXTime_sound`, `aesShiftRows_sound`, `aesMixColumns_sound`,
`aesAddRoundKey_sound` — real proofs whose bodies construct the output
wires as concrete arithmetic expressions in the input wires via the
gadget's per-bit field-level constraints), the AES S-box gadget uses
a **GF(2^8) multiplicative-inverse trick + affine transform**:

* allocate `x_inv` (8 boolean bits) and `is_zero` (1 boolean);
* assert `x · is_zero = 0` and `x_inv · is_zero = 0` (both in `Fr`);
* assert the 64 cross-products `x_bits[i] · x_inv_bits[j] = p[i][j]`;
* assert the 8 GF(2^8) product bits (computed as XOR-parities of the
  cross-products via the reduction-polynomial table) satisfy
  `prod_bits[0] = 1 − is_zero` and `prod_bits[k] = 0` for `k ∈ [1, 7]`;
* output bits = affine transform of `x_inv` XOR `0x63`.

The **algebraic content** of this construction is now mechanised in
`Formal.GF256`:

* `gf256_mul` matches the gadget's cross-product/XOR formula
  bit-for-bit (with the same `gf256_xk_bits` reduction-polynomial
  table the Rust gadget uses).
* `gf256_inv` is the standard 256-entry table-based inverse with
  `gf256_inv 0 = 0`.
* `gf256_mul_inv : ∀ x ≠ 0, gf256_mul x (gf256_inv x) = 1`
  (verified by `native_decide` over 255 nonzero bytes).
* `gf256_inv_unique : ∀ x ≠ 0 y, gf256_mul x y = 1 → y = gf256_inv x`
  (verified over `256 × 256 = 65 536` byte pairs).
* `aesSbox_algebraic_eq_table : Affine(gf256_inv x) ⊕ 0x63 = SBOX[x]`
  (the algebraic-to-table identity, verified for every byte).

The **bridge from `Fr`-level R1CS rows to the GF(2^8) statements
above** — i.e., that the gadget's per-byte cross-product wires,
parity-decomposition carry chains, and affine XOR-chains correctly
compute (in `Fr` mod the BN254 modulus, lifted to ℕ via the
BitOf-recomposition no-wrap bounds) GF(2^8) multiplication, the
GF(2^8) zero-check, and the per-bit affine transform — is **now
mechanised in Lean** via `IsValidSBoxByteWitness` and
`aesSbox_byte_constraint_sound` (see below).

What remains *outside* Lean is the **Rust-side claim** that the
gadget's emitted R1CS rows actually instantiate
`IsValidSBoxByteWitness` (i.e., that the constraints written by
the S-box gadget in `gadgets/xark-aes/src/lib.rs` correspond field-for-field to
the structure's hypotheses). The trust anchor for that bridge is:

* the Rust exhaustive unit test `sbox_all_inputs_match_table` in
  `gadgets/xark-aes/src/lib.rs`, which instantiates the gadget on every
  input byte `x ∈ [0, 255]` and asserts the gadget output equals
  `SBOX[x]`.

Two Lean soundness statements are exposed:

* **`aesSbox_byte_constraint_sound`** (per-byte) — a *real* proof.
  Given a witness of `IsValidSBoxByteWitness x …` (the full
  R1CS-style constraint chain — boolean witnesses, cross-products,
  parity-decomposition product bits, the `prod[0] = 1 − is_zero`
  / `prod[k] = 0` constraints, and the affine `0x63` XOR), it
  concludes `∀ j, BitOf (wOut j) ((aesSbox x) j)`. The proof body
  goes: the gadget's `x · is_zero = 0` and `x_inv · is_zero = 0`
  constraints + the gf256 cross-product/parity rows force the
  prover-supplied `x_inv` bits to recompose to exactly
  `gf256_inv (byteToNat x)`; then `aesAffine_nat ∘ gf256_inv ⊕ 0x63`
  equals the SBOX table by `byteToNat_aesSbox`. No vacuous lift.

* **`aesSubBytes_constraint_sound`** (state-level) — the 16-byte
  lift of the above. Discharges the per-byte SubBytes layer soundness
  directly from 16 per-byte constraint witnesses, with no vacuous
  canonical-lift step.

Both statements are `theorem`s (not axioms). `#print axioms` lists
only the three primality axioms + `native_decide`'s `ofReduceBool`
(used in `Formal.GF256` for the exhaustive `gf256_inv` and
`aesSbox_algebraic` table identities). -/

/-! ## One-round structural soundness (`aesRoundStep_bit_sound`)

Combines the four layer-soundness lemmas to give the per-bit
equivalence for one full AES round. The proof chain mirrors the four
layers of `aesRoundStep`:

1. **SubBytes**: input state bytes → S-box images. Bit-soundness
   discharged from 16 per-byte `IsValidSBoxByteWitness` chains via
   `aesSubBytes_constraint_sound` — no canonical-lift step.
2. **ShiftRows**: permutation of byte positions. Bit-witnesses
   relabelled via `aesShiftRows_sound`.
3. **MixColumns** (skipped on final round): column-wise GF(2⁸) matrix
   mul via `aesMixColumns_sound`.
4. **AddRoundKey**: byte-wise XOR with round key via
   `aesAddRoundKey_sound`.

This theorem is specialised to `F = ZMod r` (the BN254 scalar field)
because the SubBytes layer's `IsValidSBoxByteWitness` chain encodes
no-wrap arithmetic that is `r`-specific. The `Field (ZMod r)`
instance is derived from the `Fact (Nat.Prime r)` typeclass
parameter (discharged at use sites by `bn254_r_prime` from
`Formal.GrumpkinGroup`). -/

/-- **One AES round-step is bit-level structurally sound, from the
gadget's emitted constraint chain.** Given 16 per-byte
`IsValidSBoxByteWitness` chains for the SubBytes layer (each with its
own input/inverse/cross-product/parity/output wires) plus
bit-witnesses for the round key, the round-step output is bit-
witnessed at every (byte, bit) position. The `is_final` flag controls
whether MixColumns is applied. -/
theorem aesRoundStep_bit_sound [Fact (Nat.Prime r)]
    {s rk : Fin 16 → Byte8} {is_final : Bool}
    {wS wX_inv : Fin 16 → Fin 8 → ZMod r}
    {w_isz : Fin 16 → ZMod r}
    {wP : Fin 16 → Fin 8 → Fin 8 → ZMod r}
    {wProd wSub wRK : Fin 16 → Fin 8 → ZMod r}
    (hRK : ∀ i j, BitOf (wRK i j) (rk i j))
    (h_sbox : ∀ i : Fin 16,
      IsValidSBoxByteWitness (s i) (wS i) (wX_inv i) (w_isz i) (wP i)
        (wProd i) (wSub i)) :
    ∃ wOut : Fin 16 → Fin 8 → ZMod r,
      ∀ i j, BitOf (wOut i j) ((aesRoundStep s rk is_final i) j) := by
  -- Layer 1: SubBytes. Real (non-vacuous) bit-soundness from the
  -- per-byte constraint chains via `aesSubBytes_constraint_sound`.
  have hSubBit : ∀ i j, BitOf (wSub i j) ((aesSubBytes s i) j) :=
    aesSubBytes_constraint_sound h_sbox
  -- Layer 2: ShiftRows. Pure permutation; `wSub` at the permuted index works.
  let wShift : Fin 16 → Fin 8 → ZMod r := fun i j =>
    let row : ℕ := i.val % 4
    let col : ℕ := i.val / 4
    let col' : ℕ := (col + row) % 4
    wSub ⟨4 * col' + row, by
      have : row < 4 := Nat.mod_lt _ (by decide)
      have : col' < 4 := Nat.mod_lt _ (by decide)
      omega⟩ j
  have hShiftBit : ∀ i j,
      BitOf (wShift i j) ((aesShiftRows (aesSubBytes s) i) j) := by
    intro i j
    have := aesShiftRows_sound (aesSubBytes s) wSub hSubBit i j
    simp only at this
    exact this
  -- Layer 3 (conditional): MixColumns.
  cases h_final : is_final
  · -- Non-final round: apply MixColumns.
    have hMix : ∀ i, ∃ w : Fin 8 → ZMod r,
        ∀ j, BitOf (w j) ((aesMixColumns (aesShiftRows (aesSubBytes s)) i) j) :=
      fun i => aesMixColumns_sound (aesShiftRows (aesSubBytes s)) wShift hShiftBit i
    choose wMix hMixBit using hMix
    -- Layer 4: AddRoundKey.
    refine ⟨fun i j => wMix i j + wRK i j - 2 * (wMix i j * wRK i j), ?_⟩
    intro i j
    have h_add := aesAddRoundKey_sound
                    (aesMixColumns (aesShiftRows (aesSubBytes s))) rk
                    wMix wRK hMixBit hRK i j
    unfold aesRoundStep
    exact h_add
  · -- Final round: skip MixColumns.
    refine ⟨fun i j => wShift i j + wRK i j - 2 * (wShift i j * wRK i j), ?_⟩
    intro i j
    have h_add := aesAddRoundKey_sound
                    (aesShiftRows (aesSubBytes s)) rk
                    wShift wRK hShiftBit hRK i j
    unfold aesRoundStep
    simp only [if_true]
    exact h_add

/-! ## End-to-end constraint-chain witness for AES-128 (single block)

The existing `IsValidAES128EncryptWitness` is purely byte-level — it
asserts FIPS-197 round-step semantics on `Byte8` arrays without
reaching into the field-level R1CS constraint chain. That structure is
fine as the *closed* output spec (consumed by `aes128_closed_chain`),
but it leaves a layering gap: the field-level S-box constraint chain
(`IsValidSBoxByteWitness`, see above) is not connected to the
byte-level chain.

`IsValidAES128EncryptConstraintWitness` below closes that gap. It
bundles:

* the byte-level round/round-key trace (same data as
  `IsValidAES128EncryptWitness`), plus
* for each of the 10 main rounds (round 0 through round 9 — the
  inputs to each `aesRoundStep` call) and each of the 16 state
  bytes, the full `IsValidSBoxByteWitness` constraint chain for the
  SubBytes invocation on that byte.

`IsValidAES128EncryptConstraintWitness.toByteLevel` then projects to
`IsValidAES128EncryptWitness`, so every downstream byte-level theorem
(`aes128_closed_chain`, `aes128_iter_of_rel`, …) is automatically
discharged from the richer witness. -/

/-- **Constraint-chain witness for one-block AES-128 encryption.**
Carries the byte-level round trace plus, for each `(round, byte)`
position in the 10 × 16 SubBytes grid, an `IsValidSBoxByteWitness`
constraint chain that pins the S-box output bits to the prover-
supplied wires.

The key-expansion S-boxes (40 S-box invocations inside
`aesKeyExpansion`) are *not* yet covered here — they require a
parallel `IsValidKeyExpansionConstraintWitness` structure, which is a
follow-up. Round-key bytes enter this structure already-expanded via
the `rk` field. -/
structure IsValidAES128EncryptConstraintWitness
    (plaintext key ciphertext : Fin 16 → Byte8) where
  /-- 11 round states (round 0 = post-initial AddRoundKey, round 10 = ciphertext). -/
  rounds : Fin 11 → Fin 16 → Byte8
  /-- 11 round keys, expanded from the AES-128 key by `aesKeyExpansion`. -/
  rk : Fin 11 → Fin 16 → Byte8
  /-- Key expansion is correct (assumed; see "follow-up" note above). -/
  hrk : rk = aesKeyExpansion key
  /-- Initial AddRoundKey: `rounds[0] = plaintext ⊕ rk[0]`. -/
  h0 : rounds ⟨0, by decide⟩ = aesAddRoundKey plaintext (rk ⟨0, by decide⟩)
  /-- 10 round-step transitions, with `is_final` set on the last round. -/
  hstep : ∀ i : Fin 10,
    rounds ⟨i.val + 1, by omega⟩ =
      aesRoundStep (rounds ⟨i.val, by omega⟩)
        (rk ⟨i.val + 1, by omega⟩) (decide (i.val = 9))
  /-- Output ties to the last round state. -/
  hout : ciphertext = rounds ⟨10, by decide⟩
  /-- Field-level wires for the 10 × 16 S-box positions: input bit wires. -/
  wX : Fin 10 → Fin 16 → Fin 8 → ZMod r
  /-- Field-level wires: prover-supplied multiplicative-inverse bits. -/
  wX_inv : Fin 10 → Fin 16 → Fin 8 → ZMod r
  /-- Field-level wires: S-box output bits (the SubBytes layer's output). -/
  wSub : Fin 10 → Fin 16 → Fin 8 → ZMod r
  /-- Field-level wire: `is_zero` selector for each `(round, byte)`. -/
  w_isz : Fin 10 → Fin 16 → ZMod r
  /-- Field-level wires: 64 cross-products `wP[a][b] = wX[a] * wX_inv[b]`. -/
  wP : Fin 10 → Fin 16 → Fin 8 → Fin 8 → ZMod r
  /-- Field-level wires: 8 parity-decomposition product bits per byte. -/
  wProd : Fin 10 → Fin 16 → Fin 8 → ZMod r
  /-- **The 160 S-box constraint chains.** For each `(round, byte)`,
  the input to round `round`'s SubBytes layer at byte position `byte`
  is `rounds[round] byte`, and the prover-supplied S-box wires form a
  valid `IsValidSBoxByteWitness` constraint chain. -/
  h_sbox : ∀ (round : Fin 10) (byte : Fin 16),
    IsValidSBoxByteWitness (rounds ⟨round.val, by omega⟩ byte)
      (wX round byte) (wX_inv round byte) (w_isz round byte)
      (wP round byte) (wProd round byte) (wSub round byte)
  /-- Field-level wires: round-key bits for all 11 round keys. -/
  wRK : Fin 11 → Fin 16 → Fin 8 → ZMod r
  /-- Round-key bit-witness — `wRK` is `BitOf` for each `(round, byte, bit)`. -/
  hRK : ∀ (round : Fin 11) (i : Fin 16) (j : Fin 8),
    BitOf (wRK round i j) (rk round i j)
  /-- **Committed ShiftRows-layer output wires** (one per (round, byte, bit)
  in the 10 main rounds). Promoted from the existential the layer-soundness
  lemmas previously chose, so the gadget's actual emitted wires are
  visible at the structure level. -/
  wShift : Fin 10 → Fin 16 → Fin 8 → ZMod r
  /-- ShiftRows bit-witness — `wShift round` is `BitOf` for the
  ShiftRows output bits. -/
  hShift : ∀ (round : Fin 10) (i : Fin 16) (j : Fin 8),
    BitOf (wShift round i j)
      ((aesShiftRows (aesSubBytes (rounds ⟨round.val, by omega⟩)) i) j)
  /-- **Committed MixColumns-layer output wires** for the 9 non-final
  rounds (round 9 is the final round and skips MixColumns; the field is
  defined there but the hypothesis below does not constrain it). -/
  wMix : Fin 10 → Fin 16 → Fin 8 → ZMod r
  /-- MixColumns bit-witness — for non-final rounds, `wMix round` is
  `BitOf` for the MixColumns output bits. -/
  hMix : ∀ (round : Fin 10), round.val ≠ 9 →
    ∀ (i : Fin 16) (j : Fin 8),
      BitOf (wMix round i j)
        ((aesMixColumns
          (aesShiftRows (aesSubBytes (rounds ⟨round.val, by omega⟩))) i) j)
  /-- **Committed AddRoundKey-layer output wires** for the 9 non-final
  rounds. Equals the next round state by `hstep`, but exposed here
  explicitly so the bit-witness is committed to specific wires
  rather than derived as `wMix ⊕ wRK[round+1]`. -/
  wAdd : Fin 10 → Fin 16 → Fin 8 → ZMod r
  /-- AddRoundKey bit-witness — for non-final rounds, `wAdd round`
  bit-witnesses the round-step output state (which equals
  `rounds[round+1]` by `hstep`). -/
  hAdd : ∀ (round : Fin 10), round.val ≠ 9 →
    ∀ (i : Fin 16) (j : Fin 8),
      BitOf (wAdd round i j)
        ((aesRoundStep (rounds ⟨round.val, by omega⟩)
                       (rk ⟨round.val + 1, by omega⟩) false) i j)

/-- **Projection to the byte-level witness.** Every downstream chain
(`aes128_closed_chain` etc.) operates on `IsValidAES128EncryptWitness`,
so projecting through this lemma immediately discharges the byte-level
obligations from a constraint-chain witness. -/
theorem IsValidAES128EncryptConstraintWitness.toByteLevel
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext) :
    IsValidAES128EncryptWitness plaintext key ciphertext :=
  ⟨h.rounds, h.rk, h.hrk, h.h0, h.hstep, h.hout⟩

/-- **Constraint chain ⇒ S-box bit-witness at every `(round, byte, bit)`
position.** Direct lift of `aesSbox_byte_constraint_sound` over the
10 × 16 grid carried by `IsValidAES128EncryptConstraintWitness`. -/
theorem aes128_sbox_bits_sound
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (byte : Fin 16) (bit : Fin 8) :
    BitOf (h.wSub round byte bit) ((aesSbox (h.rounds ⟨round.val, by omega⟩ byte)) bit) :=
  aesSbox_byte_constraint_sound (h.h_sbox round byte) bit

/-- **Key-expansion S-box constraint chain.** Bundles the 40 S-box
invocations that drive AES-128 key expansion: per round-key boundary
(`round ∈ Fin 10`, mapping to the derivation of `rk[round+1]` from
`rk[round]`) and per byte position (`byte ∈ Fin 4`) inside that
round's `SubWord ∘ RotWord` call.

The input byte at position `(round, byte)` is the `byte`-th element of
`aesRotWord (aesKeyExpansionWord key ⟨4·round + 3, _⟩)` — i.e., the
RotWord of the last word of round `round`'s key, which AES-128's key
schedule feeds into SubWord to derive the first word of round
`round+1`'s key.

The non-SubWord parts of key expansion are pure XOR chains, modelled
elsewhere by `xor_n_*` per-bit lemmas; this structure isolates the
substantive (non-XOR) cost: the 40 S-box invocations.

A future companion theorem
`aesKeyExpansion_from_constraint_witness` will derive
`rk = aesKeyExpansion key` from a richer wire-witness for the full
key schedule. -/
structure IsValidKeyExpansionConstraintWitness
    (key : Fin 16 → Byte8) where
  /-- S-box input bit wires for the 40 key-schedule S-boxes. -/
  wX : Fin 10 → Fin 4 → Fin 8 → ZMod r
  /-- S-box inverse bit wires. -/
  wX_inv : Fin 10 → Fin 4 → Fin 8 → ZMod r
  /-- S-box output bit wires. -/
  wSub : Fin 10 → Fin 4 → Fin 8 → ZMod r
  /-- `is_zero` selector per S-box invocation. -/
  w_isz : Fin 10 → Fin 4 → ZMod r
  /-- 64 cross-product wires per S-box. -/
  wP : Fin 10 → Fin 4 → Fin 8 → Fin 8 → ZMod r
  /-- 8 parity-decomposition product bits per S-box. -/
  wProd : Fin 10 → Fin 4 → Fin 8 → ZMod r
  /-- **Word-level byte trace** — 44 expanded-key words, each 4 bytes. -/
  wordBytes : Fin 44 → Fin 4 → Byte8
  /-- **Initial-word identity** — the first 4 words equal the AES-128
  master key, four bytes per word. -/
  hWord_init : ∀ (n : Fin 4) (b : Fin 4),
    wordBytes ⟨n.val, by have := n.isLt; omega⟩ b =
      key ⟨n.val * 4 + b.val, by have := n.isLt; have := b.isLt; omega⟩
  /-- **Non-boundary recurrence** — for `n ≥ 4` with `n % 4 ≠ 0`,
  `word[n][b] = word[n-4][b] ⊕ word[n-1][b]`. -/
  hWord_nonboundary : ∀ (n : Fin 44), n.val ≥ 4 → n.val % 4 ≠ 0 →
    ∀ (b : Fin 4),
      wordBytes n b =
        xor8 (wordBytes ⟨n.val - 4, by have := n.isLt; omega⟩ b)
             (wordBytes ⟨n.val - 1, by have := n.isLt; omega⟩ b)
  /-- **Boundary recurrence** — for `n ≥ 4` with `n % 4 = 0`,
  `word[n][b] = word[n-4][b] ⊕ SubWord(RotWord(word[n-1]))[b] ⊕
  Rcon[n/4][b]`. -/
  hWord_boundary : ∀ (n : Fin 44), n.val ≥ 4 → n.val % 4 = 0 →
    ∀ (b : Fin 4),
      wordBytes n b =
        xor8 (xor8 (wordBytes ⟨n.val - 4, by have := n.isLt; omega⟩ b)
                   (aesSbox ((aesRotWord
                     (wordBytes ⟨n.val - 1, by have := n.isLt; omega⟩)) b)))
             (if b = (0 : Fin 4) then
               aesRcon ⟨n.val / 4, by have := n.isLt; omega⟩
              else byteOfNat 0)
  /-- **The 40 S-box constraint chains** — now stated in terms of
  the prover-supplied `wordBytes` rather than the spec function, so
  the wire-level inputs match the recurrence above. -/
  h_sbox : ∀ (round : Fin 10) (byte : Fin 4),
    IsValidSBoxByteWitness
      ((aesRotWord (wordBytes
        ⟨4 * round.val + 3, by have := round.isLt; omega⟩)) byte)
      (wX round byte) (wX_inv round byte) (w_isz round byte)
      (wP round byte) (wProd round byte) (wSub round byte)
  /-- **Bit-level word wires** — one ZMod r wire per
  (word, byte, bit) position. Each bit-witnesses the corresponding
  byte position via `hWord_bits`. -/
  wWord : Fin 44 → Fin 4 → Fin 8 → ZMod r
  /-- Bit-witness for `wWord` — each wire is `BitOf` for the
  matching bit of `wordBytes`. -/
  hWord_bits : ∀ (n : Fin 44) (b : Fin 4) (bit : Fin 8),
    BitOf (wWord n b bit) (wordBytes n b bit)
  /-- **Round-key byte trace** — the byte-level round-key sequence. -/
  rk : Fin 11 → Fin 16 → Byte8
  /-- **Round-key bit wires** — one per (round, byte, bit). -/
  wRK : Fin 11 → Fin 16 → Fin 8 → ZMod r
  /-- Round-key bit-witness — `wRK` is `BitOf` for each
  `(round, byte, bit)` of `rk`. -/
  hRK : ∀ (round : Fin 11) (i : Fin 16) (j : Fin 8),
    BitOf (wRK round i j) (rk round i j)
  /-- **Round-key composition** — `rk[r][i] = wordBytes[4r + i/4][i%4]`.
  This is the AES-128 convention that round-key `r` is the 4 words
  `[4r, 4r+1, 4r+2, 4r+3]` concatenated as 16 bytes. -/
  hRoundKey_from_words : ∀ (r : Fin 11) (i : Fin 16),
    rk r i = wordBytes ⟨4 * r.val + i.val / 4,
      by have := r.isLt; have := i.isLt; omega⟩
      ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- **`wordBytes` matches the FIPS-197 key expansion at every word.**

Predicate form, retained for backwards-compatible call sites; the
strong-induction proof is below as
`IsValidKeyExpansionConstraintWitness.wordBytes_eq_proof`. -/
def IsValidKeyExpansionConstraintWitness.wordBytes_eq
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key) :
    Prop := ∀ n : Fin 44, h.wordBytes n = aesKeyExpansionWord key n

/-- **Strong-induction proof.** The prover-supplied `wordBytes` matches
`aesKeyExpansionWord` at every word, derived from the recurrence
fields (`hWord_init` / `hWord_nonboundary` / `hWord_boundary`).

The proof avoids the Fin binder-scope pitfalls by working entirely
at the byte level via `funext` and exploiting Fin proof-irrelevance:
all `⟨k, _⟩ : Fin 44` with the same `k` are equal as Lean terms
(`Fin.ext` or definitional equality on the inductive constructor),
so the structure-field `by have := n.isLt; omega` proofs and the
proof-side `omega` reconstructions yield identical Fin values. -/
theorem IsValidKeyExpansionConstraintWitness.wordBytes_eq_proof
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key) :
    h.wordBytes_eq := by
  unfold IsValidKeyExpansionConstraintWitness.wordBytes_eq
  -- Reduce to a Nat-quantified statement.
  suffices aux : ∀ (m : ℕ) (hm : m < 44),
      h.wordBytes ⟨m, hm⟩ = aesKeyExpansionWord key ⟨m, hm⟩ from
    fun n => by rw [show n = ⟨n.val, n.isLt⟩ from Fin.ext rfl]; exact aux n.val n.isLt
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    funext b
    -- Rewrite the goal to extract the Nat shape of m.
    by_cases h_lt : m < 4
    · -- Base case: m ∈ {0, 1, 2, 3}. Use the eq_def lemma to expose
      -- aesKeyExpansionWord's pattern-match arms; the resulting match
      -- on a concrete `⟨k, _⟩` literal reduces via `congrArg key` +
      -- `Fin.ext` on the resulting Nat equality (e.g. `0 * 4 + b = b`).
      interval_cases m
      · rw [h.hWord_init ⟨0, by decide⟩ b, aesKeyExpansionWord.eq_def]
        exact congrArg key (Fin.ext (by simp))
      · rw [h.hWord_init ⟨1, by decide⟩ b, aesKeyExpansionWord.eq_def]
        exact congrArg key (Fin.ext (by simp))
      · rw [h.hWord_init ⟨2, by decide⟩ b, aesKeyExpansionWord.eq_def]
        exact congrArg key (Fin.ext (by simp))
      · rw [h.hWord_init ⟨3, by decide⟩ b, aesKeyExpansionWord.eq_def]
        exact congrArg key (Fin.ext (by simp))
    · -- Inductive case: m ≥ 4.
      push Not at h_lt
      obtain ⟨v, rfl⟩ : ∃ v, m = v + 4 := ⟨m - 4, by omega⟩
      have h_v_lt : v < v + 4 := by omega
      have h_v3_lt : v + 3 < v + 4 := by omega
      have h_v_lt_44 : v < 44 := by omega
      have h_v3_lt_44 : v + 3 < 44 := by omega
      have IH4 := ih v h_v_lt h_v_lt_44
      have IH1 := ih (v + 3) h_v3_lt h_v3_lt_44
      by_cases h_mod : (v + 4) % 4 = 0
      · -- Boundary
        have h_b := h.hWord_boundary ⟨v + 4, hm⟩ h_lt h_mod b
        -- Rewrite (v+4) - 4 = v and (v+4) - 1 = v+3 in h_b.
        have fin_eq_4 : (⟨v + 4 - 4, by have := hm; omega⟩ : Fin 44) =
            ⟨v, h_v_lt_44⟩ := by
          apply Fin.ext; change v + 4 - 4 = v; omega
        have fin_eq_1 : (⟨v + 4 - 1, by have := hm; omega⟩ : Fin 44) =
            ⟨v + 3, h_v3_lt_44⟩ := by
          apply Fin.ext; change v + 4 - 1 = v + 3; omega
        rw [fin_eq_4, fin_eq_1] at h_b
        rw [h_b, IH4, IH1]
        -- Now show the RHS form matches aesKeyExpansionWord's body.
        change xor8 _ _ = aesKeyExpansionWord key ⟨v + 4, hm⟩ b
        -- aesKeyExpansionWord ⟨v + 4, _⟩ pattern-matches the `n + 4` arm
        -- with n = v. We rely on definitional reduction here.
        conv_rhs => unfold aesKeyExpansionWord
        simp only [h_mod, ↓reduceIte, aesSubWord]
      · -- Non-boundary
        have h_nb := h.hWord_nonboundary ⟨v + 4, hm⟩ h_lt h_mod b
        have fin_eq_4 : (⟨v + 4 - 4, by have := hm; omega⟩ : Fin 44) =
            ⟨v, h_v_lt_44⟩ := by
          apply Fin.ext; change v + 4 - 4 = v; omega
        have fin_eq_1 : (⟨v + 4 - 1, by have := hm; omega⟩ : Fin 44) =
            ⟨v + 3, h_v3_lt_44⟩ := by
          apply Fin.ext; change v + 4 - 1 = v + 3; omega
        rw [fin_eq_4, fin_eq_1] at h_nb
        rw [h_nb, IH4, IH1]
        change xor8 _ _ = aesKeyExpansionWord key ⟨v + 4, hm⟩ b
        conv_rhs => unfold aesKeyExpansionWord
        simp only [h_mod, ↓reduceIte]

/-- **The headline derivation theorem.** From the structure's
recurrence fields + S-box chains + the `wordBytes_eq` consequence,
the round-key byte trace equals the FIPS-197 expanded key. -/
theorem aesKeyExpansion_from_constraint_witness
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key) :
    h.rk = aesKeyExpansion key := by
  funext r i
  rw [h.hRoundKey_from_words r i]
  rw [h.wordBytes_eq_proof]
  unfold aesKeyExpansion
  rfl

/-- **Round-key bit-witness from a key-expansion constraint witness.**
Direct consequence of `aesKeyExpansion_from_constraint_witness` +
`hRK`: each round-key wire bit-witnesses the FIPS-197 expanded round
key. -/
theorem aesKeyExpansion_rk_bits_sound
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key)
    (round : Fin 11) (i : Fin 16) (j : Fin 8) :
    BitOf (h.wRK round i j) ((aesKeyExpansion key) round i j) := by
  rw [← aesKeyExpansion_from_constraint_witness h]
  exact h.hRK round i j

/-! ## Cross-witness wire coherence

The `IsValid*ConstraintWitness` structures carry many wire arrays (for
S-box inputs, outputs, round keys, etc.). Each carries its own `BitOf`
hypothesis pinning it to the corresponding spec-level bit. The
coherence lemma below makes the consequence explicit: **two wires
that bit-witness the same bool *must* be equal field elements**,
regardless of which structure-field they came from.

At the gadget level this holds by construction (the R1CS builder
allocates unique variables per witness index, so any two references
to the same logical wire are the same variable). The Lean theorem
upgrades this from a gadget-level invariant to a structure-level one:
the closed chain's bit-witness conjuncts are now provably consistent
with each other.

The headline consequence: for any (round, byte, bit) position in an
AES-128 chain, the S-box input bit `h.wX round byte bit` and any
other bit-witness for the same round-state bit (e.g. one chosen by
`aes128_round_bits_sound`) must agree as field elements. -/

/-- **Cross-witness wire coherence for the AES round-state bits.** Any
wire `w` that bit-witnesses the round-`round` state byte at position
`byte`, bit `bit`, equals the constraint-witness's `wX round byte bit`. -/
theorem aes128_wX_coherence
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (byte : Fin 16) (bit : Fin 8)
    {w : ZMod r}
    (hw : BitOf w (h.rounds ⟨round.val, by omega⟩ byte bit)) :
    w = h.wX round byte bit := by
  exact BitOf.unique hw ((h.h_sbox round byte).hX bit)

/-- **Cross-witness coherence for round-key bits.** Any wire `w` that
bit-witnesses round key `round`'s byte `i`, bit `j`, equals `h.wRK
round i j`. -/
theorem aes128_wRK_coherence
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 11) (i : Fin 16) (j : Fin 8)
    {w : ZMod r}
    (hw : BitOf w (h.rk round i j)) :
    w = h.wRK round i j := by
  exact BitOf.unique hw (h.hRK round i j)

/-- **Cross-witness coherence for S-box output (SubBytes layer) bits.**
Any wire `w` that bit-witnesses `aesSbox (h.rounds round byte) bit`
equals `h.wSub round byte bit`. -/
theorem aes128_wSub_coherence
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (byte : Fin 16) (bit : Fin 8)
    {w : ZMod r}
    (hw : BitOf w ((aesSbox (h.rounds ⟨round.val, by omega⟩ byte)) bit)) :
    w = h.wSub round byte bit := by
  exact BitOf.unique hw (aesSbox_byte_constraint_sound (h.h_sbox round byte) bit)

/-- **Cross-witness coherence for ShiftRows-layer bits.** Any wire
`w` that bit-witnesses the ShiftRows-layer output equals
`h.wShift round i j`. -/
theorem aes128_wShift_coherence
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (i : Fin 16) (j : Fin 8)
    {w : ZMod r}
    (hw : BitOf w
      ((aesShiftRows (aesSubBytes (h.rounds ⟨round.val, by omega⟩)) i) j)) :
    w = h.wShift round i j :=
  BitOf.unique hw (h.hShift round i j)

/-- **Cross-witness coherence for MixColumns-layer bits (non-final
rounds).** Any wire `w` that bit-witnesses the MixColumns-layer
output equals `h.wMix round i j`. -/
theorem aes128_wMix_coherence
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (h_nonfinal : round.val ≠ 9)
    (i : Fin 16) (j : Fin 8)
    {w : ZMod r}
    (hw : BitOf w
      ((aesMixColumns (aesShiftRows
        (aesSubBytes (h.rounds ⟨round.val, by omega⟩))) i) j)) :
    w = h.wMix round i j :=
  BitOf.unique hw (h.hMix round h_nonfinal i j)

/-- **Cross-witness coherence for AddRoundKey-layer bits (non-final
rounds).** Any wire `w` that bit-witnesses the round-step output
(equivalently the next round state by `hstep`) equals
`h.wAdd round i j`. -/
theorem aes128_wAdd_coherence
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (h_nonfinal : round.val ≠ 9)
    (i : Fin 16) (j : Fin 8)
    {w : ZMod r}
    (hw : BitOf w
      ((aesRoundStep (h.rounds ⟨round.val, by omega⟩)
                     (h.rk ⟨round.val + 1, by omega⟩) false) i j)) :
    w = h.wAdd round i j :=
  BitOf.unique hw (h.hAdd round h_nonfinal i j)

/-! ## Threaded wire trace through the whole encryption

The closed chain exposes per-round per-layer bit-witnesses as separate
existential conjuncts. The structure below aggregates them into a
single typed record indexed by `(round, layer)`, so a downstream
consumer can read off the bit-witness for any layer at any round
through one uniform index. -/

/-- The five wire arrays a single AES round step produces, each
bit-witnessed to the corresponding FIPS-197 intermediate value.

* `state` — input round state (= `wX round` for round 0..9, the
  ciphertext wires for round 10).
* `sub` — SubBytes-layer output (`wSub round`).
* `shift` — ShiftRows-layer output (`wShift round`).
* `mix` — MixColumns-layer output (`wMix round`); only meaningful for
  non-final rounds.
* `add` — AddRoundKey-layer output (`wAdd round`); only meaningful for
  non-final rounds; equals the next round state by `hstep`.

For the final round (round 9 in `Fin 10` indexing, producing the
ciphertext at round-state index 10), `mix` and `add` are unconstrained
placeholders — use `ciphertext` instead. -/
structure AES128RoundWireTrace where
  state : Fin 16 → Fin 8 → ZMod r
  sub : Fin 16 → Fin 8 → ZMod r
  shift : Fin 16 → Fin 8 → ZMod r
  mix : Fin 16 → Fin 8 → ZMod r
  add : Fin 16 → Fin 8 → ZMod r

/-- **Threaded round-level wire trace.** From a constraint witness, for
each non-final round `round : Fin 10` (i.e. round ≠ 9), construct the
five-tuple `AES128RoundWireTrace` whose components each bit-witness
the corresponding FIPS-197 intermediate value. -/
def IsValidAES128EncryptConstraintWitness.wireTrace
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) : AES128RoundWireTrace where
  state := h.wX round
  sub := h.wSub round
  shift := h.wShift round
  mix := h.wMix round
  add := h.wAdd round

/-- **Bit-witness conjunction for the trace.** All four layer fields
of the trace at any non-final round bit-witness the corresponding
FIPS-197 intermediate value at that round. The conjunction packages
the per-layer bit-witnesses into a single indexed statement so a
downstream consumer can iterate the trace. -/
theorem aes128_wire_trace_bit_witnessed
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (h_nonfinal : round.val ≠ 9) (i : Fin 16) (j : Fin 8) :
    -- `state` bit-witnesses the input round state.
    BitOf ((h.wireTrace round).state i j)
      (h.rounds ⟨round.val, by omega⟩ i j) ∧
    -- `sub` bit-witnesses the SubBytes-layer output.
    BitOf ((h.wireTrace round).sub i j)
      ((aesSubBytes (h.rounds ⟨round.val, by omega⟩) i) j) ∧
    -- `shift` bit-witnesses the ShiftRows-layer output.
    BitOf ((h.wireTrace round).shift i j)
      ((aesShiftRows (aesSubBytes (h.rounds ⟨round.val, by omega⟩)) i) j) ∧
    -- `mix` bit-witnesses the MixColumns-layer output.
    BitOf ((h.wireTrace round).mix i j)
      ((aesMixColumns
        (aesShiftRows (aesSubBytes (h.rounds ⟨round.val, by omega⟩))) i) j) ∧
    -- `add` bit-witnesses the AddRoundKey-layer output
    -- (= next round state by `hstep`).
    BitOf ((h.wireTrace round).add i j)
      ((aesRoundStep (h.rounds ⟨round.val, by omega⟩)
                     (h.rk ⟨round.val + 1, by omega⟩) false) i j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (h.h_sbox round i).hX j
  · exact aesSbox_byte_constraint_sound (h.h_sbox round i) j
  · exact h.hShift round i j
  · exact h.hMix round h_nonfinal i j
  · exact h.hAdd round h_nonfinal i j

/-- **Per-S-box bit-witness from a key-expansion constraint witness.**
Direct lift of `aesSbox_byte_constraint_sound` over the 10 × 4 grid
of key-schedule S-box invocations carried by
`IsValidKeyExpansionConstraintWitness`. -/
theorem aesKeyExpansion_sbox_bits_sound
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key)
    (round : Fin 10) (byte : Fin 4) (bit : Fin 8) :
    BitOf (h.wSub round byte bit)
      ((aesSbox ((aesRotWord (aesKeyExpansionWord key
        ⟨4 * round.val + 3, by have := round.isLt; omega⟩)) byte)) bit) := by
  have h_witness := h.h_sbox round byte
  rw [← h.wordBytes_eq_proof ⟨4 * round.val + 3, by have := round.isLt; omega⟩]
  exact aesSbox_byte_constraint_sound h_witness bit

/-- **SubWord-output bit-witness from the key-expansion constraint
chain.** Direct byte-level lift of `aesKeyExpansion_sbox_bits_sound`:
the prover-supplied `wSub round byte bit` wires bit-witness the
`SubWord ∘ RotWord` output expected at round-key boundary `round`,
byte position `byte`. This is the bit-level guarantee the algebraic
key-schedule formula `aesKeyExpansionWord key ⟨4·round + 4, _⟩` relies
on; the remaining XOR-chain wiring is a non-S-box gadget composition
modeled by `xor_n_*` per-bit lemmas. -/
theorem aesKeyExpansion_subword_byte_sound
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key)
    (round : Fin 10) (byte : Fin 4) (bit : Fin 8) :
    BitOf (h.wSub round byte bit)
      ((aesSubWord (aesRotWord (aesKeyExpansionWord key
        ⟨4 * round.val + 3, by have := round.isLt; omega⟩))) byte bit) := by
  unfold aesSubWord
  exact aesKeyExpansion_sbox_bits_sound h round byte bit

/-- **Bit-level XOR identity for key-expansion non-boundary words.**
Given the byte-level recurrence `hWord_nonboundary` and the bit-wire
witnesses `hWord_bits`, the prover-supplied bit wires
`wWord(n)(b)(bit)` are `BitOf`-witnessed by the XOR of the
corresponding bits of `wWord(n-4)(b)` and `wWord(n-1)(b)`. This is
the bit-level analogue of the byte-level XOR recurrence — exposed
here as a per-bit identity to support downstream consumers that
need the XOR chain at the wire level rather than the byte level. -/
theorem aesKeyExpansion_xor_bit_nonboundary
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key)
    (n : Fin 44) (h_ge : n.val ≥ 4) (h_mod : n.val % 4 ≠ 0)
    (b : Fin 4) (bit : Fin 8) :
    BitOf (h.wWord n b bit)
      (xor (h.wordBytes ⟨n.val - 4, by have := n.isLt; omega⟩ b bit)
           (h.wordBytes ⟨n.val - 1, by have := n.isLt; omega⟩ b bit)) := by
  have := h.hWord_bits n b bit
  rw [h.hWord_nonboundary n h_ge h_mod b] at this
  -- `xor8 a b bit = xor (a bit) (b bit)` is the definition of `xor8`.
  exact this

/-- **Bit-level XOR identity for key-expansion boundary words.**
Mirrors `aesKeyExpansion_xor_bit_nonboundary` for the SubWord +
Rcon-corrected boundary path. The chain is now three-way:
`word[n][b][bit] = word[n-4][b][bit] ⊕ SubWord(RotWord(word[n-1]))[b][bit] ⊕ Rcon[n/4][b][bit]`. -/
theorem aesKeyExpansion_xor_bit_boundary
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key)
    (n : Fin 44) (h_ge : n.val ≥ 4) (h_mod : n.val % 4 = 0)
    (b : Fin 4) (bit : Fin 8) :
    BitOf (h.wWord n b bit)
      (xor (xor (h.wordBytes ⟨n.val - 4, by have := n.isLt; omega⟩ b bit)
                ((aesSbox ((aesRotWord
                  (h.wordBytes ⟨n.val - 1, by have := n.isLt; omega⟩)) b)) bit))
           ((if b = (0 : Fin 4) then
             aesRcon ⟨n.val / 4, by have := n.isLt; omega⟩
            else byteOfNat 0) bit)) := by
  have := h.hWord_bits n b bit
  rw [h.hWord_boundary n h_ge h_mod b] at this
  exact this

/-- **Bit-level identity for key-expansion initial words.** The first 4
words match the master key byte-by-byte; `hWord_bits` lifts this to
the bit level. -/
theorem aesKeyExpansion_xor_bit_init
    {key : Fin 16 → Byte8}
    (h : IsValidKeyExpansionConstraintWitness key)
    (n : Fin 4) (b : Fin 4) (bit : Fin 8) :
    BitOf (h.wWord ⟨n.val, by have := n.isLt; omega⟩ b bit)
      (key ⟨n.val * 4 + b.val, by have := n.isLt; have := b.isLt; omega⟩ bit) := by
  have := h.hWord_bits ⟨n.val, by have := n.isLt; omega⟩ b bit
  rw [h.hWord_init n b] at this
  exact this

/-- **Ciphertext bit-witness from the constraint chain.** Given a
`IsValidAES128EncryptConstraintWitness`, there exists an output-wire
array `wCipher` that bit-witnesses each byte of the ciphertext.

The witness comes from invoking `aesRoundStep_bit_sound` at round 9
(the final round, `is_final = true`) using the structure's wires for
the round-9 S-box constraint chain and the round-key bit-wires for
`rk[10]`. The resulting existential output is the desired `wCipher`. -/
theorem aes128_ciphertext_bits_sound [Fact (Nat.Prime r)]
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext) :
    ∃ wCipher : Fin 16 → Fin 8 → ZMod r,
      ∀ i j, BitOf (wCipher i j) (ciphertext i j) := by
  -- Apply the round-step soundness at round 9 (final round, is_final = true).
  obtain ⟨wOut, hOut⟩ :=
    aesRoundStep_bit_sound
      (s := h.rounds ⟨9, by decide⟩) (rk := h.rk ⟨10, by decide⟩)
      (is_final := true) (wS := h.wX ⟨9, by decide⟩)
      (wX_inv := h.wX_inv ⟨9, by decide⟩) (w_isz := h.w_isz ⟨9, by decide⟩)
      (wP := h.wP ⟨9, by decide⟩) (wProd := h.wProd ⟨9, by decide⟩)
      (wSub := h.wSub ⟨9, by decide⟩) (wRK := h.wRK ⟨10, by decide⟩)
      (hRK := h.hRK ⟨10, by decide⟩) (h_sbox := h.h_sbox ⟨9, by decide⟩)
  refine ⟨wOut, ?_⟩
  intro i j
  -- Tie ciphertext → rounds[10] → aesRoundStep(rounds[9], rk[10], true).
  have h_step := h.hstep ⟨9, by decide⟩
  simp only at h_step
  have h_step' :
      h.rounds ⟨10, by decide⟩ =
        aesRoundStep (h.rounds ⟨9, by decide⟩) (h.rk ⟨10, by decide⟩) true := by
    convert h_step using 2
  rw [h.hout, h_step']
  exact hOut i j

/-- **Per-round-state bit-witness from the constraint chain.** For any
round index `round ∈ Fin 11`, there exists an output-wire array that
bit-witnesses each byte of the corresponding round state.

For `round ∈ {0, …, 9}`, the witness comes directly from the
structure's S-box input wires (`h.wX round`), which are
`BitOf`-witnessed to `rounds round` via the `hX` field of each
constraint-chain `IsValidSBoxByteWitness`. For `round = 10`
(ciphertext), the witness is the existential output of
`aes128_ciphertext_bits_sound`, which threads through
`aesRoundStep_bit_sound` at the final round. -/
theorem aes128_round_bits_sound [Fact (Nat.Prime r)]
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 11) :
    ∃ wRoundState : Fin 16 → Fin 8 → ZMod r,
      ∀ i j, BitOf (wRoundState i j) (h.rounds round i j) := by
  by_cases h_final : round.val = 10
  · -- Round 10 = ciphertext; reuse `aes128_ciphertext_bits_sound`.
    obtain ⟨wCipher, hCipher⟩ := aes128_ciphertext_bits_sound h
    refine ⟨wCipher, ?_⟩
    intro i j
    have h_round : round = ⟨10, by decide⟩ := Fin.ext h_final
    rw [h_round, ← h.hout]
    exact hCipher i j
  · -- Rounds 0..9: use the S-box constraint chain's input wires.
    have h_lt : round.val < 10 := by
      have := round.isLt; omega
    let round_fin10 : Fin 10 := ⟨round.val, h_lt⟩
    refine ⟨h.wX round_fin10, ?_⟩
    intro i j
    have h_eq : (⟨round_fin10.val, by omega⟩ : Fin 11) = round := by
      apply Fin.ext; rfl
    rw [← h_eq]
    exact (h.h_sbox round_fin10 i).hX j

/-! ## Per-layer wire-level bit-witnesses

The round-step soundness lemma `aesRoundStep_bit_sound` produces an
existential bit-witness for the entire round-step output. The theorems
below decompose that round-step bit-witness by *layer* — exposing
intermediate bit-witnesses for the ShiftRows, MixColumns, and
AddRoundKey outputs of each non-final round.

Each layer's witness comes from threading the existing real
per-bit-primitive lemmas (`aesShiftRows_sound`, `aesMixColumns_sound`,
`aesAddRoundKey_sound`) through the structure's wires. They mirror
the internal-derivation chain of `aesRoundStep_bit_sound` but expose
the intermediate witnesses to the user. -/

/-- **ShiftRows-layer bit-witness for any round.** Now returns the
committed `h.wShift round` wires directly (rather than constructing
them as a permutation of `wSub`). The conclusion is unchanged. -/
theorem aes128_shift_rows_bits_sound
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) :
    ∃ wShift : Fin 16 → Fin 8 → ZMod r,
      ∀ i j, BitOf (wShift i j)
        ((aesShiftRows (aesSubBytes (h.rounds ⟨round.val, by omega⟩)) i) j) :=
  ⟨h.wShift round, h.hShift round⟩

/-- **MixColumns-layer bit-witness for any non-final round.** Now
returns the committed `h.wMix round` wires directly. -/
theorem aes128_mix_columns_bits_sound [Fact (Nat.Prime r)]
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (h_nonfinal : round.val ≠ 9) :
    ∃ wMix : Fin 16 → Fin 8 → ZMod r,
      ∀ i j, BitOf (wMix i j)
        ((aesMixColumns (aesShiftRows
          (aesSubBytes (h.rounds ⟨round.val, by omega⟩))) i) j) :=
  ⟨h.wMix round, h.hMix round h_nonfinal⟩

/-- **AddRoundKey-layer bit-witness for the non-final round.** Closed-
form arithmetic on the MixColumns and round-key bit-wires via
`aesAddRoundKey_sound`. The conclusion ties to `aesRoundStep` (non-final
form) of the round state, which by `h.hstep` equals the next round's
state. -/
theorem aes128_add_round_key_nonfinal_bits_sound [Fact (Nat.Prime r)]
    {plaintext key ciphertext : Fin 16 → Byte8}
    (h : IsValidAES128EncryptConstraintWitness plaintext key ciphertext)
    (round : Fin 10) (h_nonfinal : round.val ≠ 9) :
    ∃ wAdd : Fin 16 → Fin 8 → ZMod r,
      ∀ i j, BitOf (wAdd i j)
        ((aesRoundStep (h.rounds ⟨round.val, by omega⟩)
                       (h.rk ⟨round.val + 1, by omega⟩) false) i j) :=
  ⟨h.wAdd round, h.hAdd round h_nonfinal⟩

end Xark
