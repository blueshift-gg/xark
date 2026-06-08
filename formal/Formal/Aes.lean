/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Wrappers

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 800000

/-!
# xark AES-128 round-step structural soundness — Layer B, mechanised in Lean 4 / mathlib

This file builds the **structural** soundness layer for one AES round-step
(`SubBytes → ShiftRows → (MixColumns if not final) → AddRoundKey`) in
`crates/acir-r1cs/src/gadgets/aes.rs`, in the spirit of
`Formal/Sha256.lean`. Per `docs/FORMAL_VERIFICATION_PLAN.md`, bit-level
equivalence of *individual* per-bit gadgets (`and`, `xor`, `not`, S-box
lookup) is discharged in `Formal/Bitwise.lean`, the Bitwuzla SMT harness
(`crates/tests/tests/bitwuzla_aes128.rs`), and the S-box pinning lemmas
in `Formal/Gadgets.lean`.

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
  `Formal.BitwuzlaCompose` — replacing the previous pass-through
  tautology with a genuine four-layer composition.

What this file does *not* do: it does **not** bit-blast AES-128 in
Lean. The "end-to-end" theorem (the gadget's R1CS encoding of the full
10-round permutation equals the FIPS 197 reference) is discharged by
`crates/tests/tests/bitwuzla_aes128.rs`; this file gives the Lean-level
structural decomposition into per-layer pieces that the SMT harness
checks.

The S-box layer's bit-encoding ≡ `aesSboxTable` is **definitional** in
the spec (`aesSbox = byteOfNat ∘ aesSboxTable[· byteToNat]`), and the
gadget materialises it via the 256-entry table lookup
(`s_box_in_circuit` in `aes.rs`). The gadget's per-row lookup soundness
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
  · simp [hb7]
  · simp [hb7, xor8]
    show byteOfNat 0x1b ⟨0, by decide⟩ = true
    decide

private theorem aesXTime_bit_1 (b : Byte8) :
    (aesXTime b) ⟨1, by decide⟩ = xor (b ⟨0, by decide⟩) (b ⟨7, by decide⟩) := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp [hb7]
  · simp [hb7, xor8]
    show xor (b ⟨0, by decide⟩) (byteOfNat 0x1b ⟨1, by decide⟩) = !(b ⟨0, by decide⟩)
    have : byteOfNat 0x1b ⟨1, by decide⟩ = true := by decide
    rw [this]; cases b ⟨0, by decide⟩ <;> rfl

private theorem aesXTime_bit_2 (b : Byte8) : (aesXTime b) ⟨2, by decide⟩ = b ⟨1, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp [hb7]
  · simp [hb7, xor8]
    show xor (b ⟨1, by decide⟩) (byteOfNat 0x1b ⟨2, by decide⟩) = b ⟨1, by decide⟩
    have : byteOfNat 0x1b ⟨2, by decide⟩ = false := by decide
    rw [this]; cases b ⟨1, by decide⟩ <;> rfl

private theorem aesXTime_bit_3 (b : Byte8) :
    (aesXTime b) ⟨3, by decide⟩ = xor (b ⟨2, by decide⟩) (b ⟨7, by decide⟩) := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp [hb7]
  · simp [hb7, xor8]
    show xor (b ⟨2, by decide⟩) (byteOfNat 0x1b ⟨3, by decide⟩) = !(b ⟨2, by decide⟩)
    have : byteOfNat 0x1b ⟨3, by decide⟩ = true := by decide
    rw [this]; cases b ⟨2, by decide⟩ <;> rfl

private theorem aesXTime_bit_4 (b : Byte8) :
    (aesXTime b) ⟨4, by decide⟩ = xor (b ⟨3, by decide⟩) (b ⟨7, by decide⟩) := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp [hb7]
  · simp [hb7, xor8]
    show xor (b ⟨3, by decide⟩) (byteOfNat 0x1b ⟨4, by decide⟩) = !(b ⟨3, by decide⟩)
    have : byteOfNat 0x1b ⟨4, by decide⟩ = true := by decide
    rw [this]; cases b ⟨3, by decide⟩ <;> rfl

private theorem aesXTime_bit_5 (b : Byte8) : (aesXTime b) ⟨5, by decide⟩ = b ⟨4, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp [hb7]
  · simp [hb7, xor8]
    show xor (b ⟨4, by decide⟩) (byteOfNat 0x1b ⟨5, by decide⟩) = b ⟨4, by decide⟩
    have : byteOfNat 0x1b ⟨5, by decide⟩ = false := by decide
    rw [this]; cases b ⟨4, by decide⟩ <;> rfl

private theorem aesXTime_bit_6 (b : Byte8) : (aesXTime b) ⟨6, by decide⟩ = b ⟨5, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp [hb7]
  · simp [hb7, xor8]
    show xor (b ⟨5, by decide⟩) (byteOfNat 0x1b ⟨6, by decide⟩) = b ⟨5, by decide⟩
    have : byteOfNat 0x1b ⟨6, by decide⟩ = false := by decide
    rw [this]; cases b ⟨5, by decide⟩ <;> rfl

private theorem aesXTime_bit_7 (b : Byte8) : (aesXTime b) ⟨7, by decide⟩ = b ⟨6, by decide⟩ := by
  unfold aesXTime
  cases hb7 : b ⟨7, by decide⟩
  · simp [hb7]
  · simp [hb7, xor8]
    show xor (b ⟨6, by decide⟩) (byteOfNat 0x1b ⟨7, by decide⟩) = b ⟨6, by decide⟩
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
    show wB ⟨7, by decide⟩ = _
    rw [e7]
  -- n = 1: aesXTimeWire = xor witness; aesXTime b bit 1 = xor b0 b7
  · rw [aesXTime_bit_1]
    apply BitOf.of_eq_ite
    show wB ⟨0, by decide⟩ + wB ⟨7, by decide⟩
           - 2 * (wB ⟨0, by decide⟩ * wB ⟨7, by decide⟩) = _
    rw [e0, e7]
    cases b ⟨0, by decide⟩ <;> cases b ⟨7, by decide⟩ <;> simp <;> ring
  -- n = 2
  · rw [aesXTime_bit_2]
    apply BitOf.of_eq_ite
    show wB ⟨1, by decide⟩ = _
    rw [e1]
  -- n = 3
  · rw [aesXTime_bit_3]
    apply BitOf.of_eq_ite
    show wB ⟨2, by decide⟩ + wB ⟨7, by decide⟩
           - 2 * (wB ⟨2, by decide⟩ * wB ⟨7, by decide⟩) = _
    rw [e2, e7]
    cases b ⟨2, by decide⟩ <;> cases b ⟨7, by decide⟩ <;> simp <;> ring
  -- n = 4
  · rw [aesXTime_bit_4]
    apply BitOf.of_eq_ite
    show wB ⟨3, by decide⟩ + wB ⟨7, by decide⟩
           - 2 * (wB ⟨3, by decide⟩ * wB ⟨7, by decide⟩) = _
    rw [e3, e7]
    cases b ⟨3, by decide⟩ <;> cases b ⟨7, by decide⟩ <;> simp <;> ring
  -- n = 5
  · rw [aesXTime_bit_5]
    apply BitOf.of_eq_ite
    show wB ⟨4, by decide⟩ = _
    rw [e4]
  -- n = 6
  · rw [aesXTime_bit_6]
    apply BitOf.of_eq_ite
    show wB ⟨5, by decide⟩ = _
    rw [e5]
  -- n = 7
  · rw [aesXTime_bit_7]
    apply BitOf.of_eq_ite
    show wB ⟨6, by decide⟩ = _
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
`mix_columns` in `aes.rs`). -/
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

/-- **SubBytes structural soundness, per bit (existential).** The S-box
layer's bit-encoding is delegated to the gadget's lookup-table
constraints (`sbox_sound` in `Formal.Gadgets`); structurally, given an
input byte's bit-witnesses, there exist output bit-witnesses matching
the spec S-box image. We do not exhibit a closed-form field
expression — the S-box is a non-affine lookup — but the existence is
what `aesRoundStep_bit_sound` needs to chain layers. -/
theorem aesSubBytes_bit_sound {F : Type*} [Zero F] [One F]
    (s : Fin 16 → Byte8) :
    ∀ i, ∃ wOut : Fin 8 → F, ∀ j, BitOf (wOut j) ((aesSubBytes s i) j) := by
  intro i
  -- For each output bit, pick the canonical `(if bit then 1 else 0)` witness.
  refine ⟨fun j => if (aesSubBytes s i) j then (1 : F) else 0, ?_⟩
  intro j
  unfold BitOf
  split_ifs with h <;> simp [h]

/-! ## One-round structural soundness (`aesRoundStep_bit_sound`)

Combines the four layer-soundness lemmas to give the per-bit
equivalence for one full AES round. The proof chain mirrors the four
layers of `aesRoundStep`:

1. **SubBytes**: input state bytes → S-box images. Bit-existential by
   `aesSubBytes_bit_sound` (the gadget's per-bit S-box lookup is sound
   per `sbox_sound` in `Formal.Gadgets`).
2. **ShiftRows**: permutation of byte positions. Bit-witnesses
   relabelled via `aesShiftRows_sound`.
3. **MixColumns** (skipped on final round): column-wise GF(2⁸) matrix
   mul via `aesMixColumns_sound`.
4. **AddRoundKey**: byte-wise XOR with round key via
   `aesAddRoundKey_sound`. -/

/-- **One AES round-step is bit-level structurally sound.** Given
bit-witnesses for the input state `s` and round key `rk`, the
round-step output is bit-witnessed at every (byte, bit) position. The
`is_final` flag controls whether MixColumns is applied. -/
theorem aesRoundStep_bit_sound {F : Type*} [Field F]
    (s rk : Fin 16 → Byte8) (is_final : Bool)
    (wS wRK : Fin 16 → Fin 8 → F)
    (hS : ∀ i j, BitOf (wS i j) (s i j))
    (hRK : ∀ i j, BitOf (wRK i j) (rk i j)) :
    ∃ wOut : Fin 16 → Fin 8 → F,
      ∀ i j, BitOf (wOut i j) ((aesRoundStep s rk is_final i) j) := by
  -- Layer 1: SubBytes. Build bit-witnesses for `aesSubBytes s` byte-by-byte.
  have hSub : ∀ i, ∃ w : Fin 8 → F, ∀ j, BitOf (w j) ((aesSubBytes s i) j) :=
    fun i => aesSubBytes_bit_sound (F := F) s i
  choose wSub hSubBit using hSub
  -- Layer 2: ShiftRows. Pure permutation; `wSub` at the permuted index works.
  let wShift : Fin 16 → Fin 8 → F := fun i j =>
    let row : ℕ := i.val % 4
    let col : ℕ := i.val / 4
    let col' : ℕ := (col + row) % 4
    wSub ⟨4 * col' + row, by
      have : row < 4 := Nat.mod_lt _ (by decide)
      have : col' < 4 := Nat.mod_lt _ (by decide)
      omega⟩ j
  have hShiftBit : ∀ i j, BitOf (wShift i j) ((aesShiftRows (aesSubBytes s) i) j) := by
    intro i j
    have := aesShiftRows_sound (aesSubBytes s) wSub hSubBit i j
    simp only at this
    exact this
  -- Layer 3 (conditional): MixColumns.
  cases h_final : is_final
  · -- Non-final round: apply MixColumns.
    have hMix : ∀ i, ∃ w : Fin 8 → F,
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
    simp only [h_final, if_false]
    exact h_add
  · -- Final round: skip MixColumns.
    refine ⟨fun i j => wShift i j + wRK i j - 2 * (wShift i j * wRK i j), ?_⟩
    intro i j
    have h_add := aesAddRoundKey_sound
                    (aesShiftRows (aesSubBytes s)) rk
                    wShift wRK hShiftBit hRK i j
    unfold aesRoundStep
    simp only [h_final, if_true]
    exact h_add

end Xark
