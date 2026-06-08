/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

-- We disable a few style/lint checks that flag this file's proof style. None of
-- them are correctness lints; they are pinned-simp / unscoped-set-option
-- house-style checks. The proofs use a branch-uniform `cases <;> simp` driver
-- (8 Boolean cases per `Ch`/`Maj` proof) that the `flexible` linter dislikes
-- because the simp set is not pinned. The `style.header` linter hard-codes the
-- Apache license string (this is an MIT project). The `style.setOption` linter
-- flags top-level `set_option` declarations; we use them deliberately.
set_option linter.style.setOption false
set_option linter.style.header false
set_option linter.flexible false

/-!
# xark SHA-256 structural soundness — Layer B, mechanised in Lean 4 / mathlib

This file builds the **structural** soundness layer for the SHA-256 compression
gadget in `crates/acir-r1cs/src/gadgets/hash.rs`. Per
`docs/FORMAL_VERIFICATION_PLAN.md`, bit-level equivalence of *individual*
per-bit gadgets (`and`, `xor`, `not`, boolean range checks, parity carry,
wrapping-add carry) is discharged elsewhere — see `Formal/Bitwise.lean` and
`Formal/Arith.lean`, which prove each per-bit / per-word constraint pins its
output to the intended boolean / arithmetic function over the BN254 scalar
field.

What this file does:

* defines a pure Lean spec `Word32 := Fin 32 → Bool` for the 32-bit words the
  gadget threads through SHA-256 (LSB-first, mirroring `Word32.bits` in the
  Rust gadget);
* defines pure Lean specs for the FIPS 180-4 §4.1.2 primitives (`rotr`, `shr`,
  `not32`, `and32`, `xor32`, `Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁`);
* defines the FIPS 180-4 §6.2 message-schedule recurrence in pure Lean;
* gives **structural soundness theorems**: given the per-bit witness wires
  pinned to their boolean values (the conclusion of the per-bit lemmas in
  `Formal/Bitwise.lean`), the composite SHA-256 primitives (`Ch`, `Maj`, the
  four sigmas) materialise field expressions that are `BitOf` of the
  pure-spec output. These compose the proven per-bit pieces — no bit-blasting.

What this file does *not* do: it does **not** attempt to bit-blast SHA-256 in
Lean. The Formal Verification Plan explicitly says bit-oriented hashes are
better suited to SMT bit-blasting than to a proof assistant, so the
"end-to-end" theorem (output of the R1CS circuit equals 256-bit SHA-256 hash
of the input) is deferred to the SMT layer. The job here is the *structural*
assembly: show that the composite operations decompose into proven per-bit
pieces in the way `hash.rs` claims.

`Word32` is represented as `Fin 32 → Bool` rather than `BitVec 32`. The Rust
gadget stores 32 ordered bit-wires (LSB first); `rotr` and `shr` are index
permutations / projections on that ordered list. `Fin 32 → Bool` makes the
permutation reasoning a single `funext + index arithmetic` rewrite, no
`BitVec.getLsbD` unfolding.
-/

namespace Xark

/-! ## Word32 representation -/

/-- A 32-bit word, LSB-first: `w i` is the bit at position `i` (index `0`
matches the Rust `bits[0]`). This mirrors the storage of `Word32.bits` in
`crates/acir-r1cs/src/gadgets/bitwise.rs`. -/
abbrev Word32 : Type := Fin 32 → Bool

/-! ## Pure-Lean specs of the primitives -/

/-- Right rotation by `k` positions: `out i = a ((i + k) mod 32)`. Matches the
Rust `rotr` in `bitwise.rs`, which produces `bits[(i + k) % 32].clone()`. -/
def rotr (a : Word32) (k : ℕ) : Word32 :=
  fun i => a ⟨(i.val + k) % 32, Nat.mod_lt _ (by decide)⟩

/-- Right shift by `k` positions: `out i = a (i + k)` if `i + k < 32`, else
`false`. Matches the Rust `shr` in `bitwise.rs`. -/
def shr (a : Word32) (k : ℕ) : Word32 :=
  fun i =>
    if h : i.val + k < 32 then a ⟨i.val + k, h⟩ else false

/-- Bitwise NOT, pointwise. -/
def not32 (a : Word32) : Word32 := fun i => !(a i)

/-- Bitwise AND, pointwise. -/
def and32 (a b : Word32) : Word32 := fun i => (a i) && (b i)

/-- Bitwise XOR, pointwise. -/
def xor32 (a b : Word32) : Word32 := fun i => xor (a i) (b i)

/-- FIPS 180-4 §4.1.2: `Ch(x, y, z) = (x AND y) XOR ((NOT x) AND z)`. -/
def Ch (x y z : Word32) : Word32 :=
  xor32 (and32 x y) (and32 (not32 x) z)

/-- FIPS 180-4 §4.1.2: `Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z)`. -/
def Maj (x y z : Word32) : Word32 :=
  xor32 (xor32 (and32 x y) (and32 x z)) (and32 y z)

/-- FIPS 180-4 §4.1.2: `Σ₀(x) = ROTR(x,2) XOR ROTR(x,13) XOR ROTR(x,22)`. -/
def bigSigma0 (x : Word32) : Word32 :=
  xor32 (xor32 (rotr x 2) (rotr x 13)) (rotr x 22)

/-- FIPS 180-4 §4.1.2: `Σ₁(x) = ROTR(x,6) XOR ROTR(x,11) XOR ROTR(x,25)`. -/
def bigSigma1 (x : Word32) : Word32 :=
  xor32 (xor32 (rotr x 6) (rotr x 11)) (rotr x 25)

/-- FIPS 180-4 §4.1.2: `σ₀(x) = ROTR(x,7) XOR ROTR(x,18) XOR SHR(x,3)`. -/
def smallSigma0 (x : Word32) : Word32 :=
  xor32 (xor32 (rotr x 7) (rotr x 18)) (shr x 3)

/-- FIPS 180-4 §4.1.2: `σ₁(x) = ROTR(x,17) XOR ROTR(x,19) XOR SHR(x,10)`. -/
def smallSigma1 (x : Word32) : Word32 :=
  xor32 (xor32 (rotr x 17) (rotr x 19)) (shr x 10)

/-! ## Bit-level soundness primitives (the "modulo" assumptions)

The Rust gadgets in `bitwise.rs` emit per-bit constraints already proven sound
in `Formal/Bitwise.lean`:

* `and_sound`  : `a*b = out` ⇒ `out = a ∧ b`,
* `xor_sound`  : `(2a)*b = a + b − out` ⇒ `out = a ⊕ b`,
* `not_sound`  : `1 − a` is logical NOT.

We package these as a single Lean predicate `BitOf` that says a field-element
witness wire `w : F` represents a boolean bit `bit : Bool` (`w = 0 ↔ bit = false`,
`w = 1 ↔ bit = true`). The composite-primitive soundness theorems below take
hypotheses of the form "this bit-wire `BitOf` this bit of the pure-spec output"
and conclude the same for the composite output — i.e. *structural* lifting of
the per-bit lemmas to whole-word operations. -/

/-- A field element `w` represents the boolean bit `bit`: it is `0` when
`bit = false` and `1` when `bit = true`. This is the bridge from R1CS witness
wires (`ZMod r` elements) to the pure-Lean `Bool` spec. -/
def BitOf {F : Type*} [Zero F] [One F] (w : F) (bit : Bool) : Prop :=
  if bit then w = 1 else w = 0

/-- A `BitOf` wire is in `{0, 1}`. -/
theorem BitOf.isBool {F : Type*} [Zero F] [One F] {w : F} {bit : Bool}
    (h : BitOf w bit) : w = 0 ∨ w = 1 := by
  unfold BitOf at h
  cases bit
  · left; simpa using h
  · right; simpa using h

/-! ## Soundness for the index-permutation gadgets (`rotr`, `shr`)

These cost **zero constraints** in `bitwise.rs` — they relabel the bit-LCs.
Soundness is therefore trivial *given* the input bits are already pinned to
their boolean values: the output bit-wire for position `i` is simply the
input bit-wire for the permuted index, no field-level reasoning required.

We model "the witness for bit `i` of `a`" as a function `wA : Fin 32 → F`. The
hypothesis says each wire is `BitOf` the corresponding spec bit. The
conclusion picks the witness function for the output (a permutation /
projection of `wA`) and shows it is `BitOf` the spec-level rotated / shifted
output. -/

/-- **`rotr` gadget soundness.** If every input bit-wire `wA i` is `BitOf
(a i)`, then the rotation gadget's output wire for bit `i` — which is just
`wA` evaluated at the permuted index `(i + k) mod 32` — is `BitOf` the
pure-spec `rotr a k` bit. -/
theorem rotr_sound {F : Type*} [Zero F] [One F]
    (a : Word32) (wA : Fin 32 → F)
    (hA : ∀ i, BitOf (wA i) (a i)) (k : ℕ) :
    ∀ i, BitOf (wA ⟨(i.val + k) % 32, Nat.mod_lt _ (by decide)⟩)
              ((rotr a k) i) := by
  intro i
  unfold rotr
  exact hA _

/-- **`shr` gadget soundness.** The shift gadget's output wire for bit `i` is
the input wire at index `i + k` if that fits, else the field constant `(0 :
F)`. Both choices are `BitOf` the pure-spec `shr a k` bit at position `i`. -/
theorem shr_sound {F : Type*} [Zero F] [One F]
    (a : Word32) (wA : Fin 32 → F)
    (hA : ∀ i, BitOf (wA i) (a i)) (k : ℕ) :
    ∀ i,
      if h : i.val + k < 32
        then BitOf (wA ⟨i.val + k, h⟩) ((shr a k) i)
        else BitOf (0 : F) ((shr a k) i) := by
  intro i
  by_cases h : i.val + k < 32
  · simp [h, shr]; exact hA _
  · simp [h, shr]; unfold BitOf; simp

/-! ## Soundness for the pointwise gadgets (`not32`, `and32`, `xor32`)

Each output bit is pinned by the per-bit constraint proven sound in
`Formal/Bitwise.lean`. The "lift to a whole `Word32`" is `∀ i`-quantified
forwarding. -/

/-- **`not32` gadget soundness.** The Rust `not` returns the LC `1 − a` per
bit. Given the input bit-wire `wA i` is `BitOf (a i)`, the output wire `1 -
wA i` is `BitOf` the spec-level `!a i`. -/
theorem not32_sound {F : Type*} [Ring F]
    (a : Word32) (wA : Fin 32 → F)
    (hA : ∀ i, BitOf (wA i) (a i)) :
    ∀ i, BitOf ((1 : F) - wA i) ((not32 a) i) := by
  intro i
  have hi := hA i
  unfold BitOf at hi
  unfold not32 BitOf
  cases hai : a i
  · simp [hai] at hi; simp [hi]
  · simp [hai] at hi; simp [hi]

/-- **`and32` gadget soundness.** The Rust `and` allocates `out_i` with `a_i *
b_i = out_i`. Given input bit-wires `wA i`, `wB i` `BitOf` their bits, the
field product `wA i * wB i` is `BitOf` of the spec-level `a i && b i`. -/
theorem and32_sound {F : Type*} [Field F]
    (a b : Word32) (wA wB : Fin 32 → F)
    (hA : ∀ i, BitOf (wA i) (a i)) (hB : ∀ i, BitOf (wB i) (b i)) :
    ∀ i, BitOf (wA i * wB i) ((and32 a b) i) := by
  intro i
  have ha := hA i
  have hb := hB i
  unfold BitOf at ha hb
  unfold and32 BitOf
  cases hai : a i <;> cases hbi : b i <;>
    (simp [hai, hbi] at ha hb ⊢; rw [ha, hb]; norm_num)

/-- **`xor32` gadget soundness.** The Rust `xor` allocates `out_i` with
`(2*a_i)*b_i = a_i + b_i - out_i`, which (per `xor_sound` in
`Formal/Bitwise.lean`) pins `out_i = a_i + b_i - 2 a_i b_i`. That value is
`BitOf` of the spec-level `xor (a i) (b i)`. -/
theorem xor32_sound {F : Type*} [Field F]
    (a b : Word32) (wA wB : Fin 32 → F)
    (hA : ∀ i, BitOf (wA i) (a i)) (hB : ∀ i, BitOf (wB i) (b i)) :
    ∀ i, BitOf (wA i + wB i - 2 * (wA i * wB i)) ((xor32 a b) i) := by
  intro i
  have ha := hA i
  have hb := hB i
  unfold BitOf at ha hb
  unfold xor32 BitOf
  cases hai : a i <;> cases hbi : b i <;>
    (simp [hai, hbi] at ha hb ⊢; rw [ha, hb]; norm_num)

/-! ## Soundness for the composite SHA-256 primitives

`Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁` are pure-spec compositions of the
primitives above. We expose **structural-defining identities** as `rfl`-up-to-
`unfold` lemmas and then give a single bit-level soundness theorem for each
of the non-permutation composites (`Ch`, `Maj`) that chains the per-bit
witness arithmetic together. -/

/-- **Structural definition of `Ch`** matches its gadget implementation in
`hash.rs`. The Rust loop builds

```
let e_and_f      = and(builder, &e, &f)?;
let not_e_and_g  = and(builder, &not(&e), &g)?;
let ch           = xor(builder, &e_and_f, &not_e_and_g)?;
```

which is precisely `xor32 (and32 e f) (and32 (not32 e) g)`. -/
theorem Ch_unfold (x y z : Word32) :
    Ch x y z = xor32 (and32 x y) (and32 (not32 x) z) := rfl

/-- **Structural definition of `Maj`** matches its gadget. The Rust pattern
uses `xor_triple` (the parity-carry form) for the outer 3-way XOR; the
*function* computed is `xor32 (xor32 (and32 x y) (and32 x z)) (and32 y z)`.
Soundness of the `xor_triple` shape is the parity carry of
`Formal/Arith.lean`; we keep the per-bit obligation there and only state the
structural composition here. -/
theorem Maj_unfold (x y z : Word32) :
    Maj x y z = xor32 (xor32 (and32 x y) (and32 x z)) (and32 y z) := rfl

/-- **Structural definition of `Σ₀`** matches its gadget composition. -/
theorem bigSigma0_unfold (x : Word32) :
    bigSigma0 x = xor32 (xor32 (rotr x 2) (rotr x 13)) (rotr x 22) := rfl

/-- **Structural definition of `Σ₁`** matches its gadget composition. -/
theorem bigSigma1_unfold (x : Word32) :
    bigSigma1 x = xor32 (xor32 (rotr x 6) (rotr x 11)) (rotr x 25) := rfl

/-- **Structural definition of `σ₀`** matches its gadget composition. -/
theorem smallSigma0_unfold (x : Word32) :
    smallSigma0 x = xor32 (xor32 (rotr x 7) (rotr x 18)) (shr x 3) := rfl

/-- **Structural definition of `σ₁`** matches its gadget composition. -/
theorem smallSigma1_unfold (x : Word32) :
    smallSigma1 x = xor32 (xor32 (rotr x 17) (rotr x 19)) (shr x 10) := rfl

/-! ## End-to-end pointwise soundness for the SHA-256 primitives

For `Ch` and `Maj` we give a bit-level soundness theorem: if every input bit
is `BitOf`-witnessed, then the chained field-arithmetic expression that the
gadget materialises for the `i`-th output bit is `BitOf` of the `i`-th
spec-level output bit. This is the structural assembly the Formal Verification
Plan calls for: we are *not* checking concrete field arithmetic — that's
discharged per-bit in `Formal/Bitwise.lean` — we are checking the composition
tree is the intended pure function. -/

/-- **`Ch` end-to-end structural soundness, per bit.** Inputs `x, y, z` are
`BitOf`-witnessed by `wX, wY, wZ : Fin 32 → F`. Then the field-level
expression that the gadget materialises for the `i`-th output bit — namely
`e_and_f + not_e_and_g - 2 (e_and_f * not_e_and_g)` with `e_and_f = wX i * wY
i` and `not_e_and_g = (1 - wX i) * wZ i` — is `BitOf` of the `i`-th spec-level
`Ch x y z` bit. This composes `and32_sound`, `not32_sound`, `xor32_sound`. -/
theorem Ch_bit_sound {F : Type*} [Field F]
    (x y z : Word32) (wX wY wZ : Fin 32 → F)
    (hX : ∀ i, BitOf (wX i) (x i)) (hY : ∀ i, BitOf (wY i) (y i))
    (hZ : ∀ i, BitOf (wZ i) (z i)) :
    ∀ i,
      let e_and_f     := wX i * wY i
      let not_e_and_g := (1 - wX i) * wZ i
      BitOf (e_and_f + not_e_and_g - 2 * (e_and_f * not_e_and_g))
            ((Ch x y z) i) := by
  intro i
  simp only
  -- Case-split on each input bit `x i`, `y i`, `z i`. Each branch fixes the
  -- witness wire to `0` or `1` via the `BitOf` hypothesis, and the goal
  -- reduces to a concrete arithmetic identity.
  have ha := hX i
  have hb := hY i
  have hc := hZ i
  unfold BitOf at ha hb hc
  unfold Ch xor32 and32 not32 BitOf
  cases hxi : x i <;> cases hyi : y i <;> cases hzi : z i <;>
    (simp [hxi, hyi, hzi] at ha hb hc; rw [ha, hb, hc]; norm_num)

/-- **`Maj` end-to-end structural soundness, per bit.** Composes three
`and32_sound`s with two `xor32_sound`s to land on the spec-level `Maj x y z`
bit. The witness expression matches the gadget composition

```
let a_and_b   = and(builder, &a, &b)?;   // wires: wX i * wY i
let a_and_c   = and(builder, &a, &c)?;   // wires: wX i * wZ i
let b_and_c   = and(builder, &b, &c)?;   // wires: wY i * wZ i
let maj       = xor_triple(builder, &a_and_b, &a_and_c, &b_and_c)?;
```

where `xor_triple`'s parity-carry form (proven sound in `Formal/Arith.lean`)
is here unfolded to two nested binary XORs, so the bit-level witness can be
expressed in closed form. -/
theorem Maj_bit_sound {F : Type*} [Field F]
    (x y z : Word32) (wX wY wZ : Fin 32 → F)
    (hX : ∀ i, BitOf (wX i) (x i)) (hY : ∀ i, BitOf (wY i) (y i))
    (hZ : ∀ i, BitOf (wZ i) (z i)) :
    ∀ i,
      let ab := wX i * wY i
      let ac := wX i * wZ i
      let bc := wY i * wZ i
      let ab_xor_ac := ab + ac - 2 * (ab * ac)
      BitOf (ab_xor_ac + bc - 2 * (ab_xor_ac * bc))
            ((Maj x y z) i) := by
  intro i
  simp only
  -- Same approach as `Ch_bit_sound`: case-split on each input bit `x i`,
  -- `y i`, `z i`. Each branch fixes `wX i, wY i, wZ i` to `0` or `1`, then
  -- arithmetic concludes.
  have ha := hX i
  have hb := hY i
  have hc := hZ i
  unfold BitOf at ha hb hc
  unfold Maj xor32 and32 BitOf
  cases hxi : x i <;> cases hyi : y i <;> cases hzi : z i <;>
    (simp [hxi, hyi, hzi] at ha hb hc; rw [ha, hb, hc]; norm_num)

/-! ## Σ / σ soundness: bitwise spec identities

The four sigma functions are XOR-of-rotations / XOR-of-rotation-and-shift.
The rotations and shifts are zero-cost (index permutations of the input
bit-wires), so soundness at this layer is the pure-spec bitwise XOR identity
— we state them as `∀ i, ... = ...` equalities so callers chaining these into
the compression round soundness story can rewrite directly. -/

/-- **`Σ₀` bitwise spec equality.** The `i`-th bit of `Σ₀ x` is the XOR of the
`i`-th bits of three rotations of `x`. -/
theorem bigSigma0_bit (x : Word32) (i : Fin 32) :
    (bigSigma0 x) i = xor (xor ((rotr x 2) i) ((rotr x 13) i)) ((rotr x 22) i) := by
  unfold bigSigma0 xor32; rfl

/-- **`Σ₁` bitwise spec equality.** -/
theorem bigSigma1_bit (x : Word32) (i : Fin 32) :
    (bigSigma1 x) i = xor (xor ((rotr x 6) i) ((rotr x 11) i)) ((rotr x 25) i) := by
  unfold bigSigma1 xor32; rfl

/-- **`σ₀` bitwise spec equality.** -/
theorem smallSigma0_bit (x : Word32) (i : Fin 32) :
    (smallSigma0 x) i = xor (xor ((rotr x 7) i) ((rotr x 18) i)) ((shr x 3) i) := by
  unfold smallSigma0 xor32; rfl

/-- **`σ₁` bitwise spec equality.** -/
theorem smallSigma1_bit (x : Word32) (i : Fin 32) :
    (smallSigma1 x) i = xor (xor ((rotr x 17) i) ((rotr x 19) i)) ((shr x 10) i) := by
  unfold smallSigma1 xor32; rfl

/-! ## Pure-Lean SHA-256 message-schedule recurrence

We model the schedule's recurrence *equation* without committing to a concrete
recursive definition (avoiding `Nat.strongRecOn` and the noncomputability it
entails). What's important for the structural soundness story is the *shape*
of the recurrence: `W[t]` is the wrapping-add of four terms `σ₁(W[t-2])`,
`W[t-7]`, `σ₀(W[t-15])`, `W[t-16]`. The gadget builds it in exactly that
shape; the soundness obligation is that the gadget's `add_mod_32` over those
four words computes the same wrapping-add that the recurrence specifies. -/

/-- The natural-number value of a `Word32` (LSB first). Used to lift the
boolean-vector spec to a `ℕ`-valued spec for the wrapping-add. -/
def toNat (w : Word32) : ℕ :=
  ∑ i : Fin 32, (if w i then 1 else 0) * 2 ^ i.val

/-- Every `Word32` fits in 32 bits. -/
theorem toNat_lt (w : Word32) : toNat w < 2 ^ 32 := by
  unfold toNat
  have hb : ∀ i : Fin 32, (if w i then (1 : ℕ) else 0) * 2 ^ i.val ≤ 2 ^ i.val := by
    intro i; split <;> simp
  have hsum : (∑ i : Fin 32, (if w i then (1 : ℕ) else 0) * 2 ^ i.val)
            ≤ ∑ i : Fin 32, 2 ^ i.val := Finset.sum_le_sum (fun i _ => hb i)
  have heq : (∑ i : Fin 32, (2 : ℕ) ^ i.val) = 2 ^ 32 - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) 32, Nat.geomSum_eq (by norm_num) 32]
    simp
  rw [heq] at hsum
  have hp : 0 < (2 : ℕ) ^ 32 := pow_pos (by norm_num) _
  omega

/-- Reconstruct a `Word32` from a natural number by reading its low 32 bits. -/
def ofNat (n : ℕ) : Word32 := fun i => (n / 2 ^ i.val) % 2 = 1

/-- Wrapping 32-bit addition on `Word32`, defined via the `toNat`/`ofNat`
round trip. Matches the `+` of FIPS 180-4 §6.2 and the semantics of the Rust
`add_mod_32`. -/
def addMod32 (a b : Word32) : Word32 := ofNat ((toNat a + toNat b) % 2 ^ 32)

/-- **Message-schedule recurrence (pure spec).** The defining equation of
`W[t]` for `t ∈ [16, 64)` per FIPS 180-4 §6.2, written as a predicate on a
hypothetical schedule `W : Fin 64 → Word32`. The Rust gadget builds `W[t]`
with one `add_mod_32` call over four terms; the predicate below picks the
same four terms (in the same order the gadget passes them) so the structural
witness is direct. -/
def MessageScheduleStep (W : Fin 64 → Word32) (t : Fin 64) (ht : 16 ≤ t.val) : Prop :=
  W t =
    addMod32
      (addMod32
        (addMod32
          (W ⟨t.val - 16, by omega⟩)
          (smallSigma0 (W ⟨t.val - 15, by omega⟩)))
        (W ⟨t.val - 7,  by omega⟩))
      (smallSigma1 (W ⟨t.val - 2,  by omega⟩))

/-- **Message-schedule structural identity.** Restates the recurrence as an
`iff`-trivial form, useful when rewriting: knowing the gadget materialises
the four-term `add_mod_32` over the *same* four words as `MessageScheduleStep`
gives `W t = ...`, immediately. (The point is anchoring: this is the shape the
gadget reproduces — see `hash.rs` lines for `i in 16..64`.) -/
theorem MessageScheduleStep_iff (W : Fin 64 → Word32) (t : Fin 64) (ht : 16 ≤ t.val) :
    MessageScheduleStep W t ht ↔
      W t = addMod32
              (addMod32
                (addMod32
                  (W ⟨t.val - 16, by omega⟩)
                  (smallSigma0 (W ⟨t.val - 15, by omega⟩)))
                (W ⟨t.val - 7,  by omega⟩))
              (smallSigma1 (W ⟨t.val - 2,  by omega⟩)) :=
  Iff.rfl

end Xark
