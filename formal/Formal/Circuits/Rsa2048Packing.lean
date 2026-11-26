/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048Verify
import Formal.ToBits
import Formal.RsaEm

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The byte packing behind `rsa2048`'s chain calls

The chain calls' modulus, signature and encoded-message limbs are not free variables:
`bytes_to_wide` builds each limb out of the 544 `to_bits` calls' bits, and
`sha256_em_bits_82` adds the digest's bits to the constant frame. This file models
those linear combinations.

The `to_bits::<8>` gadget returns `[bit 0, bit 1, …, bit 7]` with **bit 0 affine**
(`byte − Σ_{s<7} 2^{s+1}·wit_s`) and bits 1..7 the witnesses `base + s`; byte `b`'s
call is segment `b` with `base = 544 + 7b`. `bytes_to_wide`'s bit `j` is byte
`off + 255 − j/8`, bit `j % 8`, at the limb's weight `2^{j % 82}` (the octet string is
big-endian; `off` is 0 for `n`, 256 for `sig`, 512 for the digest). The `em` limbs
add `EM82_CONST`'s limb.

`normTerms` sorts and merges the exported combination, so each packed limb is
proved equal to its model by `decide +kernel` on the normalized terms.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template

/-- The `to_bits` call for byte `b` starts its witnesses at `544 + 7b`. -/
def bitBase (b : ℕ) : ℕ := 544 + 7 * b

/-- Byte `b`'s bit `tb` as a combination over the circuit's variables: bit 0 is the
affine top output, bits 1..7 are the witnesses. -/
def bitTerms (b tb : ℕ) : List (F × ℕ) :=
  if tb = 0 then
    (1, b) :: (List.range 7).map (fun s => (-(↑(2 ^ (s + 1)) : F), bitBase b + s))
  else [(1, bitBase b + (tb - 1))]

def bitGLC (b tb : ℕ) : GLC := ⟨0, bitTerms b tb⟩

/-- The integer-coefficient form of the same bit (for the shadow). -/
def bitZ (b tb : ℕ) : Xark.Circuit.ZLC :=
  if tb = 0 then
    ⟨0, (1, b) :: (List.range 7).map (fun s => (-(2 ^ (s + 1) : ℤ), bitBase b + s))⟩
  else ⟨0, [(1, bitBase b + (tb - 1))]⟩

/-- The packing of 25×82 limbs from bytes `off .. off+255`, big-endian. -/
def packTermsAt (off q : ℕ) : List (F × ℕ) :=
  (List.range 82).flatMap fun t =>
    let j := 82 * q + t
    if j < 2048 then
      let b := off + (255 - j / 8)
      let tb := j % 8
      (bitTerms b tb).map fun term => (((↑(2 ^ t)) : F) * term.1, term.2)
    else []

def packGLCAt (off q : ℕ) : GLC := ⟨0, packTermsAt off q⟩

/-- The encoded message's limb `q`: the constant frame plus the digest's bits (only
`j < 256`; the digest integer occupies the low 256 bits). -/
def emTerms (q : ℕ) : List (F × ℕ) :=
  (List.range 82).flatMap fun t =>
    let j := 82 * q + t
    if j < 256 then
      let b := 512 + (31 - j / 8)
      let tb := j % 8
      (bitTerms b tb).map fun term => (((↑(2 ^ t)) : F) * term.1, term.2)
    else []

def emGLC (q : ℕ) : GLC := ⟨((Xark.Rsa.Em.em82 q : ℤ) : F), emTerms q⟩

def leNat : ℕ → ℕ → Bool := fun a b => a ≤ b

theorem nTerms0 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 0) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 0) := by
  decide +kernel

theorem nTerms1 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 1) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 1) := by
  decide +kernel

theorem nTerms2 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 2) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 2) := by
  decide +kernel

theorem nTerms3 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 3) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 3) := by
  decide +kernel

theorem nTerms4 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 4) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 4) := by
  decide +kernel

theorem nTerms5 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 5) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 5) := by
  decide +kernel

theorem nTerms6 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 6) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 6) := by
  decide +kernel

theorem nTerms7 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 7) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 7) := by
  decide +kernel

theorem nTerms8 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 8) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 8) := by
  decide +kernel

theorem nTerms9 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 9) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 9) := by
  decide +kernel

theorem nTerms10 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 10) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 10) := by
  decide +kernel

theorem nTerms11 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 11) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 11) := by
  decide +kernel

theorem nTerms12 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 12) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 12) := by
  decide +kernel

theorem nTerms13 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 13) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 13) := by
  decide +kernel

theorem nTerms14 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 14) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 14) := by
  decide +kernel

theorem nTerms15 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 15) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 15) := by
  decide +kernel

theorem nTerms16 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 16) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 16) := by
  decide +kernel

theorem nTerms17 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 17) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 17) := by
  decide +kernel

theorem nTerms18 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 18) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 18) := by
  decide +kernel

theorem nTerms19 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 19) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 19) := by
  decide +kernel

theorem nTerms20 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 20) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 20) := by
  decide +kernel

theorem nTerms21 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 21) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 21) := by
  decide +kernel

theorem nTerms22 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 22) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 22) := by
  decide +kernel

theorem nTerms23 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 23) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 23) := by
  decide +kernel

theorem nTerms24 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD (25 + 24) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 0 24) := by
  decide +kernel

theorem sigTerms0 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 0 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 0) := by
  decide +kernel

theorem sigTerms1 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 1 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 1) := by
  decide +kernel

theorem sigTerms2 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 2 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 2) := by
  decide +kernel

theorem sigTerms3 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 3 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 3) := by
  decide +kernel

theorem sigTerms4 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 4 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 4) := by
  decide +kernel

theorem sigTerms5 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 5 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 5) := by
  decide +kernel

theorem sigTerms6 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 6 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 6) := by
  decide +kernel

theorem sigTerms7 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 7 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 7) := by
  decide +kernel

theorem sigTerms8 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 8 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 8) := by
  decide +kernel

theorem sigTerms9 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 9 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 9) := by
  decide +kernel

theorem sigTerms10 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 10 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 10) := by
  decide +kernel

theorem sigTerms11 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 11 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 11) := by
  decide +kernel

theorem sigTerms12 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 12 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 12) := by
  decide +kernel

theorem sigTerms13 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 13 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 13) := by
  decide +kernel

theorem sigTerms14 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 14 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 14) := by
  decide +kernel

theorem sigTerms15 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 15 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 15) := by
  decide +kernel

theorem sigTerms16 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 16 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 16) := by
  decide +kernel

theorem sigTerms17 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 17 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 17) := by
  decide +kernel

theorem sigTerms18 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 18 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 18) := by
  decide +kernel

theorem sigTerms19 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 19 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 19) := by
  decide +kernel

theorem sigTerms20 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 20 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 20) := by
  decide +kernel

theorem sigTerms21 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 21 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 21) := by
  decide +kernel

theorem sigTerms22 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 22 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 22) := by
  decide +kernel

theorem sigTerms23 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 23 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 23) := by
  decide +kernel

theorem sigTerms24 :
    Xark.R1cs.normTerms leNat (ZLC.toF ((callAt 548).plugs.getD 24 (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (packTermsAt 256 24) := by
  decide +kernel

theorem emConst0 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 0) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 0 : ℤ) : F) := by
  decide +kernel

theorem emTerms0 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 0) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 0) := by
  decide +kernel

theorem emConst1 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 1) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 1 : ℤ) : F) := by
  decide +kernel

theorem emTerms1 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 1) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 1) := by
  decide +kernel

theorem emConst2 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 2) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 2 : ℤ) : F) := by
  decide +kernel

theorem emTerms2 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 2) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 2) := by
  decide +kernel

theorem emConst3 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 3) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 3 : ℤ) : F) := by
  decide +kernel

theorem emTerms3 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 3) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 3) := by
  decide +kernel

theorem emConst4 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 4) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 4 : ℤ) : F) := by
  decide +kernel

theorem emTerms4 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 4) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 4) := by
  decide +kernel

theorem emConst5 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 5) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 5 : ℤ) : F) := by
  decide +kernel

theorem emTerms5 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 5) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 5) := by
  decide +kernel

theorem emConst6 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 6) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 6 : ℤ) : F) := by
  decide +kernel

theorem emTerms6 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 6) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 6) := by
  decide +kernel

theorem emConst7 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 7) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 7 : ℤ) : F) := by
  decide +kernel

theorem emTerms7 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 7) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 7) := by
  decide +kernel

theorem emConst8 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 8) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 8 : ℤ) : F) := by
  decide +kernel

theorem emTerms8 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 8) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 8) := by
  decide +kernel

theorem emConst9 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 9) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 9 : ℤ) : F) := by
  decide +kernel

theorem emTerms9 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 9) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 9) := by
  decide +kernel

theorem emConst10 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 10) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 10 : ℤ) : F) := by
  decide +kernel

theorem emTerms10 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 10) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 10) := by
  decide +kernel

theorem emConst11 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 11) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 11 : ℤ) : F) := by
  decide +kernel

theorem emTerms11 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 11) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 11) := by
  decide +kernel

theorem emConst12 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 12) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 12 : ℤ) : F) := by
  decide +kernel

theorem emTerms12 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 12) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 12) := by
  decide +kernel

theorem emConst13 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 13) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 13 : ℤ) : F) := by
  decide +kernel

theorem emTerms13 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 13) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 13) := by
  decide +kernel

theorem emConst14 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 14) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 14 : ℤ) : F) := by
  decide +kernel

theorem emTerms14 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 14) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 14) := by
  decide +kernel

theorem emConst15 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 15) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 15 : ℤ) : F) := by
  decide +kernel

theorem emTerms15 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 15) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 15) := by
  decide +kernel

theorem emConst16 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 16) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 16 : ℤ) : F) := by
  decide +kernel

theorem emTerms16 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 16) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 16) := by
  decide +kernel

theorem emConst17 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 17) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 17 : ℤ) : F) := by
  decide +kernel

theorem emTerms17 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 17) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 17) := by
  decide +kernel

theorem emConst18 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 18) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 18 : ℤ) : F) := by
  decide +kernel

theorem emTerms18 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 18) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 18) := by
  decide +kernel

theorem emConst19 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 19) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 19 : ℤ) : F) := by
  decide +kernel

theorem emTerms19 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 19) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 19) := by
  decide +kernel

theorem emConst20 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 20) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 20 : ℤ) : F) := by
  decide +kernel

theorem emTerms20 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 20) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 20) := by
  decide +kernel

theorem emConst21 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 21) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 21 : ℤ) : F) := by
  decide +kernel

theorem emTerms21 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 21) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 21) := by
  decide +kernel

theorem emConst22 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 22) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 22 : ℤ) : F) := by
  decide +kernel

theorem emTerms22 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 22) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 22) := by
  decide +kernel

theorem emConst23 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 23) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 23 : ℤ) : F) := by
  decide +kernel

theorem emTerms23 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 23) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 23) := by
  decide +kernel

theorem emConst24 :
    (ZLC.toF ((callAt 596).plugs.getD (100 + 24) (LC.cst 0))).const
      = ((Xark.Rsa.Em.em82 24 : ℤ) : F) := by
  decide +kernel

theorem emTerms24 :
    Xark.R1cs.normTerms leNat
        (ZLC.toF ((callAt 596).plugs.getD (100 + 24) (LC.cst 0))).terms
      = Xark.R1cs.normTerms leNat (emTerms 24) := by
  decide +kernel

end Xark.Circuits.Rsa2048
