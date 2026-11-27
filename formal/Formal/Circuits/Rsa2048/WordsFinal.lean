/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.WordsSq

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The words chain: the final call's bridges

The accumulator after each squaring (`wAccList`), the modulus and the encoded message,
and the final `grouped_columns` call's four arrays.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

def wChainN (σ : ℕ → F) : ℤ := val (limb (wcallAt 40) σ 25)
def wChainEm (σ : ℕ → F) : ℤ := val (limb (wcallAt 88) σ 100)
def wAccList (σ : ℕ → F) : List ℤ :=
  [
   val (limb (wcallAt 40) σ 0),
   val (limb (wcallAt 43) σ 0),
   val (limb (wcallAt 46) σ 0),
   val (limb (wcallAt 49) σ 0),
   val (limb (wcallAt 52) σ 0),
   val (limb (wcallAt 55) σ 0),
   val (limb (wcallAt 58) σ 0),
   val (limb (wcallAt 61) σ 0),
   val (limb (wcallAt 64) σ 0),
   val (limb (wcallAt 67) σ 0),
   val (limb (wcallAt 70) σ 0),
   val (limb (wcallAt 73) σ 0),
   val (limb (wcallAt 76) σ 0),
   val (limb (wcallAt 79) σ 0),
   val (limb (wcallAt 82) σ 0),
   val (limb (wcallAt 85) σ 0),
   val (limb (wcallAt 88) σ 0)]

def wChainA (σ : ℕ → F) (k : ℕ) : ℤ := (wAccList σ).getD k 0

theorem wA_0 (σ : ℕ → F) :
    val (limb (wcallAt 43) σ 0) = val (limb (wcallAt 40) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 43).plugs.drop 0).take 25 = ((wcallAt 40).plugs.drop 75).take 25)

theorem wA_1 (σ : ℕ → F) :
    val (limb (wcallAt 46) σ 0) = val (limb (wcallAt 43) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 46).plugs.drop 0).take 25 = ((wcallAt 43).plugs.drop 75).take 25)

theorem wA_2 (σ : ℕ → F) :
    val (limb (wcallAt 49) σ 0) = val (limb (wcallAt 46) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 49).plugs.drop 0).take 25 = ((wcallAt 46).plugs.drop 75).take 25)

theorem wA_3 (σ : ℕ → F) :
    val (limb (wcallAt 52) σ 0) = val (limb (wcallAt 49) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 52).plugs.drop 0).take 25 = ((wcallAt 49).plugs.drop 75).take 25)

theorem wA_4 (σ : ℕ → F) :
    val (limb (wcallAt 55) σ 0) = val (limb (wcallAt 52) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 55).plugs.drop 0).take 25 = ((wcallAt 52).plugs.drop 75).take 25)

theorem wA_5 (σ : ℕ → F) :
    val (limb (wcallAt 58) σ 0) = val (limb (wcallAt 55) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 58).plugs.drop 0).take 25 = ((wcallAt 55).plugs.drop 75).take 25)

theorem wA_6 (σ : ℕ → F) :
    val (limb (wcallAt 61) σ 0) = val (limb (wcallAt 58) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 61).plugs.drop 0).take 25 = ((wcallAt 58).plugs.drop 75).take 25)

theorem wA_7 (σ : ℕ → F) :
    val (limb (wcallAt 64) σ 0) = val (limb (wcallAt 61) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 64).plugs.drop 0).take 25 = ((wcallAt 61).plugs.drop 75).take 25)

theorem wA_8 (σ : ℕ → F) :
    val (limb (wcallAt 67) σ 0) = val (limb (wcallAt 64) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 67).plugs.drop 0).take 25 = ((wcallAt 64).plugs.drop 75).take 25)

theorem wA_9 (σ : ℕ → F) :
    val (limb (wcallAt 70) σ 0) = val (limb (wcallAt 67) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 70).plugs.drop 0).take 25 = ((wcallAt 67).plugs.drop 75).take 25)

theorem wA_10 (σ : ℕ → F) :
    val (limb (wcallAt 73) σ 0) = val (limb (wcallAt 70) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 73).plugs.drop 0).take 25 = ((wcallAt 70).plugs.drop 75).take 25)

theorem wA_11 (σ : ℕ → F) :
    val (limb (wcallAt 76) σ 0) = val (limb (wcallAt 73) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 76).plugs.drop 0).take 25 = ((wcallAt 73).plugs.drop 75).take 25)

theorem wA_12 (σ : ℕ → F) :
    val (limb (wcallAt 79) σ 0) = val (limb (wcallAt 76) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 79).plugs.drop 0).take 25 = ((wcallAt 76).plugs.drop 75).take 25)

theorem wA_13 (σ : ℕ → F) :
    val (limb (wcallAt 82) σ 0) = val (limb (wcallAt 79) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 82).plugs.drop 0).take 25 = ((wcallAt 79).plugs.drop 75).take 25)

theorem wA_14 (σ : ℕ → F) :
    val (limb (wcallAt 85) σ 0) = val (limb (wcallAt 82) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 85).plugs.drop 0).take 25 = ((wcallAt 82).plugs.drop 75).take 25)

theorem wA_15 (σ : ℕ → F) :
    val (limb (wcallAt 88) σ 0) = val (limb (wcallAt 85) σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((wcallAt 88).plugs.drop 0).take 25 = ((wcallAt 85).plugs.drop 75).take 25)

theorem wFinB (σ : ℕ → F) :
    val (limb (wcallAt 88) σ 25) = val (limb (wcallAt 40) σ 0) :=
  val_limb_eq σ (off := 25) (off' := 0)
    (by decide +kernel : ((wcallAt 88).plugs.drop 25).take 25 = ((wcallAt 40).plugs.drop 0).take 25)

theorem wFinM (σ : ℕ → F) :
    val (limb (wcallAt 88) σ 50) = wChainN σ := by
  rw [wChainN]
  exact val_limb_eq σ (off := 50) (off' := 25)
    (by decide +kernel : ((wcallAt 88).plugs.drop 50).take 25 = ((wcallAt 40).plugs.drop 25).take 25)

end Xark.Circuits.Rsa2048
