/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.Verify
import Formal.RsaChain
import Formal.RsaEm

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# `rsa2048`'s chain, composed from its seventeen calls

The circuit's chain is segments `s548, s551, …, s593` (the sixteen
`grouped_columns_square` calls) and `s596` (the terminal `grouped_columns`). Each call's
integer identity is `square_contract`/`general_contract`; the q/r `Spec`s bound its
quotient and remainder limbs, and the packed `n`/`sig`/`em` limbs' bounds are
hypotheses here (they come from the byte packing). The chain's limb vectors line up by
linear-combination equality, and `RsaChain.chain_seq_range` gives
`em ≡ sig^(2^16+1) (mod n)`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- The modulus, as the limbs the chain calls read. -/
def chainN (σ : ℕ → F) : ℤ := val (limb sq0 σ 25)

/-- The encoded message, as the terminal call's right-hand side. -/
def chainEm (σ : ℕ → F) : ℤ := val (limb fin σ 100)

/-- The chain's accumulator after each squaring (`a 0` is the signature). -/
def accList (σ : ℕ → F) : List ℤ :=
  [val (limb sq0 σ 0),
   val (limb sq1 σ 0),
   val (limb sq2 σ 0),
   val (limb sq3 σ 0),
   val (limb sq4 σ 0),
   val (limb sq5 σ 0),
   val (limb sq6 σ 0),
   val (limb sq7 σ 0),
   val (limb sq8 σ 0),
   val (limb sq9 σ 0),
   val (limb sq10 σ 0),
   val (limb sq11 σ 0),
   val (limb sq12 σ 0),
   val (limb sq13 σ 0),
   val (limb sq14 σ 0),
   val (limb sq15 σ 0),
   val (limb fin σ 0)]

def chainA (σ : ℕ → F) (k : ℕ) : ℤ := (accList σ).getD k 0

theorem hq0 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq0 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 546 (callAt 546) h rfl (by decide) rfl hi
  have hwin : ((sq0).plugs.drop 50).take 25 = ((callAt 546).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr0 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq0 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 547 (callAt 547) h rfl (by decide) rfl hi
  have hwin : ((sq0).plugs.drop 75).take 25 = ((callAt 547).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq1 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq1 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 549 (callAt 549) h rfl (by decide) rfl hi
  have hwin : ((sq1).plugs.drop 50).take 25 = ((callAt 549).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr1 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq1 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 550 (callAt 550) h rfl (by decide) rfl hi
  have hwin : ((sq1).plugs.drop 75).take 25 = ((callAt 550).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq2 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq2 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 552 (callAt 552) h rfl (by decide) rfl hi
  have hwin : ((sq2).plugs.drop 50).take 25 = ((callAt 552).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr2 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq2 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 553 (callAt 553) h rfl (by decide) rfl hi
  have hwin : ((sq2).plugs.drop 75).take 25 = ((callAt 553).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq3 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq3 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 555 (callAt 555) h rfl (by decide) rfl hi
  have hwin : ((sq3).plugs.drop 50).take 25 = ((callAt 555).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr3 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq3 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 556 (callAt 556) h rfl (by decide) rfl hi
  have hwin : ((sq3).plugs.drop 75).take 25 = ((callAt 556).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq4 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq4 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 558 (callAt 558) h rfl (by decide) rfl hi
  have hwin : ((sq4).plugs.drop 50).take 25 = ((callAt 558).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr4 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq4 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 559 (callAt 559) h rfl (by decide) rfl hi
  have hwin : ((sq4).plugs.drop 75).take 25 = ((callAt 559).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq5 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq5 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 561 (callAt 561) h rfl (by decide) rfl hi
  have hwin : ((sq5).plugs.drop 50).take 25 = ((callAt 561).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr5 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq5 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 562 (callAt 562) h rfl (by decide) rfl hi
  have hwin : ((sq5).plugs.drop 75).take 25 = ((callAt 562).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq6 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq6 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 564 (callAt 564) h rfl (by decide) rfl hi
  have hwin : ((sq6).plugs.drop 50).take 25 = ((callAt 564).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr6 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq6 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 565 (callAt 565) h rfl (by decide) rfl hi
  have hwin : ((sq6).plugs.drop 75).take 25 = ((callAt 565).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq7 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq7 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 567 (callAt 567) h rfl (by decide) rfl hi
  have hwin : ((sq7).plugs.drop 50).take 25 = ((callAt 567).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr7 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq7 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 568 (callAt 568) h rfl (by decide) rfl hi
  have hwin : ((sq7).plugs.drop 75).take 25 = ((callAt 568).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq8 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq8 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 570 (callAt 570) h rfl (by decide) rfl hi
  have hwin : ((sq8).plugs.drop 50).take 25 = ((callAt 570).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr8 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq8 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 571 (callAt 571) h rfl (by decide) rfl hi
  have hwin : ((sq8).plugs.drop 75).take 25 = ((callAt 571).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq9 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq9 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 573 (callAt 573) h rfl (by decide) rfl hi
  have hwin : ((sq9).plugs.drop 50).take 25 = ((callAt 573).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr9 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq9 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 574 (callAt 574) h rfl (by decide) rfl hi
  have hwin : ((sq9).plugs.drop 75).take 25 = ((callAt 574).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq10 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq10 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 576 (callAt 576) h rfl (by decide) rfl hi
  have hwin : ((sq10).plugs.drop 50).take 25 = ((callAt 576).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr10 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq10 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 577 (callAt 577) h rfl (by decide) rfl hi
  have hwin : ((sq10).plugs.drop 75).take 25 = ((callAt 577).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq11 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq11 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 579 (callAt 579) h rfl (by decide) rfl hi
  have hwin : ((sq11).plugs.drop 50).take 25 = ((callAt 579).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr11 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq11 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 580 (callAt 580) h rfl (by decide) rfl hi
  have hwin : ((sq11).plugs.drop 75).take 25 = ((callAt 580).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq12 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq12 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 582 (callAt 582) h rfl (by decide) rfl hi
  have hwin : ((sq12).plugs.drop 50).take 25 = ((callAt 582).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr12 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq12 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 583 (callAt 583) h rfl (by decide) rfl hi
  have hwin : ((sq12).plugs.drop 75).take 25 = ((callAt 583).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq13 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq13 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 585 (callAt 585) h rfl (by decide) rfl hi
  have hwin : ((sq13).plugs.drop 50).take 25 = ((callAt 585).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr13 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq13 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 586 (callAt 586) h rfl (by decide) rfl hi
  have hwin : ((sq13).plugs.drop 75).take 25 = ((callAt 586).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq14 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq14 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 588 (callAt 588) h rfl (by decide) rfl hi
  have hwin : ((sq14).plugs.drop 50).take 25 = ((callAt 588).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr14 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq14 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 589 (callAt 589) h rfl (by decide) rfl hi
  have hwin : ((sq14).plugs.drop 75).take 25 = ((callAt 589).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hq15 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq15 σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 591 (callAt 591) h rfl (by decide) rfl hi
  have hwin : ((sq15).plugs.drop 50).take 25 = ((callAt 591).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hr15 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq15 σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 592 (callAt 592) h rfl (by decide) rfl hi
  have hwin : ((sq15).plugs.drop 75).take 25 = ((callAt 592).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem ha1 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq1 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 547 (callAt 547) h rfl (by decide) rfl hi
  have hwin : ((sq1).plugs.drop 0).take 25 = ((callAt 547).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq1 σ i = pn (callAt 547) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha2 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq2 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 550 (callAt 550) h rfl (by decide) rfl hi
  have hwin : ((sq2).plugs.drop 0).take 25 = ((callAt 550).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq2 σ i = pn (callAt 550) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha3 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq3 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 553 (callAt 553) h rfl (by decide) rfl hi
  have hwin : ((sq3).plugs.drop 0).take 25 = ((callAt 553).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq3 σ i = pn (callAt 553) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha4 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq4 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 556 (callAt 556) h rfl (by decide) rfl hi
  have hwin : ((sq4).plugs.drop 0).take 25 = ((callAt 556).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq4 σ i = pn (callAt 556) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha5 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq5 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 559 (callAt 559) h rfl (by decide) rfl hi
  have hwin : ((sq5).plugs.drop 0).take 25 = ((callAt 559).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq5 σ i = pn (callAt 559) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha6 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq6 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 562 (callAt 562) h rfl (by decide) rfl hi
  have hwin : ((sq6).plugs.drop 0).take 25 = ((callAt 562).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq6 σ i = pn (callAt 562) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha7 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq7 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 565 (callAt 565) h rfl (by decide) rfl hi
  have hwin : ((sq7).plugs.drop 0).take 25 = ((callAt 565).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq7 σ i = pn (callAt 565) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha8 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq8 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 568 (callAt 568) h rfl (by decide) rfl hi
  have hwin : ((sq8).plugs.drop 0).take 25 = ((callAt 568).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq8 σ i = pn (callAt 568) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha9 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq9 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 571 (callAt 571) h rfl (by decide) rfl hi
  have hwin : ((sq9).plugs.drop 0).take 25 = ((callAt 571).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq9 σ i = pn (callAt 571) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha10 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq10 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 574 (callAt 574) h rfl (by decide) rfl hi
  have hwin : ((sq10).plugs.drop 0).take 25 = ((callAt 574).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq10 σ i = pn (callAt 574) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha11 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq11 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 577 (callAt 577) h rfl (by decide) rfl hi
  have hwin : ((sq11).plugs.drop 0).take 25 = ((callAt 577).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq11 σ i = pn (callAt 577) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha12 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq12 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 580 (callAt 580) h rfl (by decide) rfl hi
  have hwin : ((sq12).plugs.drop 0).take 25 = ((callAt 580).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq12 σ i = pn (callAt 580) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha13 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq13 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 583 (callAt 583) h rfl (by decide) rfl hi
  have hwin : ((sq13).plugs.drop 0).take 25 = ((callAt 583).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq13 σ i = pn (callAt 583) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha14 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq14 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 586 (callAt 586) h rfl (by decide) rfl hi
  have hwin : ((sq14).plugs.drop 0).take 25 = ((callAt 586).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq14 σ i = pn (callAt 586) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem ha15 (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn sq15 σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 589 (callAt 589) h rfl (by decide) rfl hi
  have hwin : ((sq15).plugs.drop 0).take 25 = ((callAt 589).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn sq15 σ i = pn (callAt 589) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem hm0 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq0).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm1 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq1 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq1).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm2 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq2 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq2).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm3 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq3 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq3).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm4 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq4 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq4).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm5 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq5 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq5).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm6 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq6 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq6).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm7 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq7 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq7).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm8 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq8 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq8).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm9 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq9 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq9).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm10 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq10 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq10).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm11 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq11 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq11).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm12 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq12 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq12).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm13 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq13 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq13).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm14 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq14 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq14).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hm15 (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn sq15 σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hwin : ((sq15).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  exact hN i hi

theorem hA0 (σ : ℕ → F) :
    val (limb sq1 σ 0) = val (limb sq0 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq1).plugs.drop 0).take 25 = ((sq0).plugs.drop 75).take 25)

theorem hM0 (σ : ℕ → F) :
    val (limb sq0 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq0).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA1 (σ : ℕ → F) :
    val (limb sq2 σ 0) = val (limb sq1 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq2).plugs.drop 0).take 25 = ((sq1).plugs.drop 75).take 25)

theorem hM1 (σ : ℕ → F) :
    val (limb sq1 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq1).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA2 (σ : ℕ → F) :
    val (limb sq3 σ 0) = val (limb sq2 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq3).plugs.drop 0).take 25 = ((sq2).plugs.drop 75).take 25)

theorem hM2 (σ : ℕ → F) :
    val (limb sq2 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq2).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA3 (σ : ℕ → F) :
    val (limb sq4 σ 0) = val (limb sq3 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq4).plugs.drop 0).take 25 = ((sq3).plugs.drop 75).take 25)

theorem hM3 (σ : ℕ → F) :
    val (limb sq3 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq3).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA4 (σ : ℕ → F) :
    val (limb sq5 σ 0) = val (limb sq4 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq5).plugs.drop 0).take 25 = ((sq4).plugs.drop 75).take 25)

theorem hM4 (σ : ℕ → F) :
    val (limb sq4 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq4).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA5 (σ : ℕ → F) :
    val (limb sq6 σ 0) = val (limb sq5 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq6).plugs.drop 0).take 25 = ((sq5).plugs.drop 75).take 25)

theorem hM5 (σ : ℕ → F) :
    val (limb sq5 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq5).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA6 (σ : ℕ → F) :
    val (limb sq7 σ 0) = val (limb sq6 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq7).plugs.drop 0).take 25 = ((sq6).plugs.drop 75).take 25)

theorem hM6 (σ : ℕ → F) :
    val (limb sq6 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq6).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA7 (σ : ℕ → F) :
    val (limb sq8 σ 0) = val (limb sq7 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq8).plugs.drop 0).take 25 = ((sq7).plugs.drop 75).take 25)

theorem hM7 (σ : ℕ → F) :
    val (limb sq7 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq7).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA8 (σ : ℕ → F) :
    val (limb sq9 σ 0) = val (limb sq8 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq9).plugs.drop 0).take 25 = ((sq8).plugs.drop 75).take 25)

theorem hM8 (σ : ℕ → F) :
    val (limb sq8 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq8).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA9 (σ : ℕ → F) :
    val (limb sq10 σ 0) = val (limb sq9 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq10).plugs.drop 0).take 25 = ((sq9).plugs.drop 75).take 25)

theorem hM9 (σ : ℕ → F) :
    val (limb sq9 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq9).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA10 (σ : ℕ → F) :
    val (limb sq11 σ 0) = val (limb sq10 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq11).plugs.drop 0).take 25 = ((sq10).plugs.drop 75).take 25)

theorem hM10 (σ : ℕ → F) :
    val (limb sq10 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq10).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA11 (σ : ℕ → F) :
    val (limb sq12 σ 0) = val (limb sq11 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq12).plugs.drop 0).take 25 = ((sq11).plugs.drop 75).take 25)

theorem hM11 (σ : ℕ → F) :
    val (limb sq11 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq11).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA12 (σ : ℕ → F) :
    val (limb sq13 σ 0) = val (limb sq12 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq13).plugs.drop 0).take 25 = ((sq12).plugs.drop 75).take 25)

theorem hM12 (σ : ℕ → F) :
    val (limb sq12 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq12).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA13 (σ : ℕ → F) :
    val (limb sq14 σ 0) = val (limb sq13 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq14).plugs.drop 0).take 25 = ((sq13).plugs.drop 75).take 25)

theorem hM13 (σ : ℕ → F) :
    val (limb sq13 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq13).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hA14 (σ : ℕ → F) :
    val (limb sq15 σ 0) = val (limb sq14 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : ((sq15).plugs.drop 0).take 25 = ((sq14).plugs.drop 75).take 25)

theorem hM14 (σ : ℕ → F) :
    val (limb sq14 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq14).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hM15 (σ : ℕ → F) :
    val (limb sq15 σ 25) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 25) (off' := 25)
    (by decide +kernel : ((sq15).plugs.drop 25).take 25 = ((sq0).plugs.drop 25).take 25)

theorem hqFin (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn fin σ (75 + i) < 2 ^ 82 := by
  intro i hi
  have hb := q_call_bound σ 594 (callAt 594) h rfl (by decide) rfl hi
  have hwin : (fin.plugs.drop 75).take 25 = ((callAt 594).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem haFin (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ i < 25, pn fin σ i < 2 ^ 82 := by
  intro i hi
  have hb := r_call_bound σ 592 (callAt 592) h rfl (by decide) rfl hi
  have hwin : (fin.plugs.drop 0).take 25 = ((callAt 592).plugs.drop 0).take 25 := by
    decide +kernel
  have h0 : pn fin σ i = pn (callAt 592) σ (0 + i) :=
    pn_congr σ (getD_of_window0 hi hwin _)
  rw [h0]
  simpa [Nat.zero_add] using hb

theorem hbFin (σ : ℕ → F) (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82) :
    ∀ i < 25, pn fin σ (25 + i) < 2 ^ 82 := by
  intro i hi
  have hb := hSig i hi
  have hwin : (fin.plugs.drop 25).take 25 = ((sq0).plugs.drop 0).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hmFin (σ : ℕ → F) (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    ∀ i < 25, pn fin σ (50 + i) < 2 ^ 82 := by
  intro i hi
  have hb := hN i hi
  have hwin : (fin.plugs.drop 50).take 25 = ((sq0).plugs.drop 25).take 25 := by
    decide +kernel
  rw [pn_congr σ (getD_of_window hi hwin _)]
  simpa [Nat.zero_add] using hb

theorem hFinA (σ : ℕ → F) : val (limb fin σ 0) = val (limb sq15 σ 75) :=
  val_limb_eq σ (off := 0) (off' := 75)
    (by decide +kernel : (fin.plugs.drop 0).take 25 = ((sq15).plugs.drop 75).take 25)

theorem hFinB (σ : ℕ → F) : val (limb fin σ 25) = val (limb sq0 σ 0) :=
  val_limb_eq σ (off := 25) (off' := 0)
    (by decide +kernel : (fin.plugs.drop 25).take 25 = ((sq0).plugs.drop 0).take 25)

theorem hFinM (σ : ℕ → F) : val (limb fin σ 50) = val (limb sq0 σ 25) :=
  val_limb_eq σ (off := 50) (off' := 25)
    (by decide +kernel : (fin.plugs.drop 50).take 25 = ((sq0).plugs.drop 25).take 25)

theorem id0 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq0 σ 0) * val (limb sq0 σ 0)
      = val (limb sq0 σ 50) * val (limb sq0 σ 25) + val (limb sq0 σ 75) :=
  square_contract σ (n := 548) (c := sq0) h rfl (by decide) rfl (hSig) (hm0 σ hN) (hq0 σ h) (hr0 σ h)

theorem id1 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq1 σ 0) * val (limb sq1 σ 0)
      = val (limb sq1 σ 50) * val (limb sq1 σ 25) + val (limb sq1 σ 75) :=
  square_contract σ (n := 551) (c := sq1) h rfl (by decide) rfl (ha1 σ h) (hm1 σ hN) (hq1 σ h) (hr1 σ h)

theorem id2 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq2 σ 0) * val (limb sq2 σ 0)
      = val (limb sq2 σ 50) * val (limb sq2 σ 25) + val (limb sq2 σ 75) :=
  square_contract σ (n := 554) (c := sq2) h rfl (by decide) rfl (ha2 σ h) (hm2 σ hN) (hq2 σ h) (hr2 σ h)

theorem id3 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq3 σ 0) * val (limb sq3 σ 0)
      = val (limb sq3 σ 50) * val (limb sq3 σ 25) + val (limb sq3 σ 75) :=
  square_contract σ (n := 557) (c := sq3) h rfl (by decide) rfl (ha3 σ h) (hm3 σ hN) (hq3 σ h) (hr3 σ h)

theorem id4 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq4 σ 0) * val (limb sq4 σ 0)
      = val (limb sq4 σ 50) * val (limb sq4 σ 25) + val (limb sq4 σ 75) :=
  square_contract σ (n := 560) (c := sq4) h rfl (by decide) rfl (ha4 σ h) (hm4 σ hN) (hq4 σ h) (hr4 σ h)

theorem id5 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq5 σ 0) * val (limb sq5 σ 0)
      = val (limb sq5 σ 50) * val (limb sq5 σ 25) + val (limb sq5 σ 75) :=
  square_contract σ (n := 563) (c := sq5) h rfl (by decide) rfl (ha5 σ h) (hm5 σ hN) (hq5 σ h) (hr5 σ h)

theorem id6 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq6 σ 0) * val (limb sq6 σ 0)
      = val (limb sq6 σ 50) * val (limb sq6 σ 25) + val (limb sq6 σ 75) :=
  square_contract σ (n := 566) (c := sq6) h rfl (by decide) rfl (ha6 σ h) (hm6 σ hN) (hq6 σ h) (hr6 σ h)

theorem id7 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq7 σ 0) * val (limb sq7 σ 0)
      = val (limb sq7 σ 50) * val (limb sq7 σ 25) + val (limb sq7 σ 75) :=
  square_contract σ (n := 569) (c := sq7) h rfl (by decide) rfl (ha7 σ h) (hm7 σ hN) (hq7 σ h) (hr7 σ h)

theorem id8 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq8 σ 0) * val (limb sq8 σ 0)
      = val (limb sq8 σ 50) * val (limb sq8 σ 25) + val (limb sq8 σ 75) :=
  square_contract σ (n := 572) (c := sq8) h rfl (by decide) rfl (ha8 σ h) (hm8 σ hN) (hq8 σ h) (hr8 σ h)

theorem id9 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq9 σ 0) * val (limb sq9 σ 0)
      = val (limb sq9 σ 50) * val (limb sq9 σ 25) + val (limb sq9 σ 75) :=
  square_contract σ (n := 575) (c := sq9) h rfl (by decide) rfl (ha9 σ h) (hm9 σ hN) (hq9 σ h) (hr9 σ h)

theorem id10 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq10 σ 0) * val (limb sq10 σ 0)
      = val (limb sq10 σ 50) * val (limb sq10 σ 25) + val (limb sq10 σ 75) :=
  square_contract σ (n := 578) (c := sq10) h rfl (by decide) rfl (ha10 σ h) (hm10 σ hN) (hq10 σ h) (hr10 σ h)

theorem id11 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq11 σ 0) * val (limb sq11 σ 0)
      = val (limb sq11 σ 50) * val (limb sq11 σ 25) + val (limb sq11 σ 75) :=
  square_contract σ (n := 581) (c := sq11) h rfl (by decide) rfl (ha11 σ h) (hm11 σ hN) (hq11 σ h) (hr11 σ h)

theorem id12 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq12 σ 0) * val (limb sq12 σ 0)
      = val (limb sq12 σ 50) * val (limb sq12 σ 25) + val (limb sq12 σ 75) :=
  square_contract σ (n := 584) (c := sq12) h rfl (by decide) rfl (ha12 σ h) (hm12 σ hN) (hq12 σ h) (hr12 σ h)

theorem id13 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq13 σ 0) * val (limb sq13 σ 0)
      = val (limb sq13 σ 50) * val (limb sq13 σ 25) + val (limb sq13 σ 75) :=
  square_contract σ (n := 587) (c := sq13) h rfl (by decide) rfl (ha13 σ h) (hm13 σ hN) (hq13 σ h) (hr13 σ h)

theorem id14 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq14 σ 0) * val (limb sq14 σ 0)
      = val (limb sq14 σ 50) * val (limb sq14 σ 25) + val (limb sq14 σ 75) :=
  square_contract σ (n := 590) (c := sq14) h rfl (by decide) rfl (ha14 σ h) (hm14 σ hN) (hq14 σ h) (hr14 σ h)

theorem id15 (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82) :
    val (limb sq15 σ 0) * val (limb sq15 σ 0)
      = val (limb sq15 σ 50) * val (limb sq15 σ 25) + val (limb sq15 σ 75) :=
  square_contract σ (n := 593) (c := sq15) h rfl (by decide) rfl (ha15 σ h) (hm15 σ hN) (hq15 σ h) (hr15 σ h)

/-- **The chain's congruence from the circuit's seventeen calls.** The three limbs'
bounds are the only hypotheses: they are the byte packing's (the `to_bits` calls and
`bytes_to_wide`'s glue rows). Everything else — the q/r bounds, the per-call product
identities, and the chain order — comes from the circuit's rows. -/
theorem chain_congruence (σ : ℕ → F) (h : Sat circuit σ)
    (hSig : ∀ i < 25, pn sq0 σ i < 2 ^ 82)
    (hN : ∀ i < 25, pn sq0 σ (25 + i) < 2 ^ 82)
    (hEm : ∀ i < 25, pn fin σ (100 + i) < 2 ^ 82) :
    chainEm σ ≡ (val (limb sq0 σ 0)) ^ (2 ^ 16 + 1) [ZMOD chainN σ] := by
  have hfinal : chainA σ 16 * chainA σ 0 = val (limb fin σ 75) * chainN σ + chainEm σ := by
    have hf := general_contract σ (n := 596) (c := fin) h rfl (by decide) rfl (haFin σ h) (hbFin σ hSig)
      (hmFin σ hN) (hqFin σ h) hEm
    rw [show chainA σ 16 = val (limb fin σ 0) by rfl,
      show chainA σ 0 = val (limb sq0 σ 0) by rfl,
      show chainN σ = val (limb sq0 σ 25) by rfl,
      show chainEm σ = val (limb fin σ 100) by rfl,
      ← hFinB, ← hFinM]
    exact hf
  have hstep : ∀ j < 16, chainA σ (j + 1) ≡ chainA σ j * chainA σ j [ZMOD chainN σ] := by
    intro j hj
    interval_cases j
    · have hk := id0 σ h hSig hN
      rw [hM0 σ] at hk
      have hgoal : chainA σ 1 ≡ chainA σ 0 * chainA σ 0 [ZMOD chainN σ] := by
        rw [show chainA σ 1 = val (limb sq0 σ 75) by
              rw [show chainA σ 1 = val (limb sq1 σ 0) by rfl,
                hA0 σ],
            show chainA σ 0 = val (limb sq0 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq0 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id1 σ h hSig hN
      rw [hM1 σ] at hk
      have hgoal : chainA σ 2 ≡ chainA σ 1 * chainA σ 1 [ZMOD chainN σ] := by
        rw [show chainA σ 2 = val (limb sq1 σ 75) by
              rw [show chainA σ 2 = val (limb sq2 σ 0) by rfl,
                hA1 σ],
            show chainA σ 1 = val (limb sq1 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq1 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id2 σ h hSig hN
      rw [hM2 σ] at hk
      have hgoal : chainA σ 3 ≡ chainA σ 2 * chainA σ 2 [ZMOD chainN σ] := by
        rw [show chainA σ 3 = val (limb sq2 σ 75) by
              rw [show chainA σ 3 = val (limb sq3 σ 0) by rfl,
                hA2 σ],
            show chainA σ 2 = val (limb sq2 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq2 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id3 σ h hSig hN
      rw [hM3 σ] at hk
      have hgoal : chainA σ 4 ≡ chainA σ 3 * chainA σ 3 [ZMOD chainN σ] := by
        rw [show chainA σ 4 = val (limb sq3 σ 75) by
              rw [show chainA σ 4 = val (limb sq4 σ 0) by rfl,
                hA3 σ],
            show chainA σ 3 = val (limb sq3 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq3 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id4 σ h hSig hN
      rw [hM4 σ] at hk
      have hgoal : chainA σ 5 ≡ chainA σ 4 * chainA σ 4 [ZMOD chainN σ] := by
        rw [show chainA σ 5 = val (limb sq4 σ 75) by
              rw [show chainA σ 5 = val (limb sq5 σ 0) by rfl,
                hA4 σ],
            show chainA σ 4 = val (limb sq4 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq4 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id5 σ h hSig hN
      rw [hM5 σ] at hk
      have hgoal : chainA σ 6 ≡ chainA σ 5 * chainA σ 5 [ZMOD chainN σ] := by
        rw [show chainA σ 6 = val (limb sq5 σ 75) by
              rw [show chainA σ 6 = val (limb sq6 σ 0) by rfl,
                hA5 σ],
            show chainA σ 5 = val (limb sq5 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq5 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id6 σ h hSig hN
      rw [hM6 σ] at hk
      have hgoal : chainA σ 7 ≡ chainA σ 6 * chainA σ 6 [ZMOD chainN σ] := by
        rw [show chainA σ 7 = val (limb sq6 σ 75) by
              rw [show chainA σ 7 = val (limb sq7 σ 0) by rfl,
                hA6 σ],
            show chainA σ 6 = val (limb sq6 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq6 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id7 σ h hSig hN
      rw [hM7 σ] at hk
      have hgoal : chainA σ 8 ≡ chainA σ 7 * chainA σ 7 [ZMOD chainN σ] := by
        rw [show chainA σ 8 = val (limb sq7 σ 75) by
              rw [show chainA σ 8 = val (limb sq8 σ 0) by rfl,
                hA7 σ],
            show chainA σ 7 = val (limb sq7 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq7 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id8 σ h hSig hN
      rw [hM8 σ] at hk
      have hgoal : chainA σ 9 ≡ chainA σ 8 * chainA σ 8 [ZMOD chainN σ] := by
        rw [show chainA σ 9 = val (limb sq8 σ 75) by
              rw [show chainA σ 9 = val (limb sq9 σ 0) by rfl,
                hA8 σ],
            show chainA σ 8 = val (limb sq8 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq8 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id9 σ h hSig hN
      rw [hM9 σ] at hk
      have hgoal : chainA σ 10 ≡ chainA σ 9 * chainA σ 9 [ZMOD chainN σ] := by
        rw [show chainA σ 10 = val (limb sq9 σ 75) by
              rw [show chainA σ 10 = val (limb sq10 σ 0) by rfl,
                hA9 σ],
            show chainA σ 9 = val (limb sq9 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq9 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id10 σ h hSig hN
      rw [hM10 σ] at hk
      have hgoal : chainA σ 11 ≡ chainA σ 10 * chainA σ 10 [ZMOD chainN σ] := by
        rw [show chainA σ 11 = val (limb sq10 σ 75) by
              rw [show chainA σ 11 = val (limb sq11 σ 0) by rfl,
                hA10 σ],
            show chainA σ 10 = val (limb sq10 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq10 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id11 σ h hSig hN
      rw [hM11 σ] at hk
      have hgoal : chainA σ 12 ≡ chainA σ 11 * chainA σ 11 [ZMOD chainN σ] := by
        rw [show chainA σ 12 = val (limb sq11 σ 75) by
              rw [show chainA σ 12 = val (limb sq12 σ 0) by rfl,
                hA11 σ],
            show chainA σ 11 = val (limb sq11 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq11 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id12 σ h hSig hN
      rw [hM12 σ] at hk
      have hgoal : chainA σ 13 ≡ chainA σ 12 * chainA σ 12 [ZMOD chainN σ] := by
        rw [show chainA σ 13 = val (limb sq12 σ 75) by
              rw [show chainA σ 13 = val (limb sq13 σ 0) by rfl,
                hA12 σ],
            show chainA σ 12 = val (limb sq12 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq12 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id13 σ h hSig hN
      rw [hM13 σ] at hk
      have hgoal : chainA σ 14 ≡ chainA σ 13 * chainA σ 13 [ZMOD chainN σ] := by
        rw [show chainA σ 14 = val (limb sq13 σ 75) by
              rw [show chainA σ 14 = val (limb sq14 σ 0) by rfl,
                hA13 σ],
            show chainA σ 13 = val (limb sq13 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq13 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id14 σ h hSig hN
      rw [hM14 σ] at hk
      have hgoal : chainA σ 15 ≡ chainA σ 14 * chainA σ 14 [ZMOD chainN σ] := by
        rw [show chainA σ 15 = val (limb sq14 σ 75) by
              rw [show chainA σ 15 = val (limb sq15 σ 0) by rfl,
                hA14 σ],
            show chainA σ 14 = val (limb sq14 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq14 σ 50), by rw [hk]; ring⟩
      exact hgoal
    · have hk := id15 σ h hSig hN
      rw [hM15 σ] at hk
      have hgoal : chainA σ 16 ≡ chainA σ 15 * chainA σ 15 [ZMOD chainN σ] := by
        rw [show chainA σ 16 = val (limb sq15 σ 75) by
              rw [show chainA σ 16 = val (limb fin σ 0) by rfl,
                hFinA σ],
            show chainA σ 15 = val (limb sq15 σ 0) by rfl,
            show chainN σ = val (limb sq0 σ 25) by rfl]
        rw [Int.modEq_iff_dvd]
        exact ⟨val (limb sq15 σ 50), by rw [hk]; ring⟩
      exact hgoal
  have hc := Xark.Rsa.Chain.chain_seq_range (chainN σ) (chainEm σ) (val (limb fin σ 75))
    (chainA σ) 16 hstep hfinal
  simpa [chainA, accList] using hc

end Xark.Circuits.Rsa2048
