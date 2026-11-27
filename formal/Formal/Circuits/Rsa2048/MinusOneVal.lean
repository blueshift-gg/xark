/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.MinusOneFacts
import Formal.Circuits.Rsa2048.SigLt5

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# The words `minus_one(n)` algebra

`minus_one(n) = n - 1`: per limb `out_i = n_i - borrow_i + W·borrow_{i+1}`, the borrow
chain `borrow_{i+1} = borrow_i·b_i` with `borrow_0 = 1` and `borrow_25 = 0`, so
`Σ out_i·W^i = n_val - 1` (`telescope`). Then `require_lt(sig, out)` gives `sig < n`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
theorem mNF_eq_0 (σ : ℕ → F) : mNF 0 σ = σ 16747 := by
  have hp : (wcallAt 40).plugs.getD (25 + 0) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 16747)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 0) (LC.cst 0))).eval σ = σ 16747
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_1 (σ : ℕ → F) : mNF 1 σ = σ 17147 := by
  have hp : (wcallAt 40).plugs.getD (25 + 1) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 17147)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 1) (LC.cst 0))).eval σ = σ 17147
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_2 (σ : ℕ → F) : mNF 2 σ = σ 17547 := by
  have hp : (wcallAt 40).plugs.getD (25 + 2) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 17547)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 2) (LC.cst 0))).eval σ = σ 17547
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_3 (σ : ℕ → F) : mNF 3 σ = σ 17947 := by
  have hp : (wcallAt 40).plugs.getD (25 + 3) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 17947)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 3) (LC.cst 0))).eval σ = σ 17947
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_4 (σ : ℕ → F) : mNF 4 σ = σ 18347 := by
  have hp : (wcallAt 40).plugs.getD (25 + 4) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 18347)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 4) (LC.cst 0))).eval σ = σ 18347
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_5 (σ : ℕ → F) : mNF 5 σ = σ 18747 := by
  have hp : (wcallAt 40).plugs.getD (25 + 5) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 18747)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 5) (LC.cst 0))).eval σ = σ 18747
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_6 (σ : ℕ → F) : mNF 6 σ = σ 19147 := by
  have hp : (wcallAt 40).plugs.getD (25 + 6) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 19147)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 6) (LC.cst 0))).eval σ = σ 19147
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_7 (σ : ℕ → F) : mNF 7 σ = σ 19547 := by
  have hp : (wcallAt 40).plugs.getD (25 + 7) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 19547)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 7) (LC.cst 0))).eval σ = σ 19547
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_8 (σ : ℕ → F) : mNF 8 σ = σ 19947 := by
  have hp : (wcallAt 40).plugs.getD (25 + 8) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 19947)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 8) (LC.cst 0))).eval σ = σ 19947
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_9 (σ : ℕ → F) : mNF 9 σ = σ 20347 := by
  have hp : (wcallAt 40).plugs.getD (25 + 9) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 20347)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 9) (LC.cst 0))).eval σ = σ 20347
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_10 (σ : ℕ → F) : mNF 10 σ = σ 20747 := by
  have hp : (wcallAt 40).plugs.getD (25 + 10) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 20747)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 10) (LC.cst 0))).eval σ = σ 20747
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_11 (σ : ℕ → F) : mNF 11 σ = σ 21147 := by
  have hp : (wcallAt 40).plugs.getD (25 + 11) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 21147)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 11) (LC.cst 0))).eval σ = σ 21147
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_12 (σ : ℕ → F) : mNF 12 σ = σ 21547 := by
  have hp : (wcallAt 40).plugs.getD (25 + 12) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 21547)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 12) (LC.cst 0))).eval σ = σ 21547
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_13 (σ : ℕ → F) : mNF 13 σ = σ 21947 := by
  have hp : (wcallAt 40).plugs.getD (25 + 13) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 21947)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 13) (LC.cst 0))).eval σ = σ 21947
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_14 (σ : ℕ → F) : mNF 14 σ = σ 22347 := by
  have hp : (wcallAt 40).plugs.getD (25 + 14) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 22347)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 14) (LC.cst 0))).eval σ = σ 22347
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_15 (σ : ℕ → F) : mNF 15 σ = σ 22747 := by
  have hp : (wcallAt 40).plugs.getD (25 + 15) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 22747)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 15) (LC.cst 0))).eval σ = σ 22747
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_16 (σ : ℕ → F) : mNF 16 σ = σ 23147 := by
  have hp : (wcallAt 40).plugs.getD (25 + 16) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 23147)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 16) (LC.cst 0))).eval σ = σ 23147
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_17 (σ : ℕ → F) : mNF 17 σ = σ 23547 := by
  have hp : (wcallAt 40).plugs.getD (25 + 17) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 23547)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 17) (LC.cst 0))).eval σ = σ 23547
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_18 (σ : ℕ → F) : mNF 18 σ = σ 23947 := by
  have hp : (wcallAt 40).plugs.getD (25 + 18) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 23947)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 18) (LC.cst 0))).eval σ = σ 23947
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_19 (σ : ℕ → F) : mNF 19 σ = σ 24347 := by
  have hp : (wcallAt 40).plugs.getD (25 + 19) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 24347)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 19) (LC.cst 0))).eval σ = σ 24347
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_20 (σ : ℕ → F) : mNF 20 σ = σ 24747 := by
  have hp : (wcallAt 40).plugs.getD (25 + 20) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 24747)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 20) (LC.cst 0))).eval σ = σ 24747
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_21 (σ : ℕ → F) : mNF 21 σ = σ 25147 := by
  have hp : (wcallAt 40).plugs.getD (25 + 21) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 25147)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 21) (LC.cst 0))).eval σ = σ 25147
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_22 (σ : ℕ → F) : mNF 22 σ = σ 25547 := by
  have hp : (wcallAt 40).plugs.getD (25 + 22) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 25547)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 22) (LC.cst 0))).eval σ = σ 25547
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_23 (σ : ℕ → F) : mNF 23 σ = σ 25947 := by
  have hp : (wcallAt 40).plugs.getD (25 + 23) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 25947)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 23) (LC.cst 0))).eval σ = σ 25947
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mNF_eq_24 (σ : ℕ → F) : mNF 24 σ = σ 26347 := by
  have hp : (wcallAt 40).plugs.getD (25 + 24) (LC.cst 0) = ⟨0, [((Int.ofNat 1), 26347)]⟩ := by decide +kernel
  show (ZLC.toF ((wcallAt 40).plugs.getD (25 + 24) (LC.cst 0))).eval σ = σ 26347
  rw [hp]
  simp [ZLC.toF, Xark.R1cs.LC.eval]

theorem mhrec_0 (σ : ℕ → F) : mborrowF 1 σ = mborrowF 0 σ * mbF 0 σ := by
  simp [mborrowF, mborrow, mbF, mbLC, mzF, ZLC.toF, Xark.R1cs.LC.eval]

theorem mhrec_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 2 σ = mborrowF 1 σ * mbF 1 σ := by
  have hp := mPq_0 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 3 σ = mborrowF 2 σ * mbF 2 σ := by
  have hp := mPq_1 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 4 σ = mborrowF 3 σ * mbF 3 σ := by
  have hp := mPq_2 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 5 σ = mborrowF 4 σ * mbF 4 σ := by
  have hp := mPq_3 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 6 σ = mborrowF 5 σ * mbF 5 σ := by
  have hp := mPq_4 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 7 σ = mborrowF 6 σ * mbF 6 σ := by
  have hp := mPq_5 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 8 σ = mborrowF 7 σ * mbF 7 σ := by
  have hp := mPq_6 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 9 σ = mborrowF 8 σ * mbF 8 σ := by
  have hp := mPq_7 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 10 σ = mborrowF 9 σ * mbF 9 σ := by
  have hp := mPq_8 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 11 σ = mborrowF 10 σ * mbF 10 σ := by
  have hp := mPq_9 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 12 σ = mborrowF 11 σ * mbF 11 σ := by
  have hp := mPq_10 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 13 σ = mborrowF 12 σ * mbF 12 σ := by
  have hp := mPq_11 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 14 σ = mborrowF 13 σ * mbF 13 σ := by
  have hp := mPq_12 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 15 σ = mborrowF 14 σ * mbF 14 σ := by
  have hp := mPq_13 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 16 σ = mborrowF 15 σ * mbF 15 σ := by
  have hp := mPq_14 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 17 σ = mborrowF 16 σ * mbF 16 σ := by
  have hp := mPq_15 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 18 σ = mborrowF 17 σ * mbF 17 σ := by
  have hp := mPq_16 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 19 σ = mborrowF 18 σ * mbF 18 σ := by
  have hp := mPq_17 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 20 σ = mborrowF 19 σ * mbF 19 σ := by
  have hp := mPq_18 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 21 σ = mborrowF 20 σ * mbF 20 σ := by
  have hp := mPq_19 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 22 σ = mborrowF 21 σ * mbF 21 σ := by
  have hp := mPq_20 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 23 σ = mborrowF 22 σ * mbF 22 σ := by
  have hp := mPq_21 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 24 σ = mborrowF 23 σ * mbF 23 σ := by
  have hp := mPq_22 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm

theorem mhrec_24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 25 σ = mborrowF 24 σ * mbF 24 σ := by
  have hp := mPq_23 σ h
  simpa [mborrowF, mborrow, mbF, mbLC, mzF, mzvar, mnxt, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg] using hp.symm


theorem mborrowF0 (σ : ℕ → F) : mborrowF 0 σ = 1 := by
  simp [mborrowF, mborrow, ZLC.toF, Xark.R1cs.LC.eval]

theorem mborrowF25 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) : mborrowF 25 σ = 0 := by
  have hz := mFq σ h
  simp [mborrowF, mborrow, mnxt, ZLC.toF, Xark.R1cs.LC.eval, hz]

end Xark.Circuits.Rsa2048
