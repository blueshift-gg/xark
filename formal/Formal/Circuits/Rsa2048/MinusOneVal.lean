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

theorem mhnb_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 0 σ = 0 ↔ mbF 0 σ = 1 := by
  have e1 := mE1q_0 σ h
  have e2 := mE2q_0 σ h
  have h1 : mNF 0 σ * mwF 0 σ = mzF 0 σ := by
    simpa [mNF_eq_0, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 0 σ * (1 - mzF 0 σ) = 0 := by
    simpa [mNF_eq_0, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_0 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 0 σ = 0 ∨ mbF 0 σ = 1 := by
  have e1 := mE1q_0 σ h
  have e2 := mE2q_0 σ h
  have hz : mzF 0 σ = 0 ∨ mzF 0 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 1 σ = 0 ↔ mbF 1 σ = 1 := by
  have e1 := mE1q_1 σ h
  have e2 := mE2q_1 σ h
  have h1 : mNF 1 σ * mwF 1 σ = mzF 1 σ := by
    simpa [mNF_eq_1, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 1 σ * (1 - mzF 1 σ) = 0 := by
    simpa [mNF_eq_1, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 1 σ = 0 ∨ mbF 1 σ = 1 := by
  have e1 := mE1q_1 σ h
  have e2 := mE2q_1 σ h
  have hz : mzF 1 σ = 0 ∨ mzF 1 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 2 σ = 0 ↔ mbF 2 σ = 1 := by
  have e1 := mE1q_2 σ h
  have e2 := mE2q_2 σ h
  have h1 : mNF 2 σ * mwF 2 σ = mzF 2 σ := by
    simpa [mNF_eq_2, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 2 σ * (1 - mzF 2 σ) = 0 := by
    simpa [mNF_eq_2, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 2 σ = 0 ∨ mbF 2 σ = 1 := by
  have e1 := mE1q_2 σ h
  have e2 := mE2q_2 σ h
  have hz : mzF 2 σ = 0 ∨ mzF 2 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 3 σ = 0 ↔ mbF 3 σ = 1 := by
  have e1 := mE1q_3 σ h
  have e2 := mE2q_3 σ h
  have h1 : mNF 3 σ * mwF 3 σ = mzF 3 σ := by
    simpa [mNF_eq_3, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 3 σ * (1 - mzF 3 σ) = 0 := by
    simpa [mNF_eq_3, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 3 σ = 0 ∨ mbF 3 σ = 1 := by
  have e1 := mE1q_3 σ h
  have e2 := mE2q_3 σ h
  have hz : mzF 3 σ = 0 ∨ mzF 3 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 4 σ = 0 ↔ mbF 4 σ = 1 := by
  have e1 := mE1q_4 σ h
  have e2 := mE2q_4 σ h
  have h1 : mNF 4 σ * mwF 4 σ = mzF 4 σ := by
    simpa [mNF_eq_4, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 4 σ * (1 - mzF 4 σ) = 0 := by
    simpa [mNF_eq_4, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 4 σ = 0 ∨ mbF 4 σ = 1 := by
  have e1 := mE1q_4 σ h
  have e2 := mE2q_4 σ h
  have hz : mzF 4 σ = 0 ∨ mzF 4 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 5 σ = 0 ↔ mbF 5 σ = 1 := by
  have e1 := mE1q_5 σ h
  have e2 := mE2q_5 σ h
  have h1 : mNF 5 σ * mwF 5 σ = mzF 5 σ := by
    simpa [mNF_eq_5, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 5 σ * (1 - mzF 5 σ) = 0 := by
    simpa [mNF_eq_5, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 5 σ = 0 ∨ mbF 5 σ = 1 := by
  have e1 := mE1q_5 σ h
  have e2 := mE2q_5 σ h
  have hz : mzF 5 σ = 0 ∨ mzF 5 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 6 σ = 0 ↔ mbF 6 σ = 1 := by
  have e1 := mE1q_6 σ h
  have e2 := mE2q_6 σ h
  have h1 : mNF 6 σ * mwF 6 σ = mzF 6 σ := by
    simpa [mNF_eq_6, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 6 σ * (1 - mzF 6 σ) = 0 := by
    simpa [mNF_eq_6, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 6 σ = 0 ∨ mbF 6 σ = 1 := by
  have e1 := mE1q_6 σ h
  have e2 := mE2q_6 σ h
  have hz : mzF 6 σ = 0 ∨ mzF 6 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 7 σ = 0 ↔ mbF 7 σ = 1 := by
  have e1 := mE1q_7 σ h
  have e2 := mE2q_7 σ h
  have h1 : mNF 7 σ * mwF 7 σ = mzF 7 σ := by
    simpa [mNF_eq_7, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 7 σ * (1 - mzF 7 σ) = 0 := by
    simpa [mNF_eq_7, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 7 σ = 0 ∨ mbF 7 σ = 1 := by
  have e1 := mE1q_7 σ h
  have e2 := mE2q_7 σ h
  have hz : mzF 7 σ = 0 ∨ mzF 7 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 8 σ = 0 ↔ mbF 8 σ = 1 := by
  have e1 := mE1q_8 σ h
  have e2 := mE2q_8 σ h
  have h1 : mNF 8 σ * mwF 8 σ = mzF 8 σ := by
    simpa [mNF_eq_8, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 8 σ * (1 - mzF 8 σ) = 0 := by
    simpa [mNF_eq_8, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 8 σ = 0 ∨ mbF 8 σ = 1 := by
  have e1 := mE1q_8 σ h
  have e2 := mE2q_8 σ h
  have hz : mzF 8 σ = 0 ∨ mzF 8 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 9 σ = 0 ↔ mbF 9 σ = 1 := by
  have e1 := mE1q_9 σ h
  have e2 := mE2q_9 σ h
  have h1 : mNF 9 σ * mwF 9 σ = mzF 9 σ := by
    simpa [mNF_eq_9, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 9 σ * (1 - mzF 9 σ) = 0 := by
    simpa [mNF_eq_9, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 9 σ = 0 ∨ mbF 9 σ = 1 := by
  have e1 := mE1q_9 σ h
  have e2 := mE2q_9 σ h
  have hz : mzF 9 σ = 0 ∨ mzF 9 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 10 σ = 0 ↔ mbF 10 σ = 1 := by
  have e1 := mE1q_10 σ h
  have e2 := mE2q_10 σ h
  have h1 : mNF 10 σ * mwF 10 σ = mzF 10 σ := by
    simpa [mNF_eq_10, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 10 σ * (1 - mzF 10 σ) = 0 := by
    simpa [mNF_eq_10, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 10 σ = 0 ∨ mbF 10 σ = 1 := by
  have e1 := mE1q_10 σ h
  have e2 := mE2q_10 σ h
  have hz : mzF 10 σ = 0 ∨ mzF 10 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 11 σ = 0 ↔ mbF 11 σ = 1 := by
  have e1 := mE1q_11 σ h
  have e2 := mE2q_11 σ h
  have h1 : mNF 11 σ * mwF 11 σ = mzF 11 σ := by
    simpa [mNF_eq_11, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 11 σ * (1 - mzF 11 σ) = 0 := by
    simpa [mNF_eq_11, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 11 σ = 0 ∨ mbF 11 σ = 1 := by
  have e1 := mE1q_11 σ h
  have e2 := mE2q_11 σ h
  have hz : mzF 11 σ = 0 ∨ mzF 11 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 12 σ = 0 ↔ mbF 12 σ = 1 := by
  have e1 := mE1q_12 σ h
  have e2 := mE2q_12 σ h
  have h1 : mNF 12 σ * mwF 12 σ = mzF 12 σ := by
    simpa [mNF_eq_12, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 12 σ * (1 - mzF 12 σ) = 0 := by
    simpa [mNF_eq_12, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 12 σ = 0 ∨ mbF 12 σ = 1 := by
  have e1 := mE1q_12 σ h
  have e2 := mE2q_12 σ h
  have hz : mzF 12 σ = 0 ∨ mzF 12 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 13 σ = 0 ↔ mbF 13 σ = 1 := by
  have e1 := mE1q_13 σ h
  have e2 := mE2q_13 σ h
  have h1 : mNF 13 σ * mwF 13 σ = mzF 13 σ := by
    simpa [mNF_eq_13, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 13 σ * (1 - mzF 13 σ) = 0 := by
    simpa [mNF_eq_13, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 13 σ = 0 ∨ mbF 13 σ = 1 := by
  have e1 := mE1q_13 σ h
  have e2 := mE2q_13 σ h
  have hz : mzF 13 σ = 0 ∨ mzF 13 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 14 σ = 0 ↔ mbF 14 σ = 1 := by
  have e1 := mE1q_14 σ h
  have e2 := mE2q_14 σ h
  have h1 : mNF 14 σ * mwF 14 σ = mzF 14 σ := by
    simpa [mNF_eq_14, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 14 σ * (1 - mzF 14 σ) = 0 := by
    simpa [mNF_eq_14, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 14 σ = 0 ∨ mbF 14 σ = 1 := by
  have e1 := mE1q_14 σ h
  have e2 := mE2q_14 σ h
  have hz : mzF 14 σ = 0 ∨ mzF 14 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 15 σ = 0 ↔ mbF 15 σ = 1 := by
  have e1 := mE1q_15 σ h
  have e2 := mE2q_15 σ h
  have h1 : mNF 15 σ * mwF 15 σ = mzF 15 σ := by
    simpa [mNF_eq_15, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 15 σ * (1 - mzF 15 σ) = 0 := by
    simpa [mNF_eq_15, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 15 σ = 0 ∨ mbF 15 σ = 1 := by
  have e1 := mE1q_15 σ h
  have e2 := mE2q_15 σ h
  have hz : mzF 15 σ = 0 ∨ mzF 15 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 16 σ = 0 ↔ mbF 16 σ = 1 := by
  have e1 := mE1q_16 σ h
  have e2 := mE2q_16 σ h
  have h1 : mNF 16 σ * mwF 16 σ = mzF 16 σ := by
    simpa [mNF_eq_16, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 16 σ * (1 - mzF 16 σ) = 0 := by
    simpa [mNF_eq_16, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 16 σ = 0 ∨ mbF 16 σ = 1 := by
  have e1 := mE1q_16 σ h
  have e2 := mE2q_16 σ h
  have hz : mzF 16 σ = 0 ∨ mzF 16 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 17 σ = 0 ↔ mbF 17 σ = 1 := by
  have e1 := mE1q_17 σ h
  have e2 := mE2q_17 σ h
  have h1 : mNF 17 σ * mwF 17 σ = mzF 17 σ := by
    simpa [mNF_eq_17, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 17 σ * (1 - mzF 17 σ) = 0 := by
    simpa [mNF_eq_17, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 17 σ = 0 ∨ mbF 17 σ = 1 := by
  have e1 := mE1q_17 σ h
  have e2 := mE2q_17 σ h
  have hz : mzF 17 σ = 0 ∨ mzF 17 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 18 σ = 0 ↔ mbF 18 σ = 1 := by
  have e1 := mE1q_18 σ h
  have e2 := mE2q_18 σ h
  have h1 : mNF 18 σ * mwF 18 σ = mzF 18 σ := by
    simpa [mNF_eq_18, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 18 σ * (1 - mzF 18 σ) = 0 := by
    simpa [mNF_eq_18, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 18 σ = 0 ∨ mbF 18 σ = 1 := by
  have e1 := mE1q_18 σ h
  have e2 := mE2q_18 σ h
  have hz : mzF 18 σ = 0 ∨ mzF 18 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 19 σ = 0 ↔ mbF 19 σ = 1 := by
  have e1 := mE1q_19 σ h
  have e2 := mE2q_19 σ h
  have h1 : mNF 19 σ * mwF 19 σ = mzF 19 σ := by
    simpa [mNF_eq_19, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 19 σ * (1 - mzF 19 σ) = 0 := by
    simpa [mNF_eq_19, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 19 σ = 0 ∨ mbF 19 σ = 1 := by
  have e1 := mE1q_19 σ h
  have e2 := mE2q_19 σ h
  have hz : mzF 19 σ = 0 ∨ mzF 19 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 20 σ = 0 ↔ mbF 20 σ = 1 := by
  have e1 := mE1q_20 σ h
  have e2 := mE2q_20 σ h
  have h1 : mNF 20 σ * mwF 20 σ = mzF 20 σ := by
    simpa [mNF_eq_20, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 20 σ * (1 - mzF 20 σ) = 0 := by
    simpa [mNF_eq_20, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 20 σ = 0 ∨ mbF 20 σ = 1 := by
  have e1 := mE1q_20 σ h
  have e2 := mE2q_20 σ h
  have hz : mzF 20 σ = 0 ∨ mzF 20 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 21 σ = 0 ↔ mbF 21 σ = 1 := by
  have e1 := mE1q_21 σ h
  have e2 := mE2q_21 σ h
  have h1 : mNF 21 σ * mwF 21 σ = mzF 21 σ := by
    simpa [mNF_eq_21, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 21 σ * (1 - mzF 21 σ) = 0 := by
    simpa [mNF_eq_21, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 21 σ = 0 ∨ mbF 21 σ = 1 := by
  have e1 := mE1q_21 σ h
  have e2 := mE2q_21 σ h
  have hz : mzF 21 σ = 0 ∨ mzF 21 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 22 σ = 0 ↔ mbF 22 σ = 1 := by
  have e1 := mE1q_22 σ h
  have e2 := mE2q_22 σ h
  have h1 : mNF 22 σ * mwF 22 σ = mzF 22 σ := by
    simpa [mNF_eq_22, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 22 σ * (1 - mzF 22 σ) = 0 := by
    simpa [mNF_eq_22, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 22 σ = 0 ∨ mbF 22 σ = 1 := by
  have e1 := mE1q_22 σ h
  have e2 := mE2q_22 σ h
  have hz : mzF 22 σ = 0 ∨ mzF 22 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 23 σ = 0 ↔ mbF 23 σ = 1 := by
  have e1 := mE1q_23 σ h
  have e2 := mE2q_23 σ h
  have h1 : mNF 23 σ * mwF 23 σ = mzF 23 σ := by
    simpa [mNF_eq_23, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 23 σ * (1 - mzF 23 σ) = 0 := by
    simpa [mNF_eq_23, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 23 σ = 0 ∨ mbF 23 σ = 1 := by
  have e1 := mE1q_23 σ h
  have e2 := mE2q_23 σ h
  have hz : mzF 23 σ = 0 ∨ mzF 23 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mhnb_24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mNF 24 σ = 0 ↔ mbF 24 σ = 1 := by
  have e1 := mE1q_24 σ h
  have e2 := mE2q_24 σ h
  have h1 : mNF 24 σ * mwF 24 σ = mzF 24 σ := by
    simpa [mNF_eq_24, mwF, mzF, mwvar, mzvar] using e1
  have h2 : mNF 24 σ * (1 - mzF 24 σ) = 0 := by
    simpa [mNF_eq_24, mzF, mzvar] using e2
  have := isZero_iff h1 h2
  rw [mbF_eq]
  exact this

theorem mbBit_24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mbF 24 σ = 0 ∨ mbF 24 σ = 1 := by
  have e1 := mE1q_24 σ h
  have e2 := mE2q_24 σ h
  have hz : mzF 24 σ = 0 ∨ mzF 24 σ = 1 := by
    simpa [mzF, mzvar] using zBit e1 e2
  rw [mbF_eq]
  exact bBit_of rfl hz

theorem mborrowBit_0 (σ : ℕ → F) : mborrowF 0 σ = 0 ∨ mborrowF 0 σ = 1 := by
  right
  rw [mborrowF0]

theorem mborrowBit_1 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 1 σ = 0 ∨ mborrowF 1 σ = 1 := by
  rw [mhrec_0]
  rcases mborrowBit_0 σ with h0 | h0 <;> rcases mbBit_0 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_2 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 2 σ = 0 ∨ mborrowF 2 σ = 1 := by
  rw [mhrec_1 σ h]
  rcases mborrowBit_1 σ h with h0 | h0 <;> rcases mbBit_1 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_3 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 3 σ = 0 ∨ mborrowF 3 σ = 1 := by
  rw [mhrec_2 σ h]
  rcases mborrowBit_2 σ h with h0 | h0 <;> rcases mbBit_2 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_4 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 4 σ = 0 ∨ mborrowF 4 σ = 1 := by
  rw [mhrec_3 σ h]
  rcases mborrowBit_3 σ h with h0 | h0 <;> rcases mbBit_3 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_5 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 5 σ = 0 ∨ mborrowF 5 σ = 1 := by
  rw [mhrec_4 σ h]
  rcases mborrowBit_4 σ h with h0 | h0 <;> rcases mbBit_4 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_6 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 6 σ = 0 ∨ mborrowF 6 σ = 1 := by
  rw [mhrec_5 σ h]
  rcases mborrowBit_5 σ h with h0 | h0 <;> rcases mbBit_5 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_7 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 7 σ = 0 ∨ mborrowF 7 σ = 1 := by
  rw [mhrec_6 σ h]
  rcases mborrowBit_6 σ h with h0 | h0 <;> rcases mbBit_6 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_8 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 8 σ = 0 ∨ mborrowF 8 σ = 1 := by
  rw [mhrec_7 σ h]
  rcases mborrowBit_7 σ h with h0 | h0 <;> rcases mbBit_7 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_9 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 9 σ = 0 ∨ mborrowF 9 σ = 1 := by
  rw [mhrec_8 σ h]
  rcases mborrowBit_8 σ h with h0 | h0 <;> rcases mbBit_8 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_10 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 10 σ = 0 ∨ mborrowF 10 σ = 1 := by
  rw [mhrec_9 σ h]
  rcases mborrowBit_9 σ h with h0 | h0 <;> rcases mbBit_9 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_11 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 11 σ = 0 ∨ mborrowF 11 σ = 1 := by
  rw [mhrec_10 σ h]
  rcases mborrowBit_10 σ h with h0 | h0 <;> rcases mbBit_10 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_12 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 12 σ = 0 ∨ mborrowF 12 σ = 1 := by
  rw [mhrec_11 σ h]
  rcases mborrowBit_11 σ h with h0 | h0 <;> rcases mbBit_11 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_13 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 13 σ = 0 ∨ mborrowF 13 σ = 1 := by
  rw [mhrec_12 σ h]
  rcases mborrowBit_12 σ h with h0 | h0 <;> rcases mbBit_12 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_14 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 14 σ = 0 ∨ mborrowF 14 σ = 1 := by
  rw [mhrec_13 σ h]
  rcases mborrowBit_13 σ h with h0 | h0 <;> rcases mbBit_13 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_15 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 15 σ = 0 ∨ mborrowF 15 σ = 1 := by
  rw [mhrec_14 σ h]
  rcases mborrowBit_14 σ h with h0 | h0 <;> rcases mbBit_14 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_16 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 16 σ = 0 ∨ mborrowF 16 σ = 1 := by
  rw [mhrec_15 σ h]
  rcases mborrowBit_15 σ h with h0 | h0 <;> rcases mbBit_15 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_17 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 17 σ = 0 ∨ mborrowF 17 σ = 1 := by
  rw [mhrec_16 σ h]
  rcases mborrowBit_16 σ h with h0 | h0 <;> rcases mbBit_16 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_18 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 18 σ = 0 ∨ mborrowF 18 σ = 1 := by
  rw [mhrec_17 σ h]
  rcases mborrowBit_17 σ h with h0 | h0 <;> rcases mbBit_17 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_19 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 19 σ = 0 ∨ mborrowF 19 σ = 1 := by
  rw [mhrec_18 σ h]
  rcases mborrowBit_18 σ h with h0 | h0 <;> rcases mbBit_18 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_20 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 20 σ = 0 ∨ mborrowF 20 σ = 1 := by
  rw [mhrec_19 σ h]
  rcases mborrowBit_19 σ h with h0 | h0 <;> rcases mbBit_19 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_21 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 21 σ = 0 ∨ mborrowF 21 σ = 1 := by
  rw [mhrec_20 σ h]
  rcases mborrowBit_20 σ h with h0 | h0 <;> rcases mbBit_20 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_22 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 22 σ = 0 ∨ mborrowF 22 σ = 1 := by
  rw [mhrec_21 σ h]
  rcases mborrowBit_21 σ h with h0 | h0 <;> rcases mbBit_21 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_23 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 23 σ = 0 ∨ mborrowF 23 σ = 1 := by
  rw [mhrec_22 σ h]
  rcases mborrowBit_22 σ h with h0 | h0 <;> rcases mbBit_22 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_24 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 24 σ = 0 ∨ mborrowF 24 σ = 1 := by
  rw [mhrec_23 σ h]
  rcases mborrowBit_23 σ h with h0 | h0 <;> rcases mbBit_23 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

theorem mborrowBit_25 (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    mborrowF 25 σ = 0 ∨ mborrowF 25 σ = 1 := by
  rw [mhrec_24 σ h]
  rcases mborrowBit_24 σ h with h0 | h0 <;> rcases mbBit_24 σ h with b0 | b0 <;> rw [h0, b0] <;> norm_num

end Xark.Circuits.Rsa2048
