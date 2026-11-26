/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.SigLt

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The value of `minus_one`'s limbs, field side

`outF i` is the m plug's field value; `houtE_i` evaluates the `hout_i` linear
combination through the LC combinators' evaluations.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

def addG (l m : GLC) : GLC := ⟨l.const + m.const, l.terms ++ m.terms⟩
def negG (l : GLC) : GLC := ⟨-l.const, l.terms.map fun t => (-t.1, t.2)⟩
def smulG (c : F) (l : GLC) : GLC := ⟨c * l.const, l.terms.map fun t => (c * t.1, t.2)⟩

theorem eval_addG (l m : GLC) (σ : ℕ → F) :
    (addG l m).eval σ = l.eval σ + m.eval σ := by
  obtain ⟨a, ts⟩ := l; obtain ⟨b, us⟩ := m
  simp only [addG, Xark.R1cs.LC.eval, List.map_append, List.sum_append]; ring

theorem sum_neg (ts : List (F × ℕ)) (σ : ℕ → F) :
    (ts.map fun t => (-t.1) * σ t.2).sum = -((ts.map fun t => t.1 * σ t.2).sum) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    ring

theorem sum_mul (c : F) (ts : List (F × ℕ)) (σ : ℕ → F) :
    (ts.map fun t => (c * t.1) * σ t.2).sum = c * ((ts.map fun t => t.1 * σ t.2).sum) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    ring

theorem eval_negG (l : GLC) (σ : ℕ → F) : (negG l).eval σ = -(l.eval σ) := by
  obtain ⟨a, ts⟩ := l
  simp only [negG, Xark.R1cs.LC.eval, List.map_map, Function.comp_def]
  rw [sum_neg]
  ring

theorem eval_smulG (c : F) (l : GLC) (σ : ℕ → F) :
    (smulG c l).eval σ = c * (l.eval σ) := by
  obtain ⟨a, ts⟩ := l
  simp only [smulG, Xark.R1cs.LC.eval, List.map_map, Function.comp_def]
  rw [sum_mul]
  ring

/-- The field value of the m plug `i`. -/
def outF (i : ℕ) (σ : ℕ → F) : F :=
  (ZLC.toF ((callAt 545).plugs.getD (25 + i) (LC.cst 0))).eval σ

theorem houtE_0 (σ : ℕ → F) :
    outF 0 σ = nF 0 σ - (ZLC.toF (borrow 0)).eval σ
      + (W : F) * (ZLC.toF (borrow 1)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 0) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 0) (LC.cst 0)))
          (negG (ZLC.toF (borrow 0)))) (smulG (W : F) (ZLC.toF (borrow 1))) := by
    have h := congrArg ZLC.toF (hout_0)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_1 (σ : ℕ → F) :
    outF 1 σ = nF 1 σ - (ZLC.toF (borrow 1)).eval σ
      + (W : F) * (ZLC.toF (borrow 2)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 1) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 1) (LC.cst 0)))
          (negG (ZLC.toF (borrow 1)))) (smulG (W : F) (ZLC.toF (borrow 2))) := by
    have h := congrArg ZLC.toF (hout_1)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_2 (σ : ℕ → F) :
    outF 2 σ = nF 2 σ - (ZLC.toF (borrow 2)).eval σ
      + (W : F) * (ZLC.toF (borrow 3)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 2) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 2) (LC.cst 0)))
          (negG (ZLC.toF (borrow 2)))) (smulG (W : F) (ZLC.toF (borrow 3))) := by
    have h := congrArg ZLC.toF (hout_2)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_3 (σ : ℕ → F) :
    outF 3 σ = nF 3 σ - (ZLC.toF (borrow 3)).eval σ
      + (W : F) * (ZLC.toF (borrow 4)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 3) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 3) (LC.cst 0)))
          (negG (ZLC.toF (borrow 3)))) (smulG (W : F) (ZLC.toF (borrow 4))) := by
    have h := congrArg ZLC.toF (hout_3)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_4 (σ : ℕ → F) :
    outF 4 σ = nF 4 σ - (ZLC.toF (borrow 4)).eval σ
      + (W : F) * (ZLC.toF (borrow 5)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 4) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 4) (LC.cst 0)))
          (negG (ZLC.toF (borrow 4)))) (smulG (W : F) (ZLC.toF (borrow 5))) := by
    have h := congrArg ZLC.toF (hout_4)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_5 (σ : ℕ → F) :
    outF 5 σ = nF 5 σ - (ZLC.toF (borrow 5)).eval σ
      + (W : F) * (ZLC.toF (borrow 6)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 5) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 5) (LC.cst 0)))
          (negG (ZLC.toF (borrow 5)))) (smulG (W : F) (ZLC.toF (borrow 6))) := by
    have h := congrArg ZLC.toF (hout_5)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_6 (σ : ℕ → F) :
    outF 6 σ = nF 6 σ - (ZLC.toF (borrow 6)).eval σ
      + (W : F) * (ZLC.toF (borrow 7)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 6) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 6) (LC.cst 0)))
          (negG (ZLC.toF (borrow 6)))) (smulG (W : F) (ZLC.toF (borrow 7))) := by
    have h := congrArg ZLC.toF (hout_6)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_7 (σ : ℕ → F) :
    outF 7 σ = nF 7 σ - (ZLC.toF (borrow 7)).eval σ
      + (W : F) * (ZLC.toF (borrow 8)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 7) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 7) (LC.cst 0)))
          (negG (ZLC.toF (borrow 7)))) (smulG (W : F) (ZLC.toF (borrow 8))) := by
    have h := congrArg ZLC.toF (hout_7)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_8 (σ : ℕ → F) :
    outF 8 σ = nF 8 σ - (ZLC.toF (borrow 8)).eval σ
      + (W : F) * (ZLC.toF (borrow 9)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 8) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 8) (LC.cst 0)))
          (negG (ZLC.toF (borrow 8)))) (smulG (W : F) (ZLC.toF (borrow 9))) := by
    have h := congrArg ZLC.toF (hout_8)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_9 (σ : ℕ → F) :
    outF 9 σ = nF 9 σ - (ZLC.toF (borrow 9)).eval σ
      + (W : F) * (ZLC.toF (borrow 10)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 9) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 9) (LC.cst 0)))
          (negG (ZLC.toF (borrow 9)))) (smulG (W : F) (ZLC.toF (borrow 10))) := by
    have h := congrArg ZLC.toF (hout_9)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_10 (σ : ℕ → F) :
    outF 10 σ = nF 10 σ - (ZLC.toF (borrow 10)).eval σ
      + (W : F) * (ZLC.toF (borrow 11)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 10) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 10) (LC.cst 0)))
          (negG (ZLC.toF (borrow 10)))) (smulG (W : F) (ZLC.toF (borrow 11))) := by
    have h := congrArg ZLC.toF (hout_10)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_11 (σ : ℕ → F) :
    outF 11 σ = nF 11 σ - (ZLC.toF (borrow 11)).eval σ
      + (W : F) * (ZLC.toF (borrow 12)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 11) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 11) (LC.cst 0)))
          (negG (ZLC.toF (borrow 11)))) (smulG (W : F) (ZLC.toF (borrow 12))) := by
    have h := congrArg ZLC.toF (hout_11)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_12 (σ : ℕ → F) :
    outF 12 σ = nF 12 σ - (ZLC.toF (borrow 12)).eval σ
      + (W : F) * (ZLC.toF (borrow 13)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 12) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 12) (LC.cst 0)))
          (negG (ZLC.toF (borrow 12)))) (smulG (W : F) (ZLC.toF (borrow 13))) := by
    have h := congrArg ZLC.toF (hout_12)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_13 (σ : ℕ → F) :
    outF 13 σ = nF 13 σ - (ZLC.toF (borrow 13)).eval σ
      + (W : F) * (ZLC.toF (borrow 14)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 13) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 13) (LC.cst 0)))
          (negG (ZLC.toF (borrow 13)))) (smulG (W : F) (ZLC.toF (borrow 14))) := by
    have h := congrArg ZLC.toF (hout_13)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_14 (σ : ℕ → F) :
    outF 14 σ = nF 14 σ - (ZLC.toF (borrow 14)).eval σ
      + (W : F) * (ZLC.toF (borrow 15)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 14) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 14) (LC.cst 0)))
          (negG (ZLC.toF (borrow 14)))) (smulG (W : F) (ZLC.toF (borrow 15))) := by
    have h := congrArg ZLC.toF (hout_14)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_15 (σ : ℕ → F) :
    outF 15 σ = nF 15 σ - (ZLC.toF (borrow 15)).eval σ
      + (W : F) * (ZLC.toF (borrow 16)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 15) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 15) (LC.cst 0)))
          (negG (ZLC.toF (borrow 15)))) (smulG (W : F) (ZLC.toF (borrow 16))) := by
    have h := congrArg ZLC.toF (hout_15)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_16 (σ : ℕ → F) :
    outF 16 σ = nF 16 σ - (ZLC.toF (borrow 16)).eval σ
      + (W : F) * (ZLC.toF (borrow 17)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 16) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 16) (LC.cst 0)))
          (negG (ZLC.toF (borrow 16)))) (smulG (W : F) (ZLC.toF (borrow 17))) := by
    have h := congrArg ZLC.toF (hout_16)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_17 (σ : ℕ → F) :
    outF 17 σ = nF 17 σ - (ZLC.toF (borrow 17)).eval σ
      + (W : F) * (ZLC.toF (borrow 18)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 17) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 17) (LC.cst 0)))
          (negG (ZLC.toF (borrow 17)))) (smulG (W : F) (ZLC.toF (borrow 18))) := by
    have h := congrArg ZLC.toF (hout_17)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_18 (σ : ℕ → F) :
    outF 18 σ = nF 18 σ - (ZLC.toF (borrow 18)).eval σ
      + (W : F) * (ZLC.toF (borrow 19)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 18) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 18) (LC.cst 0)))
          (negG (ZLC.toF (borrow 18)))) (smulG (W : F) (ZLC.toF (borrow 19))) := by
    have h := congrArg ZLC.toF (hout_18)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_19 (σ : ℕ → F) :
    outF 19 σ = nF 19 σ - (ZLC.toF (borrow 19)).eval σ
      + (W : F) * (ZLC.toF (borrow 20)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 19) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 19) (LC.cst 0)))
          (negG (ZLC.toF (borrow 19)))) (smulG (W : F) (ZLC.toF (borrow 20))) := by
    have h := congrArg ZLC.toF (hout_19)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_20 (σ : ℕ → F) :
    outF 20 σ = nF 20 σ - (ZLC.toF (borrow 20)).eval σ
      + (W : F) * (ZLC.toF (borrow 21)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 20) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 20) (LC.cst 0)))
          (negG (ZLC.toF (borrow 20)))) (smulG (W : F) (ZLC.toF (borrow 21))) := by
    have h := congrArg ZLC.toF (hout_20)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_21 (σ : ℕ → F) :
    outF 21 σ = nF 21 σ - (ZLC.toF (borrow 21)).eval σ
      + (W : F) * (ZLC.toF (borrow 22)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 21) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 21) (LC.cst 0)))
          (negG (ZLC.toF (borrow 21)))) (smulG (W : F) (ZLC.toF (borrow 22))) := by
    have h := congrArg ZLC.toF (hout_21)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_22 (σ : ℕ → F) :
    outF 22 σ = nF 22 σ - (ZLC.toF (borrow 22)).eval σ
      + (W : F) * (ZLC.toF (borrow 23)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 22) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 22) (LC.cst 0)))
          (negG (ZLC.toF (borrow 22)))) (smulG (W : F) (ZLC.toF (borrow 23))) := by
    have h := congrArg ZLC.toF (hout_22)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_23 (σ : ℕ → F) :
    outF 23 σ = nF 23 σ - (ZLC.toF (borrow 23)).eval σ
      + (W : F) * (ZLC.toF (borrow 24)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 23) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 23) (LC.cst 0)))
          (negG (ZLC.toF (borrow 23)))) (smulG (W : F) (ZLC.toF (borrow 24))) := by
    have h := congrArg ZLC.toF (hout_23)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

theorem houtE_24 (σ : ℕ → F) :
    outF 24 σ = nF 24 σ - (ZLC.toF (borrow 24)).eval σ
      + (W : F) * (ZLC.toF (borrow 25)).eval σ := by
  have hh : ZLC.toF ((callAt 545).plugs.getD (25 + 24) (LC.cst 0))
      = addG (addG (ZLC.toF ((callAt 548).plugs.getD (25 + 24) (LC.cst 0)))
          (negG (ZLC.toF (borrow 24)))) (smulG (W : F) (ZLC.toF (borrow 25))) := by
    have h := congrArg ZLC.toF (hout_24)
    simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg, List.map_append, List.map_map, Function.comp_def] using h
  rw [outF, hh, eval_addG, eval_addG, eval_negG, eval_smulG]
  simp only [nF]
  ring

end Xark.Circuits.Rsa2048
