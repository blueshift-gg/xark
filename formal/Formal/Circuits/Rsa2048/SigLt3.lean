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


/-! ### The value formula for the m plugs

`(outF i σ).val = (nF i σ).val − (borrowF i σ).val + 2^82 · (borrowF (i+1) σ).val` over
`ℤ`. `val_formula` is the case split on the borrow bits: `borrow_i = 0` forces
`borrow_{i+1} = 0`; `borrow_i = 1` splits on `b_i`, which is `1` exactly when limb `i` is
zero. Each branch is a `Nat.cast`/`ZMod.val` computation, so no subtraction is carried
through a cast. -/

theorem two_pow_82_lt_r : (2 : ℕ) ^ 82 < Xark.r :=
  lt_trans (by norm_num : (2 : ℕ) ^ 82 < 2 ^ 253) Xark.two_pow_lt_r

theorem val_formula (W : ℕ) (hW0 : 0 < W) (hW : W < Xark.r) (out n bo bn b : F)
    (hout : out = n - bo + (W : F) * bn)
    (hrec : bn = bo * b)
    (hbo : bo = 0 ∨ bo = 1)
    (hb : b = 0 ∨ b = 1)
    (hnb : n = 0 ↔ b = 1) :
    (out.val : ℤ) = (n.val : ℤ) - (bo.val : ℤ) + (W : ℤ) * (bn.val : ℤ) := by
  have hr : 0 < Xark.r := Nat.pos_of_ne_zero (NeZero.ne Xark.r)
  have hnlt : n.val < Xark.r := ZMod.val_lt n
  rcases hbo with hbo | hbo
  · have hbn : bn = 0 := by rw [hrec, hbo]; ring
    subst hbo; subst hbn
    have ho : out = n := by rw [hout]; ring
    rw [ho]
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero]
    ring
  · subst hbo
    rcases hb with hb | hb
    · have hbn : bn = 0 := by rw [hrec, hb]; ring
      have h1 : 1 ≤ n.val := by
        rw [Nat.one_le_iff_ne_zero]
        intro hv
        have hn0 : n = 0 := (ZMod.val_eq_zero n).mp hv
        have hb1 : b = 1 := hnb.mp hn0
        rw [hb] at hb1
        exact zero_ne_one hb1
      have ho : out = n - 1 := by rw [hout, hbn]; ring
      subst hbn
      have ho' : out = ((n.val - 1 : ℕ) : F) := by
        have hcs : ((n.val : F) - 1) = ((n.val - 1 : ℕ) : F) := by
          rw [← Nat.cast_one, ← Nat.cast_sub h1]
        rw [ho]
        conv_lhs => rw [← ZMod.natCast_zmod_val n]
        exact hcs
      rw [ho', ZMod.val_cast_of_lt (by omega)]
      simp only [ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero]
      have hcast : ((n.val - 1 : ℕ) : ℤ) = ((n.val : ℕ) : ℤ) - 1 := by
        rw [Nat.cast_sub h1, Nat.cast_one]
      rw [hcast]
    · have hbn : bn = 1 := by rw [hrec, hb]; ring
      have hn : n = 0 := hnb.mpr hb
      subst hbn; subst hn
      have ho : out = (W : F) - 1 := by rw [hout]; ring
      have hWv : (W : F).val = W := ZMod.val_cast_of_lt hW
      have hsub : ((W : F) - 1).val = W - 1 := by
        rw [ZMod.val_sub (by rw [hWv, ZMod.val_one]; omega), hWv, ZMod.val_one]
      rw [ho, hsub]
      simp only [ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one, mul_one]
      have hcast : ((W - 1 : ℕ) : ℤ) = (W : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ W), Nat.cast_one]
      rw [hcast]
      ring

theorem hrec_0 (σ : ℕ → F) :
    borrowF 1 σ = borrowF 0 σ * bF 0 σ := by
  simp [borrowF, borrow, bLC, bF, zF, zvar, ZLC.toF, Xark.R1cs.LC.eval, sub_eq_add_neg]

theorem hrec_1 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 2 σ = borrowF 1 σ * bF 1 σ := by
  have hp := P_0 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_2 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 3 σ = borrowF 2 σ * bF 2 σ := by
  have hp := P_1 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_3 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 4 σ = borrowF 3 σ * bF 3 σ := by
  have hp := P_2 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_4 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 5 σ = borrowF 4 σ * bF 4 σ := by
  have hp := P_3 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_5 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 6 σ = borrowF 5 σ * bF 5 σ := by
  have hp := P_4 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_6 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 7 σ = borrowF 6 σ * bF 6 σ := by
  have hp := P_5 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_7 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 8 σ = borrowF 7 σ * bF 7 σ := by
  have hp := P_6 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_8 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 9 σ = borrowF 8 σ * bF 8 σ := by
  have hp := P_7 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_9 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 10 σ = borrowF 9 σ * bF 9 σ := by
  have hp := P_8 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_10 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 11 σ = borrowF 10 σ * bF 10 σ := by
  have hp := P_9 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_11 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 12 σ = borrowF 11 σ * bF 11 σ := by
  have hp := P_10 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_12 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 13 σ = borrowF 12 σ * bF 12 σ := by
  have hp := P_11 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_13 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 14 σ = borrowF 13 σ * bF 13 σ := by
  have hp := P_12 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_14 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 15 σ = borrowF 14 σ * bF 14 σ := by
  have hp := P_13 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_15 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 16 σ = borrowF 15 σ * bF 15 σ := by
  have hp := P_14 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_16 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 17 σ = borrowF 16 σ * bF 16 σ := by
  have hp := P_15 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_17 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 18 σ = borrowF 17 σ * bF 17 σ := by
  have hp := P_16 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_18 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 19 σ = borrowF 18 σ * bF 18 σ := by
  have hp := P_17 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_19 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 20 σ = borrowF 19 σ * bF 19 σ := by
  have hp := P_18 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_20 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 21 σ = borrowF 20 σ * bF 20 σ := by
  have hp := P_19 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_21 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 22 σ = borrowF 21 σ * bF 21 σ := by
  have hp := P_20 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_22 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 23 σ = borrowF 22 σ * bF 22 σ := by
  have hp := P_21 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_23 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 24 σ = borrowF 23 σ * bF 23 σ := by
  have hp := P_22 σ h
  simpa [borrowF, bF] using hp.symm

theorem hrec_24 (σ : ℕ → F) (h : Sat circuit σ) :
    borrowF 25 σ = borrowF 24 σ * bF 24 σ := by
  have hp := P_23 σ h
  simpa [borrowF, bF] using hp.symm

theorem hnb_0 (σ : ℕ → F) (h : Sat circuit σ) : nF 0 σ = 0 ↔ bF 0 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_0 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 0 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_0 σ h
    have hb' : (1 - zF 0 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_1 (σ : ℕ → F) (h : Sat circuit σ) : nF 1 σ = 0 ↔ bF 1 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_1 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 1 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_1 σ h
    have hb' : (1 - zF 1 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_2 (σ : ℕ → F) (h : Sat circuit σ) : nF 2 σ = 0 ↔ bF 2 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_2 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 2 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_2 σ h
    have hb' : (1 - zF 2 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_3 (σ : ℕ → F) (h : Sat circuit σ) : nF 3 σ = 0 ↔ bF 3 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_3 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 3 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_3 σ h
    have hb' : (1 - zF 3 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_4 (σ : ℕ → F) (h : Sat circuit σ) : nF 4 σ = 0 ↔ bF 4 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_4 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 4 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_4 σ h
    have hb' : (1 - zF 4 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_5 (σ : ℕ → F) (h : Sat circuit σ) : nF 5 σ = 0 ↔ bF 5 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_5 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 5 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_5 σ h
    have hb' : (1 - zF 5 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_6 (σ : ℕ → F) (h : Sat circuit σ) : nF 6 σ = 0 ↔ bF 6 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_6 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 6 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_6 σ h
    have hb' : (1 - zF 6 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_7 (σ : ℕ → F) (h : Sat circuit σ) : nF 7 σ = 0 ↔ bF 7 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_7 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 7 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_7 σ h
    have hb' : (1 - zF 7 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_8 (σ : ℕ → F) (h : Sat circuit σ) : nF 8 σ = 0 ↔ bF 8 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_8 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 8 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_8 σ h
    have hb' : (1 - zF 8 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_9 (σ : ℕ → F) (h : Sat circuit σ) : nF 9 σ = 0 ↔ bF 9 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_9 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 9 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_9 σ h
    have hb' : (1 - zF 9 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_10 (σ : ℕ → F) (h : Sat circuit σ) : nF 10 σ = 0 ↔ bF 10 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_10 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 10 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_10 σ h
    have hb' : (1 - zF 10 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_11 (σ : ℕ → F) (h : Sat circuit σ) : nF 11 σ = 0 ↔ bF 11 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_11 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 11 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_11 σ h
    have hb' : (1 - zF 11 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_12 (σ : ℕ → F) (h : Sat circuit σ) : nF 12 σ = 0 ↔ bF 12 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_12 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 12 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_12 σ h
    have hb' : (1 - zF 12 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_13 (σ : ℕ → F) (h : Sat circuit σ) : nF 13 σ = 0 ↔ bF 13 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_13 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 13 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_13 σ h
    have hb' : (1 - zF 13 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_14 (σ : ℕ → F) (h : Sat circuit σ) : nF 14 σ = 0 ↔ bF 14 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_14 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 14 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_14 σ h
    have hb' : (1 - zF 14 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_15 (σ : ℕ → F) (h : Sat circuit σ) : nF 15 σ = 0 ↔ bF 15 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_15 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 15 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_15 σ h
    have hb' : (1 - zF 15 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_16 (σ : ℕ → F) (h : Sat circuit σ) : nF 16 σ = 0 ↔ bF 16 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_16 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 16 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_16 σ h
    have hb' : (1 - zF 16 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_17 (σ : ℕ → F) (h : Sat circuit σ) : nF 17 σ = 0 ↔ bF 17 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_17 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 17 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_17 σ h
    have hb' : (1 - zF 17 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_18 (σ : ℕ → F) (h : Sat circuit σ) : nF 18 σ = 0 ↔ bF 18 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_18 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 18 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_18 σ h
    have hb' : (1 - zF 18 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_19 (σ : ℕ → F) (h : Sat circuit σ) : nF 19 σ = 0 ↔ bF 19 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_19 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 19 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_19 σ h
    have hb' : (1 - zF 19 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_20 (σ : ℕ → F) (h : Sat circuit σ) : nF 20 σ = 0 ↔ bF 20 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_20 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 20 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_20 σ h
    have hb' : (1 - zF 20 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_21 (σ : ℕ → F) (h : Sat circuit σ) : nF 21 σ = 0 ↔ bF 21 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_21 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 21 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_21 σ h
    have hb' : (1 - zF 21 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_22 (σ : ℕ → F) (h : Sat circuit σ) : nF 22 σ = 0 ↔ bF 22 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_22 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 22 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_22 σ h
    have hb' : (1 - zF 22 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_23 (σ : ℕ → F) (h : Sat circuit σ) : nF 23 σ = 0 ↔ bF 23 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_23 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 23 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_23 σ h
    have hb' : (1 - zF 23 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem hnb_24 (σ : ℕ → F) (h : Sat circuit σ) : nF 24 σ = 0 ↔ bF 24 σ = 1 := by
  constructor
  · intro hn
    have e1 := E1_24 σ h
    rw [hn, zero_mul] at e1
    have hz : zF 24 σ = 0 := e1.symm
    simp [bF, hz]
  · intro hb
    have e2 := E2_24 σ h
    have hb' : (1 - zF 24 σ) = 1 := hb
    rw [hb', mul_one] at e2
    exact e2

theorem outVal_0 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 0 σ).val : ℤ) = ((nF 0 σ).val : ℤ) - ((borrowF 0 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 1 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 0 σ) (nF 0 σ) (borrowF 0 σ) (borrowF 1 σ) (bF 0 σ)
    (houtE_0 σ) (hrec_0 σ) (borrowBit_0 σ) (bBit_0 σ h) (hnb_0 σ h)

theorem outVal_1 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 1 σ).val : ℤ) = ((nF 1 σ).val : ℤ) - ((borrowF 1 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 2 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 1 σ) (nF 1 σ) (borrowF 1 σ) (borrowF 2 σ) (bF 1 σ)
    (houtE_1 σ) (hrec_1 σ h) (borrowBit_1 σ h) (bBit_1 σ h) (hnb_1 σ h)

theorem outVal_2 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 2 σ).val : ℤ) = ((nF 2 σ).val : ℤ) - ((borrowF 2 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 3 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 2 σ) (nF 2 σ) (borrowF 2 σ) (borrowF 3 σ) (bF 2 σ)
    (houtE_2 σ) (hrec_2 σ h) (borrowBit_2 σ h) (bBit_2 σ h) (hnb_2 σ h)

theorem outVal_3 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 3 σ).val : ℤ) = ((nF 3 σ).val : ℤ) - ((borrowF 3 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 4 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 3 σ) (nF 3 σ) (borrowF 3 σ) (borrowF 4 σ) (bF 3 σ)
    (houtE_3 σ) (hrec_3 σ h) (borrowBit_3 σ h) (bBit_3 σ h) (hnb_3 σ h)

theorem outVal_4 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 4 σ).val : ℤ) = ((nF 4 σ).val : ℤ) - ((borrowF 4 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 5 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 4 σ) (nF 4 σ) (borrowF 4 σ) (borrowF 5 σ) (bF 4 σ)
    (houtE_4 σ) (hrec_4 σ h) (borrowBit_4 σ h) (bBit_4 σ h) (hnb_4 σ h)

theorem outVal_5 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 5 σ).val : ℤ) = ((nF 5 σ).val : ℤ) - ((borrowF 5 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 6 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 5 σ) (nF 5 σ) (borrowF 5 σ) (borrowF 6 σ) (bF 5 σ)
    (houtE_5 σ) (hrec_5 σ h) (borrowBit_5 σ h) (bBit_5 σ h) (hnb_5 σ h)

theorem outVal_6 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 6 σ).val : ℤ) = ((nF 6 σ).val : ℤ) - ((borrowF 6 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 7 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 6 σ) (nF 6 σ) (borrowF 6 σ) (borrowF 7 σ) (bF 6 σ)
    (houtE_6 σ) (hrec_6 σ h) (borrowBit_6 σ h) (bBit_6 σ h) (hnb_6 σ h)

theorem outVal_7 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 7 σ).val : ℤ) = ((nF 7 σ).val : ℤ) - ((borrowF 7 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 8 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 7 σ) (nF 7 σ) (borrowF 7 σ) (borrowF 8 σ) (bF 7 σ)
    (houtE_7 σ) (hrec_7 σ h) (borrowBit_7 σ h) (bBit_7 σ h) (hnb_7 σ h)

theorem outVal_8 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 8 σ).val : ℤ) = ((nF 8 σ).val : ℤ) - ((borrowF 8 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 9 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 8 σ) (nF 8 σ) (borrowF 8 σ) (borrowF 9 σ) (bF 8 σ)
    (houtE_8 σ) (hrec_8 σ h) (borrowBit_8 σ h) (bBit_8 σ h) (hnb_8 σ h)

theorem outVal_9 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 9 σ).val : ℤ) = ((nF 9 σ).val : ℤ) - ((borrowF 9 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 10 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 9 σ) (nF 9 σ) (borrowF 9 σ) (borrowF 10 σ) (bF 9 σ)
    (houtE_9 σ) (hrec_9 σ h) (borrowBit_9 σ h) (bBit_9 σ h) (hnb_9 σ h)

theorem outVal_10 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 10 σ).val : ℤ) = ((nF 10 σ).val : ℤ) - ((borrowF 10 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 11 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 10 σ) (nF 10 σ) (borrowF 10 σ) (borrowF 11 σ) (bF 10 σ)
    (houtE_10 σ) (hrec_10 σ h) (borrowBit_10 σ h) (bBit_10 σ h) (hnb_10 σ h)

theorem outVal_11 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 11 σ).val : ℤ) = ((nF 11 σ).val : ℤ) - ((borrowF 11 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 12 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 11 σ) (nF 11 σ) (borrowF 11 σ) (borrowF 12 σ) (bF 11 σ)
    (houtE_11 σ) (hrec_11 σ h) (borrowBit_11 σ h) (bBit_11 σ h) (hnb_11 σ h)

theorem outVal_12 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 12 σ).val : ℤ) = ((nF 12 σ).val : ℤ) - ((borrowF 12 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 13 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 12 σ) (nF 12 σ) (borrowF 12 σ) (borrowF 13 σ) (bF 12 σ)
    (houtE_12 σ) (hrec_12 σ h) (borrowBit_12 σ h) (bBit_12 σ h) (hnb_12 σ h)

theorem outVal_13 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 13 σ).val : ℤ) = ((nF 13 σ).val : ℤ) - ((borrowF 13 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 14 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 13 σ) (nF 13 σ) (borrowF 13 σ) (borrowF 14 σ) (bF 13 σ)
    (houtE_13 σ) (hrec_13 σ h) (borrowBit_13 σ h) (bBit_13 σ h) (hnb_13 σ h)

theorem outVal_14 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 14 σ).val : ℤ) = ((nF 14 σ).val : ℤ) - ((borrowF 14 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 15 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 14 σ) (nF 14 σ) (borrowF 14 σ) (borrowF 15 σ) (bF 14 σ)
    (houtE_14 σ) (hrec_14 σ h) (borrowBit_14 σ h) (bBit_14 σ h) (hnb_14 σ h)

theorem outVal_15 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 15 σ).val : ℤ) = ((nF 15 σ).val : ℤ) - ((borrowF 15 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 16 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 15 σ) (nF 15 σ) (borrowF 15 σ) (borrowF 16 σ) (bF 15 σ)
    (houtE_15 σ) (hrec_15 σ h) (borrowBit_15 σ h) (bBit_15 σ h) (hnb_15 σ h)

theorem outVal_16 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 16 σ).val : ℤ) = ((nF 16 σ).val : ℤ) - ((borrowF 16 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 17 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 16 σ) (nF 16 σ) (borrowF 16 σ) (borrowF 17 σ) (bF 16 σ)
    (houtE_16 σ) (hrec_16 σ h) (borrowBit_16 σ h) (bBit_16 σ h) (hnb_16 σ h)

theorem outVal_17 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 17 σ).val : ℤ) = ((nF 17 σ).val : ℤ) - ((borrowF 17 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 18 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 17 σ) (nF 17 σ) (borrowF 17 σ) (borrowF 18 σ) (bF 17 σ)
    (houtE_17 σ) (hrec_17 σ h) (borrowBit_17 σ h) (bBit_17 σ h) (hnb_17 σ h)

theorem outVal_18 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 18 σ).val : ℤ) = ((nF 18 σ).val : ℤ) - ((borrowF 18 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 19 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 18 σ) (nF 18 σ) (borrowF 18 σ) (borrowF 19 σ) (bF 18 σ)
    (houtE_18 σ) (hrec_18 σ h) (borrowBit_18 σ h) (bBit_18 σ h) (hnb_18 σ h)

theorem outVal_19 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 19 σ).val : ℤ) = ((nF 19 σ).val : ℤ) - ((borrowF 19 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 20 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 19 σ) (nF 19 σ) (borrowF 19 σ) (borrowF 20 σ) (bF 19 σ)
    (houtE_19 σ) (hrec_19 σ h) (borrowBit_19 σ h) (bBit_19 σ h) (hnb_19 σ h)

theorem outVal_20 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 20 σ).val : ℤ) = ((nF 20 σ).val : ℤ) - ((borrowF 20 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 21 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 20 σ) (nF 20 σ) (borrowF 20 σ) (borrowF 21 σ) (bF 20 σ)
    (houtE_20 σ) (hrec_20 σ h) (borrowBit_20 σ h) (bBit_20 σ h) (hnb_20 σ h)

theorem outVal_21 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 21 σ).val : ℤ) = ((nF 21 σ).val : ℤ) - ((borrowF 21 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 22 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 21 σ) (nF 21 σ) (borrowF 21 σ) (borrowF 22 σ) (bF 21 σ)
    (houtE_21 σ) (hrec_21 σ h) (borrowBit_21 σ h) (bBit_21 σ h) (hnb_21 σ h)

theorem outVal_22 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 22 σ).val : ℤ) = ((nF 22 σ).val : ℤ) - ((borrowF 22 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 23 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 22 σ) (nF 22 σ) (borrowF 22 σ) (borrowF 23 σ) (bF 22 σ)
    (houtE_22 σ) (hrec_22 σ h) (borrowBit_22 σ h) (bBit_22 σ h) (hnb_22 σ h)

theorem outVal_23 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 23 σ).val : ℤ) = ((nF 23 σ).val : ℤ) - ((borrowF 23 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 24 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 23 σ) (nF 23 σ) (borrowF 23 σ) (borrowF 24 σ) (bF 23 σ)
    (houtE_23 σ) (hrec_23 σ h) (borrowBit_23 σ h) (bBit_23 σ h) (hnb_23 σ h)

theorem outVal_24 (σ : ℕ → F) (h : Sat circuit σ) :
    ((outF 24 σ).val : ℤ) = ((nF 24 σ).val : ℤ) - ((borrowF 24 σ).val : ℤ)
      + (2 : ℤ) ^ 82 * ((borrowF 25 σ).val : ℤ) := by
  exact val_formula (W := 2 ^ 82) (by norm_num) two_pow_82_lt_r
    (outF 24 σ) (nF 24 σ) (borrowF 24 σ) (borrowF 25 σ) (bF 24 σ)
    (houtE_24 σ) (hrec_24 σ h) (borrowBit_24 σ h) (bBit_24 σ h) (hnb_24 σ h)



end Xark.Circuits.Rsa2048
