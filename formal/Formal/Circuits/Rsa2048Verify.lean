/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048
import Formal.GroupedColumnsSquareGadget
import Formal.GroupedColumnsGadget
import Formal.RsaChain
import Formal.RangeCheckQ
import Formal.RangeCheckR
import Formal.RsaEm

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Composing `rsa2048` from its seventeen chain calls

The exported circuit hands each chain gadget its plugs as linear combinations over the
circuit's variables. `seg`/`callAt` reach those segments by index (no template
comparison: `List.getD` on the generated literal list), and `segSat` turns a
satisfying assignment into the segment's row satisfaction without traversing the
597-element list. Each square call's contract is
`Formal/GroupedColumnsSquareGadget.soundness`; the terminal call's is the general
gadget's. This file identifies the chain's limb vectors (`a (k+1) = r k`, `m k = n`)
by linear-combination equality, and applies `RsaChain.chain_seq`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- Segment `n` of the circuit. -/
def seg (n : ℕ) : Seg := circuit.getD n (.glue [])

/-- Segment `n` as a call (the default is unused: every index below 597 that this file
reads is a `.call`). -/
def callAt (n : ℕ) : Call :=
  match seg n with
  | .call c => c
  | _ => ⟨Xark.Templates.GroupedColumnsSquare.template, [], 0⟩

theorem segSat {σ : ℕ → F} (h : Sat circuit σ) {n : ℕ} (hn : n < circuit.length) :
    Sat (seg n).rows σ := by
  rw [seg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  exact sat_seg (List.getElem_mem hn) h

/-- The call's plug values as integers. -/
def pv (c : Call) (σ : ℕ → F) (i : ℕ) : ℤ := ((c.lift σ (.plug i)).val : ℤ)

theorem call_sat_of {σ : ℕ → F} (h : Sat circuit σ) (n : ℕ) (c : Call)
    (hseg : seg n = .call c) (hn : n < circuit.length) :
    c.t.Sat (c.lift σ) := by
  have hs : Sat (seg n).rows σ := segSat h hn
  rw [hseg] at hs
  exact Call.sat_rows hs



/-! ### The concrete call list -/

def sq0 : Call := callAt 548
def sq1 : Call := callAt 551
def sq2 : Call := callAt 554
def sq3 : Call := callAt 557
def sq4 : Call := callAt 560
def sq5 : Call := callAt 563
def sq6 : Call := callAt 566
def sq7 : Call := callAt 569
def sq8 : Call := callAt 572
def sq9 : Call := callAt 575
def sq10 : Call := callAt 578
def sq11 : Call := callAt 581
def sq12 : Call := callAt 584
def sq13 : Call := callAt 587
def sq14 : Call := callAt 590
def sq15 : Call := callAt 593
def fin : Call := callAt 596

example : (sq1.plugs.drop 0).take 25 = (sq0.plugs.drop 75).take 25 := by decide +kernel
example : (fin.plugs.drop 0).take 25 = (sq15.plugs.drop 75).take 25 := by decide +kernel
example : (fin.plugs.drop 25).take 25 = (sq0.plugs.drop 0).take 25 := by decide +kernel
example : (fin.plugs.drop 50).take 25 = (sq0.plugs.drop 25).take 25 := by decide +kernel
example : (callAt 546).plugs = (sq0.plugs.drop 50).take 25 := by decide +kernel
example : (callAt 547).plugs = (sq0.plugs.drop 75).take 25 := by decide +kernel

/-! ### Limb values and linear-combination identity -/

/-- The call's plug value as a natural number. -/
def pn (c : Call) (σ : ℕ → F) (i : ℕ) : ℕ := (c.lift σ (.plug i)).val

theorem pv_eq_pn (c : Call) (σ : ℕ → F) (i : ℕ) : pv c σ i = (pn c σ i : ℤ) := rfl

/-- A column of a call: the 25 plug values starting at `off`. -/
def limb (c : Call) (σ : ℕ → F) (off : ℕ) : ℕ → ℤ := fun i => pv c σ (off + i)

theorem getD_of_window0 {l l' : List Xark.Circuit.ZLC} {off' i : ℕ} (hi : i < 25)
    (h : l.take 25 = (l'.drop off').take 25) (d : Xark.Circuit.ZLC) :
    l.getD i d = l'.getD (off' + i) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have h1 : (l.take 25)[i]? = l[i]? := by
    rw [List.getElem?_take, if_pos hi]
  have h2 : ((l'.drop off').take 25)[i]? = l'[off' + i]? := by
    rw [List.getElem?_take, if_pos hi, List.getElem?_drop]
  rw [← h1, h, h2]

theorem pn_congr {c c' : Call} (σ : ℕ → F) {i i' : ℕ}
    (h : c.plugs.getD i (Xark.R1cs.LC.cst 0) = c'.plugs.getD i' (Xark.R1cs.LC.cst 0)) :
    pn c σ i = pn c' σ i' := by
  simp only [pn, Call.lift, Call.env, Xark.Circuit.ZLC.toF]
  rw [h]

theorem pv_congr {c c' : Call} (σ : ℕ → F) {i i' : ℕ}
    (h : c.plugs.getD i (Xark.R1cs.LC.cst 0) = c'.plugs.getD i' (Xark.R1cs.LC.cst 0)) :
    pv c σ i = pv c' σ i' := by
  simp only [pv, Call.lift, Call.env, Xark.Circuit.ZLC.toF]
  rw [h]

/-- `getD` at `off + i` from an equality of the 25-element windows. -/
theorem getD_of_window {l l' : List Xark.Circuit.ZLC} {off off' i : ℕ} (hi : i < 25)
    (h : (l.drop off).take 25 = (l'.drop off').take 25) (d : Xark.Circuit.ZLC) :
    l.getD (off + i) d = l'.getD (off' + i) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have h1 : ((l.drop off).take 25)[i]? = l[off + i]? := by
    rw [List.getElem?_take, if_pos hi, List.getElem?_drop]
  have h2 : ((l'.drop off').take 25)[i]? = l'[off' + i]? := by
    rw [List.getElem?_take, if_pos hi, List.getElem?_drop]
  rw [← h1, h, h2]

theorem val_limb_eq {c c' : Call} (σ : ℕ → F) {off off' : ℕ}
    (h : (c.plugs.drop off).take 25 = (c'.plugs.drop off').take 25) :
    val (limb c σ off) = val (limb c' σ off') := by
  rw [val, val]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [limb, limb, pv_congr σ (getD_of_window (Finset.mem_range.mp hi) h _)]

/-! ### The range-check contracts -/

theorem q_ins_getD (σ : Xark.Template.TVar → F) {j : ℕ} (hj : j < 25) :
    (Xark.Templates.RangeCheckQ.template.ins σ).getD j 0 = σ (.plug j) := by
  rw [Template.ins, Xark.Templates.RangeCheckQ.inputs_eq,
    Xark.Templates.RangeDerived.modelInputs, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
  simp

theorem r_ins_getD (σ : Xark.Template.TVar → F) {j : ℕ} (hj : j < 25) :
    (Xark.Templates.RangeCheckR.template.ins σ).getD j 0 = σ (.plug j) := by
  rw [Template.ins, Xark.Templates.RangeCheckR.inputs_eq,
    Xark.Templates.RangeDerived.modelInputs, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
  simp

theorem q_call_bound (σ : ℕ → F) (n : ℕ) (c : Call)
    (h : Sat circuit σ) (hseg : seg n = .call c) (hn : n < circuit.length)
    (ht : c.t = Xark.Templates.RangeCheckQ.template) {j : ℕ} (hj : j < 25) :
    pn c σ j < 2 ^ 82 := by
  have hsat := call_sat_of h n c hseg hn
  rw [ht] at hsat
  have hs := Xark.Templates.RangeCheckQ.soundness (c.lift σ) hsat
  rw [Xark.Templates.RangeCheckQ.Spec, Xark.Templates.RangeDerived.SpecAt] at hs
  rcases hs with ⟨h1, h2⟩
  by_cases hj24 : j < 24
  · have := h1 j hj24
    rwa [q_ins_getD (c.lift σ) hj] at this
  · have hj24' : j = 24 := by omega
    subst hj24'
    have := h2
    rw [q_ins_getD (c.lift σ) (by norm_num : 24 < 25)] at this
    exact lt_trans this (by norm_num)

theorem r_call_bound (σ : ℕ → F) (n : ℕ) (c : Call)
    (h : Sat circuit σ) (hseg : seg n = .call c) (hn : n < circuit.length)
    (ht : c.t = Xark.Templates.RangeCheckR.template) {j : ℕ} (hj : j < 25) :
    pn c σ j < 2 ^ 82 := by
  have hsat := call_sat_of h n c hseg hn
  rw [ht] at hsat
  have hs := Xark.Templates.RangeCheckR.soundness (c.lift σ) hsat
  rw [Xark.Templates.RangeCheckR.Spec, Xark.Templates.RangeDerived.SpecAt] at hs
  rcases hs with ⟨h1, h2⟩
  by_cases hj24 : j < 24
  · have := h1 j hj24
    rwa [r_ins_getD (c.lift σ) hj] at this
  · have hj24' : j = 24 := by omega
    subst hj24'
    have := h2
    rw [r_ins_getD (c.lift σ) (by norm_num : 24 < 25)] at this
    exact lt_trans this (by norm_num)


/-! ### The per-call contracts -/

theorem val_inLimb_sq (c : Call) (σ : ℕ → F) (off : ℕ) (hoff : off + 25 ≤ 100) :
    val (fun i => Xark.Templates.GroupedColumnsSquare.inLimb
        (Xark.Templates.GroupedColumnsSquare.template.ins (c.lift σ)) (off + i))
      = val (limb c σ off) := by
  rw [val, val]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi25 := Finset.mem_range.mp hi
  rw [Xark.Templates.GroupedColumnsSquare.inLimb,
    Xark.Templates.GroupedColumnsSquare.ins_getD _ (by omega)]
  rfl

theorem val_inLimb_sq0 (c : Call) (σ : ℕ → F) :
    val (fun i => Xark.Templates.GroupedColumnsSquare.inLimb
        (Xark.Templates.GroupedColumnsSquare.template.ins (c.lift σ)) i)
      = val (limb c σ 0) := by
  rw [val, val]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi25 := Finset.mem_range.mp hi
  rw [Xark.Templates.GroupedColumnsSquare.inLimb,
    Xark.Templates.GroupedColumnsSquare.ins_getD _ (by omega)]
  simp [limb, pv, Nat.zero_add]

theorem val_inLimb_gen (c : Call) (σ : ℕ → F) (off : ℕ) (hoff : off + 25 ≤ 125) :
    val (fun i => Xark.Templates.GroupedColumns.inLimb
        (Xark.Templates.GroupedColumns.template.ins (c.lift σ)) (off + i))
      = val (limb c σ off) := by
  rw [val, val]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi25 := Finset.mem_range.mp hi
  rw [Xark.Templates.GroupedColumns.inLimb,
    Xark.Templates.GroupedColumns.ins_getD _ (by omega)]
  rfl

/-- The square call's integer identity, from the four quarter bounds. -/
theorem square_contract (σ : ℕ → F) {n : ℕ} {c : Call}
    (h : Sat circuit σ) (hseg : seg n = .call c) (hn : n < circuit.length)
    (ht : c.t = Xark.Templates.GroupedColumnsSquare.template)
    (ha : ∀ i < 25, pn c σ i < 2 ^ 82)
    (hm : ∀ i < 25, pn c σ (25 + i) < 2 ^ 82)
    (hq : ∀ i < 25, pn c σ (50 + i) < 2 ^ 82)
    (hr : ∀ i < 25, pn c σ (75 + i) < 2 ^ 82) :
    val (limb c σ 0) * val (limb c σ 0)
      = val (limb c σ 50) * val (limb c σ 25) + val (limb c σ 75) := by
  have hsat := call_sat_of h n c hseg hn
  rw [ht] at hsat
  have hspec := Xark.Templates.GroupedColumnsSquare.soundness (c.lift σ) hsat
  have hass : Xark.Templates.GroupedColumnsSquare.Assumptions
      (Xark.Templates.GroupedColumnsSquare.template.ins (c.lift σ)) := by
    intro i hi
    rw [Xark.Templates.GroupedColumnsSquare.ins_getD _ hi]
    by_cases h1 : i < 25
    · exact ha i h1
    · by_cases h2 : i < 50
      · have hi' : i = 25 + (i - 25) := by omega
        rw [hi']; exact hm (i - 25) (by omega)
      · by_cases h3 : i < 75
        · have hi' : i = 50 + (i - 50) := by omega
          rw [hi']; exact hq (i - 50) (by omega)
        · have hi' : i = 75 + (i - 75) := by omega
          rw [hi']; exact hr (i - 75) (by omega)
  have hid := hspec hass
  rw [val_inLimb_sq0 c σ, val_inLimb_sq c σ 50 (by norm_num),
    val_inLimb_sq c σ 25 (by norm_num), val_inLimb_sq c σ 75 (by norm_num)] at hid
  exact hid

/-- The terminal call's integer identity. -/
theorem val_inLimb_gen0 (c : Call) (σ : ℕ → F) :
    val (fun i => Xark.Templates.GroupedColumns.inLimb
        (Xark.Templates.GroupedColumns.template.ins (c.lift σ)) i)
      = val (limb c σ 0) := by
  rw [val, val]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi25 := Finset.mem_range.mp hi
  rw [Xark.Templates.GroupedColumns.inLimb,
    Xark.Templates.GroupedColumns.ins_getD _ (by omega)]
  simp [limb, pv, Nat.zero_add]

theorem general_contract (σ : ℕ → F) {n : ℕ} {c : Call}
    (h : Sat circuit σ) (hseg : seg n = .call c) (hn : n < circuit.length)
    (ht : c.t = Xark.Templates.GroupedColumns.template)
    (ha : ∀ i < 25, pn c σ i < 2 ^ 82)
    (hb : ∀ i < 25, pn c σ (25 + i) < 2 ^ 82)
    (hm : ∀ i < 25, pn c σ (50 + i) < 2 ^ 82)
    (hq : ∀ i < 25, pn c σ (75 + i) < 2 ^ 82)
    (hr : ∀ i < 25, pn c σ (100 + i) < 2 ^ 82) :
    val (limb c σ 0) * val (limb c σ 25)
      = val (limb c σ 75) * val (limb c σ 50) + val (limb c σ 100) := by
  have hsat := call_sat_of h n c hseg hn
  rw [ht] at hsat
  have hspec := Xark.Templates.GroupedColumns.soundness (c.lift σ) hsat
  have hass : Xark.Templates.GroupedColumns.Assumptions
      (Xark.Templates.GroupedColumns.template.ins (c.lift σ)) := by
    intro i hi
    rw [Xark.Templates.GroupedColumns.ins_getD _ hi]
    by_cases h1 : i < 25
    · exact ha i h1
    · by_cases h2 : i < 50
      · have hi' : i = 25 + (i - 25) := by omega
        rw [hi']; exact hb (i - 25) (by omega)
      · by_cases h3 : i < 75
        · have hi' : i = 50 + (i - 50) := by omega
          rw [hi']; exact hm (i - 50) (by omega)
        · by_cases h4 : i < 100
          · have hi' : i = 75 + (i - 75) := by omega
            rw [hi']; exact hq (i - 75) (by omega)
          · have hi' : i = 100 + (i - 100) := by omega
            rw [hi']; exact hr (i - 100) (by omega)
  have hid := hspec hass
  rw [val_inLimb_gen0 c σ, val_inLimb_gen c σ 25 (by norm_num),
    val_inLimb_gen c σ 50 (by norm_num), val_inLimb_gen c σ 75 (by norm_num),
    val_inLimb_gen c σ 100 (by norm_num)] at hid
  exact hid

end Xark.Circuits.Rsa2048
