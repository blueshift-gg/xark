/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048Words
import Formal.Circuits.Rsa2048.Verify
import Formal.RangeCheckLimbs17x121

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The 17×121 circuit: plumbing and input-reader bounds

`Formal/Circuits/Rsa2048Words.lean` is the exported whole-number circuit (89 segments).
This file reaches its segments by index the way `Verify.lean` does for the byte path,
and reads the two input-reader `range_check_limbs::<17, 121>` calls' bounds. The rest of
the composition — the `convert_wide` identity and the 25×82 chain — builds on these.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- Segment `n` of the 17×121 circuit. -/
def wseg (n : ℕ) : Seg := Rsa2048Words.circuit.getD n (.glue [])

/-- Segment `n` as a call (the default is unused: every index read below is a `.call`). -/
def wcallAt (n : ℕ) : Call :=
  match wseg n with
  | .call c => c
  | _ => ⟨Xark.Templates.RangeCheckLimbs17x121.template, [], 0⟩

theorem wsegSat {σ : ℕ → F} (h : Sat Rsa2048Words.circuit σ) {n : ℕ}
    (hn : n < Rsa2048Words.circuit.length) : Sat (wseg n).rows σ := by
  rw [wseg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  exact sat_seg (List.getElem_mem hn) h

theorem wcall_sat_of {σ : ℕ → F} (h : Sat Rsa2048Words.circuit σ) (n : ℕ) (c : Call)
    (hseg : wseg n = .call c) (hn : n < Rsa2048Words.circuit.length) :
    c.t.Sat (c.lift σ) := by
  have hs : Sat (wseg n).rows σ := wsegSat h hn
  rw [hseg] at hs
  exact Call.sat_rows hs

/-- The range check's 17 inputs are its plugs. -/
theorem rcl_ins_getD (σ : TVar → F) {j : ℕ} (hj : j < 17) :
    (Xark.Templates.RangeCheckLimbs17x121.template.ins σ).getD j 0 = σ (.plug j) :=
  Xark.Templates.RangeCheckLimbs.getD_ins _
    Xark.Templates.RangeCheckLimbs17x121.inputs_eq σ hj

/-- **A `range_check_limbs::<17, 121>` call bounds each of its 17 plugs.** -/
theorem rcl_call_bound (σ : ℕ → F) (n : ℕ) (c : Call) (h : Sat Rsa2048Words.circuit σ)
    (hseg : wseg n = .call c) (hn : n < Rsa2048Words.circuit.length)
    (ht : c.t = Xark.Templates.RangeCheckLimbs17x121.template) {j : ℕ} (hj : j < 17) :
    pn c σ j < 2 ^ 121 := by
  have hsat := wcall_sat_of h n c hseg hn
  rw [ht] at hsat
  have hs := Xark.Templates.RangeCheckLimbs17x121.soundness (c.lift σ) hsat
  rw [Xark.Templates.RangeCheckLimbs17x121.Spec] at hs
  have hb := hs j hj
  rw [rcl_ins_getD (c.lift σ) hj] at hb
  exact hb

/-- The modulus's 17 limbs, from the input reader. -/
theorem n_limb_bound (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) {j : ℕ} (hj : j < 17) :
    pn (wcallAt 0) σ j < 2 ^ 121 := by
  refine rcl_call_bound σ 0 (wcallAt 0) h ?_ (by decide) ?_ hj
  · rfl
  · rfl

/-- The signature's 17 limbs, from the input reader. -/
theorem sig_limb_bound (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) {j : ℕ} (hj : j < 17) :
    pn (wcallAt 1) σ j < 2 ^ 121 := by
  refine rcl_call_bound σ 1 (wcallAt 1) h ?_ (by decide) ?_ hj
  · rfl
  · rfl

end Xark.Circuits.Rsa2048
