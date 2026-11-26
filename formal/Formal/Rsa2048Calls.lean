/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuit
import Formal.GroupedColumnStep
import Formal.RangeCheckQ
import Formal.RangeCheckR
import Formal.RsaCalls
import Formal.Circuits.Rsa2048

set_option linter.style.header false

/-!
# The rsa2048 circuit's gadget calls, from `Circuit.Sat`

`Formal/Circuit.lean`'s `sat_call` hands a call's template its satisfying assignment,
and `Formal/RsaCalls.lean` applies the rsa gadget proofs to one call. This file
lifts that to **all** calls of a template in a circuit: `callsOf t C` collects the
`.call` segments whose template is `t`, and `step_calls_bounded` etc. quantify over it.

For the production circuit that is a statement about every one of its 408
`grouped_column_step` calls, 17 `range_check_q` calls and 16 `range_check_r` calls:
under any satisfying assignment, each carry is below `2^89` and pinned, and each
checked limb is in range. The per-call instances are what the chain's assembly
(`GroupedColumns.carry_spec_of_steps` plus `GroupedCarry.carry_of_sat`) consumes.
-/

namespace Xark.Circuits

open Xark.Circuit Xark.Template Xark.R1cs

/-- The `.call` segments of `C` whose template is exactly `t`. -/
def callsOf (t : Template) (C : Circuit) : List Call :=
  C.filterMap fun s =>
    match s with
    | .call c => if c.t = t then some c else none
    | _ => none

theorem mem_callsOf {t : Template} {C : Circuit} {c : Call} (h : c ∈ callsOf t C) :
    Seg.call c ∈ C ∧ c.t = t := by
  obtain ⟨a, ha, hf⟩ := List.mem_filterMap.mp h
  match a with
  | .glue _ => exact absurd hf (by simp [callsOf])
  | .folded _ _ => exact absurd hf (by simp [callsOf])
  | .call c' =>
    by_cases ht : c'.t = t
    · simp only [callsOf, ht, if_pos] at hf
      have hc : c' = c := by simpa using hf
      subst hc
      exact ⟨ha, ht⟩
    · simp only [callsOf, ht, if_false] at hf
      exact absurd hf (by simp)

variable {C : Circuit} {σ : ℕ → F}

/-- **Every `grouped_column_step` call in a circuit is bounded.** Its output is below
`2^89` and row 0 pins `num = 2^164·k` (`GroupedColumnStep.pin_eval`). -/
theorem step_calls_bounded (h : Sat C σ) :
    ∀ c ∈ callsOf Xark.Templates.GroupedColumnStep.template C,
      (Xark.Templates.GroupedColumnStep.Spec (c.t.ins (c.lift σ))
        (c.t.outs (c.lift σ))) := by
  intro c hc
  obtain ⟨hmem, ht⟩ := mem_callsOf hc
  exact step_call_spec hmem ht σ h

/-- Every `range_check_q` call's 24 limbs are below `2^82` and its top below `2^81`. -/
theorem q_calls_bounded (h : Sat C σ) :
    ∀ c ∈ callsOf Xark.Templates.RangeCheckQ.template C,
      (Xark.Templates.RangeCheckQ.Spec (c.t.ins (c.lift σ))
        (c.t.outs (c.lift σ))) := by
  intro c hc
  obtain ⟨hmem, ht⟩ := mem_callsOf hc
  exact q_call_spec hmem ht σ h

/-- Every `range_check_r` call's 24 limbs are below `2^82` and its top below `2^80`. -/
theorem r_calls_bounded (h : Sat C σ) :
    ∀ c ∈ callsOf Xark.Templates.RangeCheckR.template C,
      (Xark.Templates.RangeCheckR.Spec (c.t.ins (c.lift σ))
        (c.t.outs (c.lift σ))) := by
  intro c hc
  obtain ⟨hmem, ht⟩ := mem_callsOf hc
  exact r_call_spec hmem ht σ h

/-! ### The production circuit's counts -/

/-- `examples/rsa2048`'s circuit: 408 `grouped_column_step` calls (24 per
`grouped_columns`, 17 of those). -/
theorem rsa2048_step_calls :
    (callsOf Xark.Templates.GroupedColumnStep.template
      Xark.Circuits.Rsa2048.circuit).length = 408 := by
  decide +kernel

/-- And 17 `range_check_q` calls (one per `square_lazy`/`fused_final`). -/
theorem rsa2048_q_calls :
    (callsOf Xark.Templates.RangeCheckQ.template Xark.Circuits.Rsa2048.circuit).length = 17 := by
  decide +kernel

/-- And 16 `range_check_r` calls (the squarings; the final fused step pins `em`). -/
theorem rsa2048_r_calls :
    (callsOf Xark.Templates.RangeCheckR.template Xark.Circuits.Rsa2048.circuit).length = 16 := by
  decide +kernel

end Xark.Circuits
