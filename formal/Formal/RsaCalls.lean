/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuit
import Formal.GroupedColumnStep
import Formal.RangeCheckQ
import Formal.RangeCheckR

set_option linter.style.header false

/-!
# The rsa2048 circuit's gadget calls, from `Circuit.Sat`

`Formal/Circuit.lean`'s `sat_call` hands a call's template its satisfying assignment;
these lemmas apply the rsa gadget proofs to a call anywhere in a circuit, which is the
first rung of the chain's composition: every `grouped_column_step` call's carry is below
`2^89` and pinned, and every `range_check_q`/`range_check_r` call's limbs are in range.

The glue rows are used directly through `Row.Sat` (`mul_row_value` for the frontend's
product variables); assembling the 24 step calls of one `grouped_columns` into
`GroupedColumns.CarrySpec` is `GroupedColumns.carry_spec_of_steps`, and the per-step
integer identity is `GroupedCarry.carry_of_sat`.
-/

namespace Xark.Circuits

open Xark.Circuit Xark.Template Xark.R1cs

/-- A product row fixes its output variable: `Row.mul A B t` under `σ` means
`σ t = A.eval σ · B.eval σ`. -/
theorem mul_row_value {A B : GLC} {t : ℕ} {σ : ℕ → F} (h : Row.Sat (Row.mul A B t) σ) :
    σ t = A.eval σ * B.eval σ := by
  simpa [Row.Sat, Row.mul, LC.eval, LC.var] using h.symm

/-- **Every `grouped_column_step` call in a circuit is bounded.** Its output is below
`2^89` and row 0 pins `num = 2^164·k` (see `GroupedColumnStep.pin_eval`). -/
theorem step_call_spec {C : Circuit} {c : Call} (hc : Seg.call c ∈ C)
    (ht : c.t = Xark.Templates.GroupedColumnStep.template) (σ : ℕ → F) (h : Sat C σ) :
    Xark.Templates.GroupedColumnStep.Spec (c.t.ins (c.lift σ)) (c.t.outs (c.lift σ)) := by
  have hs : Xark.Templates.GroupedColumnStep.template.Sat (c.lift σ) := by
    have := sat_call hc h
    rwa [ht] at this
  have := Xark.Templates.GroupedColumnStep.soundness _ hs
  rw [ht]
  exact this

/-- Every `range_check_q` call in a circuit puts its 24 limbs below `2^82` and its top
limb below `2^81`. -/
theorem q_call_spec {C : Circuit} {c : Call} (hc : Seg.call c ∈ C)
    (ht : c.t = Xark.Templates.RangeCheckQ.template) (σ : ℕ → F) (h : Sat C σ) :
    Xark.Templates.RangeCheckQ.Spec (c.t.ins (c.lift σ)) (c.t.outs (c.lift σ)) := by
  have hs : Xark.Templates.RangeCheckQ.template.Sat (c.lift σ) := by
    have := sat_call hc h
    rwa [ht] at this
  have := Xark.Templates.RangeCheckQ.soundness _ hs
  rw [ht]
  exact this

/-- Every `range_check_r` call in a circuit puts its 24 limbs below `2^82` and its top
limb below `2^80`. -/
theorem r_call_spec {C : Circuit} {c : Call} (hc : Seg.call c ∈ C)
    (ht : c.t = Xark.Templates.RangeCheckR.template) (σ : ℕ → F) (h : Sat C σ) :
    Xark.Templates.RangeCheckR.Spec (c.t.ins (c.lift σ)) (c.t.outs (c.lift σ)) := by
  have hs : Xark.Templates.RangeCheckR.template.Sat (c.lift σ) := by
    have := sat_call hc h
    rwa [ht] at this
  have := Xark.Templates.RangeCheckR.soundness _ hs
  rw [ht]
  exact this

end Xark.Circuits
