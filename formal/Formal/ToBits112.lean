/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.ToBits112
import Formal.ToBits
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# `Field::to_bits::<112>`, proven over its exported rows

`Formal/Templates/ToBits112.lean` (`cargo xtask lean-export to_bits__112`) is the
model of `Formal/ToBits.lean` at `m = 111`; soundness is that file's
`soundness_of` at width 112.
-/

namespace Xark.Templates.ToBits112

open Xark.Template Xark.R1cs Xark.Templates.ToBits

/-- The spec at width 112. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 112 ins outs

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs 111 := by
  decide +kernel

theorem rows_eq : template.rows = modelRows 111 := by
  decide +kernel

/-- **Soundness.** Any assignment satisfying the exported rows has `x < 2^112` and
outputs exactly the 112 bits of `x`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 111 (by norm_num) inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.ToBits112
