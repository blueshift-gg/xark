/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.ToBits85
import Formal.ToBits

set_option linter.style.header false

/-!
# `Field::to_bits::<85>`, proven over its exported rows

`Formal/Templates/ToBits85.lean` (`cargo xtask lean-export to_bits__85`) is the model
of `Formal/ToBits.lean` at `m = 84`; soundness is that file's
`soundness_of` at width 85.
-/

namespace Xark.Templates.ToBits85

open Xark.Template Xark.R1cs Xark.Templates.ToBits

/-- The spec at width 85. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 85 ins outs

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs 84 := by
  decide +kernel

theorem rows_eq : template.rows = modelRows 84 := by
  decide +kernel

/-- **Soundness.** Any assignment satisfying the exported rows has `x < 2^85` and
outputs exactly the 85 bits of `x`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 84 (by norm_num) inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.ToBits85
