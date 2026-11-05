/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.ToBits98
import Formal.ToBits

set_option linter.style.header false

/-!
# `Field::to_bits::<98>`, proven over its exported rows

`Formal/Templates/ToBits98.lean` (`cargo xtask lean-export to_bits__98`) is the model
of `Formal/ToBits.lean` at `m = 97`; soundness is that file's
`soundness_of` at width 98.
-/

namespace Xark.Templates.ToBits98

open Xark.Template Xark.R1cs Xark.Templates.ToBits

/-- The spec at width 98. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 98 ins outs

theorem inputs_eq : template.inputs = [LC.var (.plug 0)] := by
  decide +kernel

theorem outputs_eq : template.outputs = modelOutputs 97 := by
  decide +kernel

theorem rows_eq : template.rows = modelRows 97 := by
  decide +kernel

/-- **Soundness.** Any assignment satisfying the exported rows has `x < 2^98` and
outputs exactly the 98 bits of `x`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 97 (by norm_num) inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.ToBits98
