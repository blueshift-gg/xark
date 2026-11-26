/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RangeCheckR
import Formal.RangeDerived
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `xark_rsa::range_check_r`, proven over its exported rows

`Formal/Templates/RangeCheckR.lean` (`cargo xtask lean-export range_check_r`) is
`Formal/RangeDerived.lean`'s model at 24 limbs of 82 bits and a top limb of 80: the
lazy remainder is only proved below `2^2048` (not below `n`), so `24·82 + 80 = 2048`
bits cover it.
-/

namespace Xark.Templates.RangeCheckR

open Xark.Template Xark.R1cs
open Xark.Templates.RangeDerived

/-- The remainder's limbs: 24 of 82 bits, then one of 80. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 25 82 80 ins outs

theorem inputs_eq : template.inputs = modelInputs 25 := by decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem rows_eq : template.rows = rows (limbs 25 82 80) := by
  decide +kernel

/-- **Soundness.** With no input assumption, every assignment satisfying the rows has
24 limbs below `2^82` and the top limb below `2^80`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 25 82 80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) inputs_eq rows_eq σ h

end Xark.Templates.RangeCheckR
