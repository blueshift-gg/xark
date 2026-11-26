/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RangeCheckLimbs17x121
import Formal.RangeCheckLimbs
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# `xark_bignum::range_check_limbs::<17, 121>`, proven over its exported rows

`Formal/Templates/RangeCheckLimbs17x121.lean`
(`cargo xtask lean-export range_check_limbs__17x121`) is
`Formal/RangeCheckLimbs.lean`'s model at `L = 17`, `B = 121`.
-/

namespace Xark.Templates.RangeCheckLimbs17x121

open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs

abbrev Spec (ins outs : List F) : Prop := SpecAt 17 121 ins outs

theorem inputs_eq : template.inputs = modelInputs 17 := by decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem rows_eq : template.rows = rows (limbs 17 121) := by decide +kernel

/-- **Soundness.** With no input assumption, every assignment satisfying the rows has
each limb below `2¹²¹`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 17 121 (by norm_num) inputs_eq rows_eq σ h

end Xark.Templates.RangeCheckLimbs17x121
