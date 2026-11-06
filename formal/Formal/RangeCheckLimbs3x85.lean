/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RangeCheckLimbs3x85
import Formal.RangeCheckLimbs
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# `xark_bignum::range_check_limbs::<3, 85>`, proven over its exported rows

`Formal/Templates/RangeCheckLimbs3x85.lean` (`cargo xtask lean-export range_check_limbs__3x85`)
is `Formal/RangeCheckLimbs.lean`'s model at `L = 3`, `B = 86`.
-/

namespace Xark.Templates.RangeCheckLimbs3x85

open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs

abbrev Spec (ins outs : List F) : Prop := SpecAt 3 85 ins outs

theorem inputs_eq : template.inputs = modelInputs 3 := by decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem rows_eq : template.rows = rows (limbs 3 85) := by decide +kernel

/-- **Soundness.** With no input assumption, every assignment satisfying the rows has each
limb below `2^85`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 3 85 (by norm_num) inputs_eq rows_eq σ h

end Xark.Templates.RangeCheckLimbs3x85
