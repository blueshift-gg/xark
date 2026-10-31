/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RangeCheckLimbs8x32
import Formal.RangeCheckLimbs

set_option linter.style.header false

/-!
# `xark_bignum::range_check_limbs::<8, 32>`, proven over its exported rows

`Formal/Templates/RangeCheckLimbs8x32.lean` (`cargo xtask lean-export range_check_limbs__8x32`)
is `Formal/RangeCheckLimbs.lean`'s model at `L = 8`, `B = 32`.
-/

namespace Xark.Templates.RangeCheckLimbs8x32

open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs

abbrev Spec (ins outs : List F) : Prop := SpecAt 8 32 ins outs

theorem inputs_eq : template.inputs = modelInputs 8 := by decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem rows_eq : template.rows = rows (limbs 8 32) := by decide +kernel

/-- **Soundness.** With no input assumption, every assignment satisfying the rows has each
limb below `2³²`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 8 32 (by norm_num) inputs_eq rows_eq σ h

end Xark.Templates.RangeCheckLimbs8x32
