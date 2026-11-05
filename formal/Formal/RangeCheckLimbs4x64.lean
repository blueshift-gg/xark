/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RangeCheckLimbs4x64
import Formal.RangeCheckLimbs

set_option linter.style.header false

/-!
# `xark_bignum::range_check_limbs::<4, 64>`, proven over its exported rows

`Formal/Templates/RangeCheckLimbs4x64.lean` (`cargo xtask lean-export range_check_limbs__4x64`)
is `Formal/RangeCheckLimbs.lean`'s model at `L = 4`, `B = 64`.
-/

namespace Xark.Templates.RangeCheckLimbs4x64

open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs

abbrev Spec (ins outs : List F) : Prop := SpecAt 4 64 ins outs

theorem inputs_eq : template.inputs = modelInputs 4 := by decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem rows_eq : template.rows = rows (limbs 4 64) := by decide +kernel

/-- **Soundness.** With no input assumption, every assignment satisfying the rows has each
limb below `2^64`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 4 64 (by norm_num) inputs_eq rows_eq σ h

end Xark.Templates.RangeCheckLimbs4x64
