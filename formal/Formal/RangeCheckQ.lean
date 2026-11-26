/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RangeCheckQ
import Formal.RangeDerived
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `xark_rsa::range_check_q`, proven over its exported rows

`Formal/Templates/RangeCheckQ.lean` (`cargo xtask lean-export range_check_q`) is
`Formal/RangeDerived.lean`'s model at 24 limbs of 82 bits and a top limb of 81: a
lazy quotient of `a·b - r` is below `2^2048` over `n >= 2^2047`, so it is below
`2^2049`, and `2^2049 - 24·82 = 81` bits are left for the top limb. That top width
is what separates it from `range_check_r`.
-/

namespace Xark.Templates.RangeCheckQ

open Xark.Template Xark.R1cs
open Xark.Templates.RangeDerived

/-- The quotient's limbs: 24 of 82 bits, then one of 81. -/
abbrev Spec (ins outs : List F) : Prop := SpecAt 25 82 81 ins outs

theorem inputs_eq : template.inputs = modelInputs 25 := by decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem rows_eq : template.rows = rows (limbs 25 82 81) := by
  decide +kernel

/-- **Soundness.** With no input assumption, every assignment satisfying the rows has
24 limbs below `2^82` and the top limb below `2^81`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 25 82 81 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) inputs_eq rows_eq σ h

end Xark.Templates.RangeCheckQ
