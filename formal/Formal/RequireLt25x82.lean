/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RequireLt25x82
import Formal.RequireLt
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# `xark_bignum::require_lt::<25, 82>`, proven over its exported rows

The harness call on fresh `x` and `m − 1` is the model of `Formal/RequireLt.lean` at
`L = 25, B = 82` (`is_model`). Production's RSA-2048 `verify_wide` passes `m − 1` from
`minus_one`, a linear combination; the template's soundness assumes nothing of
`m − 1`, so the LC plugs are sound. A constant `m − 1` is this template with
constant plugs: `soundness_consts`.
-/

namespace Xark.Templates.RequireLt25x82

open Xark.Template

/-- `x`'s limbs, the first 25 inputs, are below `2^82`; each caller enforces it
(`Formal/RequireLt.lean`). -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins.take 25, v.val < 2 ^ 82

/-- `x ≤ m − 1` as 25-limb numbers in base `2^82`. -/
def Spec (ins : List F) : Prop := RequireLt.Spec 25 82 ins

/-- The exported rows are the model's. -/
theorem is_model : RequireLt.Is 25 82 (RequireLt.plugM 25) template := by decide +kernel

/-- **Soundness**: on `x` with limbs below `2^82`, every satisfying assignment has
`x ≤ m − 1`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) :=
  RequireLt.soundness is_model (by norm_num) (by norm_num) (by norm_num) σ
    (RequireLt.assumptions_of_take ha) h

/-- **Soundness with constant plugs** `c` (production's constant `m − 1`). -/
theorem soundness_consts (c : List (ℕ × F)) (σ : TVar → F)
    (ha : Assumptions ((template.inst (Template.consts c)).ins σ))
    (h : (template.inst (Template.consts c)).Sat σ) :
    Spec ((template.inst (Template.consts c)).ins σ) :=
  Template.soundness_inst (S := fun ins _ => Spec ins) template
    (fun σ ha h => soundness σ ha h) _ σ ha h

end Xark.Templates.RequireLt25x82
