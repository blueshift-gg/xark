/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RequireLt3x85
import Formal.RequireLt
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# `xark_bignum::require_lt::<3, 85>`, proven over its exported rows

The harness call on fresh `x` and `m − 1` is the model of `Formal/RequireLt.lean` at
`L = 3, B = 85` (`is_model`). Its production calls:

* ed25519's `point_in` (`gadgets/xark-ed25519`): 3 × 85 limbs against `P1_25519_L`.

A constant `m − 1` is this template with constant plugs: `soundness_consts`. It needs
`Assumptions` of the variable `x` plugs only (the caller's): nothing of the constants.
-/

namespace Xark.Templates.RequireLt3x85

open Xark.Template

/-- `x`'s limbs, the first 3 inputs, are below `2^85`; each caller enforces it
(`Formal/RequireLt.lean`). -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins.take 3, v.val < 2 ^ 85

/-- `x ≤ m − 1` as 3-limb numbers in base `2^85`. -/
def Spec (ins : List F) : Prop := RequireLt.Spec 3 85 ins

/-- The exported rows are the model's. -/
theorem is_model : RequireLt.Is 3 85 (RequireLt.plugM 3) template := by decide +kernel

/-- **Soundness**: on `x` with limbs below `2^85`, every satisfying assignment has
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

end Xark.Templates.RequireLt3x85
