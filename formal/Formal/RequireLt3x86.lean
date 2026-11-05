/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.RequireLt3x86
import Formal.RequireLt

set_option linter.style.header false

/-!
# `xark_bignum::require_lt::<3, 86>`, proven over its exported rows

The harness call on fresh `x` and `m − 1` is the model of `Formal/RequireLt.lean` at
`L = 3, B = 86` (`is_model`). Its production calls:

* `fp!`'s 3 × 86 fields (`assert_canonical`, and `mod_mul` / `sub2` through `mul_divmod`):
  the secp256k1 and secp256r1 base and scalar fields (`weierstrass!`), ed25519's 3 × 86
  `Fp` and `Fq` (`edwards!`, `eddsa_verify`'s scalar check) and `examples/bignum_ops`'s `El`,
  each against its constant `m − 1`;
* `examples/bignum`: `Bignum::mul` against a public `m − 1`, the template itself.

Two `assert_canonical` sites pass `x` as linear combinations instead (LC plugs): ed25519's
`eddsa_verify` scalar check (bit sums) and secp256r1's ECDSA `r, s, e` and `q` (`unpack`'s
limbs). Their `x`-limb bound is caller-enforced; `formal/coverage-allowlist.txt` names the rows.

A constant `m − 1` is this template with constant plugs: `soundness_consts`. It needs
`Assumptions` of the variable `x` plugs only (the caller's): nothing of the constants.
-/

namespace Xark.Templates.RequireLt3x86

open Xark.Template

/-- `x`'s limbs, the first 3 inputs, are below `2^86`; each caller enforces it
(`Formal/RequireLt.lean`). -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins.take 3, v.val < 2 ^ 86

/-- `x ≤ m − 1` as 3-limb numbers in base `2^86`. -/
def Spec (ins : List F) : Prop := RequireLt.Spec 3 86 ins

/-- The exported rows are the model's. -/
theorem is_model : RequireLt.Is 3 86 (RequireLt.plugM 3) template := by decide +kernel

/-- **Soundness**: on `x` with limbs below `2^86`, every satisfying assignment has
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

end Xark.Templates.RequireLt3x86
