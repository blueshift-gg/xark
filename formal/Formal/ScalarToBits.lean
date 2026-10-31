/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.ScalarToBits
import Formal.RangeCheckLimbs

set_option linter.style.header false

/-!
# `xark_bignum::scalar_to_bits`, proven over its exported rows

`scalar_to_bits(u)` decomposes a 3 × 86-bit scalar into `86 + 86 + 84` pinned bits: the
range-check blocks of `Formal/RangeCheckLimbs.lean` over its three plugs, whose bit variables
are its outputs. ed25519's verifier feeds `S` and the digest through it, and its bits feed
`fake_glv_check_25519`'s `limbs64` plugs and `assert_scalar_below_order`'s `require_lt`.

`soundness`: with no input assumption, `u₀, u₁ < 2⁸⁶`, `u₂ < 2⁸⁴` and the outputs are their
bits, little-endian, limb after limb (so `u < 2²⁵⁶` and every output is a bit).
-/

namespace Xark.Templates.ScalarToBits

open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs

def blocks : List Block := [(.plug 0, 0, 86), (.plug 1, 172, 86), (.plug 2, 344, 84)]

def modelOutputs : List LC :=
  blocks.flatMap fun b => (List.range b.2.2).map fun i => LC.var (.wit (b.2.1 + 2 * i))

def width (j : ℕ) : ℕ := if j = 2 then 84 else 86

/-- Limb `j` is below `2^(width j)`. -/
def Assumptions (ins : List F) : Prop := ∀ j < 3, (ins.getD j 0).val < 2 ^ width j

/-- The limbs are in range and the outputs are their bits, limb after limb. -/
def Spec (ins outs : List F) : Prop :=
  Assumptions ins ∧
    outs = (List.range 3).flatMap fun j => (List.range (width j)).map (bitOf (ins.getD j 0))

theorem inputs_eq : template.inputs = modelInputs 3 := by decide +kernel
theorem outputs_eq : template.outputs = modelOutputs := by decide +kernel
theorem rows_eq : template.rows = rows blocks := by decide +kernel

theorem blocks_eq : blocks = (List.range 3).map fun j => (.plug j, 172 * j, width j) := by decide

/-- **Soundness.** With no input assumption, the limbs are in range and the outputs are their
bits. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [Template.Sat, rows_eq] at h
  have hb := sound blocks (by decide) σ h
  have hin : ∀ j < 3, (template.ins σ).getD j 0 = σ (.plug j) := fun j hj =>
    getD_ins template inputs_eq σ hj
  have hold : ∀ j < 3, Holds σ (.plug j, 172 * j, width j) := fun j hj =>
    hb _ (by rw [blocks_eq]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  refine ⟨fun j hj => by rw [hin j hj]; exact (hold j hj).1, ?_⟩
  rw [Template.outs, outputs_eq, modelOutputs, blocks_eq, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun j hj => ?_
  have hj := List.mem_range.mp hj
  rw [List.map_map, hin j hj]
  refine List.map_congr_left fun i hi => ?_
  simpa using (hold j hj).2 i (List.mem_range.mp hi)

end Xark.Templates.ScalarToBits
