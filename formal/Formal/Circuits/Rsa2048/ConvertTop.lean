/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.ConvertValue

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# The `n_top` row's pieces

Row 9812 pins the top limb's affine expression `limb_24 − Σ bits` to `2^79`. These are
the verified ingredients for that lift: the row's shape, its evaluation as a
`Finset.sum`, the top block's boolean bits, and the cast of the bit sum to the field.
The final `limb_24 = 2^79 + Σ bits ≥ 2^79` assembly is the next step.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt sum_map_range cast_sum)

/-- The `n_top` row's `a`: `(limb_24 − Σ bits) − 2^79`. -/
def topNLC : GLC :=
  ⟨-((2 ^ 79 : ℕ) : F),
    (1, 26347) :: (List.range 79).map (fun i => ((-((2 ^ i : ℕ) : F)), 26348 + 2 * i))⟩

theorem topN_row : growAt 9812 = ⟨topNLC, ⟨1, []⟩, ⟨0, []⟩⟩ := by
  decide +kernel

/-- The row reads `−2^79 + limb_24 − Σ_i 2^i·bit_i`. -/
theorem topN_eval (σ : ℕ → F) :
    topNLC.eval σ =
      -((2 ^ 79 : ℕ) : F) + σ 26347
        - ∑ i ∈ Finset.range 79, ((2 ^ i : ℕ) : F) * σ (26348 + 2 * i) := by
  simp only [topNLC, Xark.R1cs.LC.eval, List.map_cons, List.sum_cons, sum_map_range,
    Function.comp_def, List.map_map]
  simp only [neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- The top block's 79 bits are boolean. -/
theorem topN_bits (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ∀ i < 79, IsBit (σ (26348 + 2 * i)) := by
  have hblock : Sat (gblockRows 26347 26348 80) σ :=
    gblock_sat (s36_sat h) (k := 4826) (by decide +kernel)
  intro i hi
  have hmem : gboolRow 26348 i ∈ gblockRows 26347 26348 80 := by
    rw [gblockRows]
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega : i < 80 - 1), rfl⟩)
  have hrow := hblock _ hmem
  refine isBit_of_mul_self ?_
  simpa [Xark.R1cs.Row.Sat, gboolRow, LC.var, LC.eval, gbit] using hrow

/-- The bit sum, as a natural number, casts to the same field sum the row carries. -/
theorem topN_hcast (σ : ℕ → F) :
    ((∑ i ∈ Finset.range 79, 2 ^ i * (σ (26348 + 2 * i)).val : ℕ) : F) =
      (gacc 26348 80).eval σ := by
  simp only [gacc, Xark.R1cs.LC.eval, List.map_map, Function.comp_def, sum_map_range]
  push_cast
  simp only [ZMod.natCast_zmod_val, gbit, zero_add]

end Xark.Circuits.Rsa2048
