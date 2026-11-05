/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.Unpack
import Formal.Templates.Unpack4
import Formal.Templates.Unpack8K1
import Formal.Templates.Unpack8R1
import Formal.RangeCheckLimbs

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Input packing: `unpack` / `unpack4` and `unpack8` (secp256k1, secp256r1)

The ECDSA verifiers take each 256-bit public value as two 128-bit halves `[lo, hi]` and split
them into limbs: `unpack` (secp256k1) and `unpack4` (secp256r1, the same rows) into 4 × 64
bits, `unpack8` (both) into 8 × 32. The split is `divRem` hints (in `unpack8`'s witness
region, unconstrained there), then `range_check_limbs` over the limbs (the blocks of
`Formal/RangeCheckLimbs.lean`, their bits after the hints' variables), then one row per
half, `half − Σⱼ 2^(Bj)·limbⱼ = 0`.

`soundness`: with no input assumption, every limb is below `2^B` and each half is, as a
natural number, exactly its limbs' value. So each half is below `2¹²⁸` and its limbs are its
unique base-`2^B` digits: the plugs downstream (`fake_glv_check_*`'s `r`, `s`, `e`, the point
coordinates of `on_curve_*` and the curve adds) get canonical limbs.
-/

namespace Xark.Templates.UnpackModel

open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs
open scoped Xark.Templates

/-- `half k = Σⱼ 2^(Bj)·limb j` as one row: the half's plug minus `terms`, times `1`, is `0`. -/
def packRow (k : ℕ) (terms : List (F × TVar)) : Row := ⟨⟨0, (1, .plug k) :: terms⟩, ⟨1, []⟩, ⟨0, []⟩⟩

theorem sat_packRow (k : ℕ) (terms : List (F × TVar)) (σ : TVar → F) :
    (packRow k terms).Sat σ ↔ σ (.plug k) = -(terms.map fun t => t.1 * σ t.2).sum := by
  simp only [Row.Sat, packRow, LC.eval, List.map_cons, List.sum_cons, List.map_nil,
    List.sum_nil, add_zero, mul_one, one_mul, zero_add]
  constructor <;> intro h <;> linear_combination h

/-- A natural number below `r` is determined by its cast. -/
theorem val_of_cast {a : F} {n : ℕ} (h : a = (n : F)) (hn : n < r) : a.val = n := by
  rw [h, ZMod.val_natCast_of_lt hn]

end Xark.Templates.UnpackModel

/-! ### `unpack` / `unpack4`: 4 × 64 -/

namespace Xark.Templates.Unpack64

open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs Xark.Templates.UnpackModel

/-- Limbs `[lo % 2⁶⁴, lo / 2⁶⁴, hi % 2⁶⁴, hi / 2⁶⁴]`: `divRem`'s remainder `wit (2k+1)` then
quotient `wit (2k)`; their bits from variable 4. -/
def blocks : List Block :=
  [(.wit 1, 4, 64), (.wit 0, 132, 64), (.wit 3, 260, 64), (.wit 2, 388, 64)]

def packRows : List Row :=
  [packRow 0 [(-18446744073709551616, .wit 0), (-1, .wit 1)],
    packRow 1 [(-18446744073709551616, .wit 2), (-1, .wit 3)]]

def modelOutputs : List LC := [LC.var (.wit 1), LC.var (.wit 0), LC.var (.wit 3), LC.var (.wit 2)]

/-- The four limbs are below `2⁶⁴` and each half is exactly its two limbs' value. -/
def Spec (ins outs : List F) : Prop :=
  (∀ j < 4, (outs.getD j 0).val < 2 ^ 64) ∧
    ∀ k < 2, (ins.getD k 0).val = (outs.getD (2 * k) 0).val + 2 ^ 64 * (outs.getD (2 * k + 1) 0).val

theorem blocks_le : ∀ b ∈ blocks, b.2.2 ≤ 253 := by decide

theorem two64 : (18446744073709551616 : F) = ((2 ^ 64 : ℕ) : F) := by norm_num

/-- A packing row over limbs below `2⁶⁴` is exact over the naturals. -/
theorem pack_val {p a b : F} (ha : a.val < 2 ^ 64) (hb : b.val < 2 ^ 64)
    (h : p = -(-18446744073709551616 * b + (-1 * a + 0))) : p.val = a.val + 2 ^ 64 * b.val := by
  refine val_of_cast ?_ (lt_of_lt_of_le (by omega) (ToBits.two_pow_lt_r' (n := 129) (by norm_num)).le)
  rw [h, two64]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id]; ring

theorem soundness_of (t : Template) (hi : t.inputs = [LC.var (.plug 0), LC.var (.plug 1)])
    (ho : t.outputs = modelOutputs) (hr : t.rows = rows blocks ++ packRows) (σ : TVar → F)
    (h : t.Sat σ) : Spec (t.ins σ) (t.outs σ) := by
  rw [Template.Sat, hr] at h
  have hb := sound blocks blocks_le σ fun r hr => h r (List.mem_append_left _ hr)
  have hp := fun r (hr : r ∈ packRows) => h r (List.mem_append_right _ hr)
  have l1 := (hb (.wit 1, 4, 64) (by simp [blocks])).1
  have l0 := (hb (.wit 0, 132, 64) (by simp [blocks])).1
  have l3 := (hb (.wit 3, 260, 64) (by simp [blocks])).1
  have l2 := (hb (.wit 2, 388, 64) (by simp [blocks])).1
  have p0 := (sat_packRow 0 [(-18446744073709551616, .wit 0), (-1, .wit 1)] σ).mp
    (hp _ (by simp [packRows]))
  have p1 := (sat_packRow 1 [(-18446744073709551616, .wit 2), (-1, .wit 3)] σ).mp
    (hp _ (by simp [packRows]))
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at p0 p1
  refine ⟨fun j hj => ?_, fun k hk => ?_⟩
  · interval_cases j <;> simpa [Template.outs, ho, modelOutputs]
  · interval_cases k
    · simpa [Template.ins, Template.outs, hi, ho, modelOutputs] using pack_val l1 l0 p0
    · simpa [Template.ins, Template.outs, hi, ho, modelOutputs] using pack_val l3 l2 p1

end Xark.Templates.Unpack64

namespace Xark.Templates.Unpack
open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs Xark.Templates.Unpack64

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1)] := by decide +kernel
theorem outputs_eq : template.outputs = modelOutputs := by decide +kernel
theorem rows_eq : template.rows = rows blocks ++ packRows := by decide +kernel

/-- **Soundness.** With no input assumption, the four limbs are below `2⁶⁴` and each half is
exactly its two limbs' value. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.Unpack

namespace Xark.Templates.Unpack4
open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs Xark.Templates.Unpack64

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1)] := by decide +kernel
theorem outputs_eq : template.outputs = modelOutputs := by decide +kernel
theorem rows_eq : template.rows = rows blocks ++ packRows := by decide +kernel

/-- **Soundness.** As `Unpack.soundness` (the same rows). -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.Unpack4

/-! ### `unpack8`: 8 × 32 -/

namespace Xark.Templates.Unpack32

open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs Xark.Templates.UnpackModel

/-- Each half is split three times by `2³²` (`divRem`, quotient `wit q`, remainder `wit q+1`,
the next split reading the quotient): limbs `[r₀, r₁, r₂, q₂]` per half, bits from variable 12. -/
def blocks : List Block :=
  [(.wit 1, 12, 32), (.wit 3, 76, 32), (.wit 5, 140, 32), (.wit 4, 204, 32),
    (.wit 7, 268, 32), (.wit 9, 332, 32), (.wit 11, 396, 32), (.wit 10, 460, 32)]

def packTerms (o : ℕ) : List (F × TVar) :=
  [(-1, .wit (o + 1)), (-4294967296, .wit (o + 3)), (-79228162514264337593543950336, .wit (o + 4)),
    (-18446744073709551616, .wit (o + 5))]

def packRows : List Row := [packRow 0 (packTerms 0), packRow 1 (packTerms 6)]

def modelOutputs : List LC :=
  [1, 3, 5, 4, 7, 9, 11, 10].map fun w => LC.var (.wit w)

/-- The eight limbs are below `2³²` and each half is exactly its four limbs' value. -/
def Spec (ins outs : List F) : Prop :=
  (∀ j < 8, (outs.getD j 0).val < 2 ^ 32) ∧
    ∀ k < 2, (ins.getD k 0).val = (outs.getD (4 * k) 0).val + 2 ^ 32 * (outs.getD (4 * k + 1) 0).val +
      2 ^ 64 * (outs.getD (4 * k + 2) 0).val + 2 ^ 96 * (outs.getD (4 * k + 3) 0).val

theorem blocks_le : ∀ b ∈ blocks, b.2.2 ≤ 253 := by decide

theorem lits : (4294967296 : F) = ((2 ^ 32 : ℕ) : F) ∧ (18446744073709551616 : F) = ((2 ^ 64 : ℕ) : F) ∧
    (79228162514264337593543950336 : F) = ((2 ^ 96 : ℕ) : F) := by norm_num

theorem pack_val {p a b c d : F} (ha : a.val < 2 ^ 32) (hb : b.val < 2 ^ 32) (hc : c.val < 2 ^ 32)
    (hd : d.val < 2 ^ 32)
    (h : p = -(-1 * a + (-4294967296 * b + (-79228162514264337593543950336 * d +
      (-18446744073709551616 * c + 0))))) :
    p.val = a.val + 2 ^ 32 * b.val + 2 ^ 64 * c.val + 2 ^ 96 * d.val := by
  refine val_of_cast ?_ (lt_of_lt_of_le (by omega) (ToBits.two_pow_lt_r' (n := 129) (by norm_num)).le)
  rw [h, lits.1, lits.2.1, lits.2.2]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id]; ring

theorem soundness_of (t : Template) (hi : t.inputs = [LC.var (.plug 0), LC.var (.plug 1)])
    (ho : t.outputs = modelOutputs) (hr : t.rows = rows blocks ++ packRows) (σ : TVar → F)
    (h : t.Sat σ) : Spec (t.ins σ) (t.outs σ) := by
  rw [Template.Sat, hr] at h
  have hb := sound blocks blocks_le σ fun r hr => h r (List.mem_append_left _ hr)
  have hp := fun r (hr : r ∈ packRows) => h r (List.mem_append_right _ hr)
  have l : ∀ w ∈ [1, 3, 5, 4, 7, 9, 11, 10], (σ (.wit w)).val < 2 ^ 32 := by
    intro w hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hb (.wit 1, 12, 32) (by simp [blocks])).1
    · exact (hb (.wit 3, 76, 32) (by simp [blocks])).1
    · exact (hb (.wit 5, 140, 32) (by simp [blocks])).1
    · exact (hb (.wit 4, 204, 32) (by simp [blocks])).1
    · exact (hb (.wit 7, 268, 32) (by simp [blocks])).1
    · exact (hb (.wit 9, 332, 32) (by simp [blocks])).1
    · exact (hb (.wit 11, 396, 32) (by simp [blocks])).1
    · exact (hb (.wit 10, 460, 32) (by simp [blocks])).1
  have p0 := (sat_packRow 0 (packTerms 0) σ).mp (hp _ (by simp [packRows]))
  have p1 := (sat_packRow 1 (packTerms 6) σ).mp (hp _ (by simp [packRows]))
  simp only [packTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at p0 p1
  refine ⟨fun j hj => ?_, fun k hk => ?_⟩
  · interval_cases j <;> simpa [Template.outs, ho, modelOutputs] using l _ (by simp)
  · interval_cases k
    · simpa [Template.ins, Template.outs, hi, ho, modelOutputs] using
        pack_val (l 1 (by simp)) (l 3 (by simp)) (l 5 (by simp)) (l 4 (by simp)) p0
    · simpa [Template.ins, Template.outs, hi, ho, modelOutputs] using
        pack_val (l 7 (by simp)) (l 9 (by simp)) (l 11 (by simp)) (l 10 (by simp)) p1

end Xark.Templates.Unpack32

namespace Xark.Templates.Unpack8K1
open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs Xark.Templates.Unpack32

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1)] := by decide +kernel
theorem outputs_eq : template.outputs = modelOutputs := by decide +kernel
theorem rows_eq : template.rows = rows blocks ++ packRows := by decide +kernel

/-- **Soundness.** With no input assumption, the eight limbs are below `2³²` and each half is
exactly its four limbs' value. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.Unpack8K1

namespace Xark.Templates.Unpack8R1
open Xark.Template Xark.R1cs Xark.Templates.RangeCheckLimbs Xark.Templates.Unpack32

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1)] := by decide +kernel
theorem outputs_eq : template.outputs = modelOutputs := by decide +kernel
theorem rows_eq : template.rows = rows blocks ++ packRows := by decide +kernel

/-- **Soundness.** With no input assumption, the eight limbs are below `2³²` and each half is
exactly its four limbs' value. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.Unpack8R1
