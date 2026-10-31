/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.MuxpK1
import Formal.Templates.MuxpR1
import Formal.Template
import Formal.Add32

set_option linter.style.header false

/-!
# The point muxes: `xark_secp256k1::muxp`, `xark_secp256r1::muxp`, `xark_ed25519::mux`

`mux(s, a, b)` over `n` limbs emits, per limb `j`, the product row `s · (aⱼ − bⱼ) = wⱼ` and
outputs `bⱼ + wⱼ` (`n = 16` for the secp points, `24` for ed25519's extended points). Its
plugs are `s`, then `a`'s limbs, then `b`'s. `select8` (both curves) is a tree of seven
such calls, and the secp256r1 verifier's per-digit table read is one.

`soundness`: with no input assumption, every satisfying assignment outputs `bⱼ + s·(aⱼ − bⱼ)`;
at a bit `s` that is `a` (`s = 1`) or `b` (`s = 0`) (`select_bit`). That a caller's selector
is a bit is the caller's (its producers are named in `formal/coverage-allowlist.txt`).
-/

namespace Xark.Templates.MuxModel

open Xark.Template Xark.R1cs

def dLC (n j : ℕ) : LC := ⟨0, [(1, .plug (1 + j)), (-1, .plug (n + 1 + j))]⟩

def modelRows (n : ℕ) : List Row :=
  (List.range n).map fun j => ⟨LC.var (.plug 0), dLC n j, LC.var (.wit j)⟩

def modelInputs (n : ℕ) : List LC := (List.range (2 * n + 1)).map fun k => LC.var (.plug k)

def modelOutputs (n : ℕ) : List LC :=
  (List.range n).map fun j => ⟨0, [(1, .plug (n + 1 + j)), (1, .wit j)]⟩

/-- The output limbs are `bⱼ + s·(aⱼ − bⱼ)`. -/
def SpecAt (n : ℕ) (ins outs : List F) : Prop :=
  outs = (List.range n).map fun j =>
    ins.getD (n + 1 + j) 0 + ins.getD 0 0 * (ins.getD (1 + j) 0 - ins.getD (n + 1 + j) 0)

/-- At a bit selector the mux picks one arm. -/
theorem select_bit {n : ℕ} {ins outs : List F} (h : SpecAt n ins outs)
    (hs : Add32.IsBit (ins.getD 0 0)) :
    outs = (List.range n).map fun j =>
      if ins.getD 0 0 = 1 then ins.getD (1 + j) 0 else ins.getD (n + 1 + j) 0 := by
  rw [h]
  generalize ins.getD 0 0 = s at hs ⊢
  refine List.map_congr_left fun j _ => ?_
  rcases hs with rfl | rfl <;> simp

theorem getD_ins (t : Template) {n : ℕ} (hi : t.inputs = modelInputs n) (σ : TVar → F) {k : ℕ}
    (hk : k < 2 * n + 1) : (t.ins σ).getD k 0 = σ (.plug k) := by
  simp [Template.ins, hi, modelInputs, List.getD_eq_getElem?_getD, hk]

theorem soundness_of (t : Template) (n : ℕ) (hi : t.inputs = modelInputs n)
    (ho : t.outputs = modelOutputs n) (hr : t.rows = modelRows n) (σ : TVar → F) (h : t.Sat σ) :
    SpecAt n (t.ins σ) (t.outs σ) := by
  rw [SpecAt, Template.outs, ho, modelOutputs, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have hrow := h _ (by rw [hr]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simp only [Row.Sat, LC.eval_var] at hrow
  simp only [dLC, LC.eval] at hrow
  rw [getD_ins t hi σ (by omega), getD_ins t hi σ (by omega), getD_ins t hi σ (by omega)]
  simp only [Function.comp_apply, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hrow ⊢
  linear_combination -hrow

end Xark.Templates.MuxModel

/-! ### The exported templates -/

namespace Xark.Templates.MuxpK1
open Xark.Template Xark.Templates.MuxModel

abbrev Spec (ins outs : List F) : Prop := SpecAt 16 ins outs

theorem inputs_eq : template.inputs = modelInputs 16 := by decide +kernel
theorem outputs_eq : template.outputs = modelOutputs 16 := by decide +kernel
theorem rows_eq : template.rows = modelRows 16 := by decide +kernel

/-- **Soundness.** With no input assumption the outputs are `bⱼ + s·(aⱼ − bⱼ)`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 16 inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.MuxpK1

namespace Xark.Templates.MuxpR1
open Xark.Template Xark.Templates.MuxModel

abbrev Spec (ins outs : List F) : Prop := SpecAt 16 ins outs

theorem inputs_eq : template.inputs = modelInputs 16 := by decide +kernel
theorem outputs_eq : template.outputs = modelOutputs 16 := by decide +kernel
theorem rows_eq : template.rows = modelRows 16 := by decide +kernel

/-- **Soundness.** With no input assumption the outputs are `bⱼ + s·(aⱼ − bⱼ)`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) :=
  soundness_of template 16 inputs_eq outputs_eq rows_eq σ h

end Xark.Templates.MuxpR1
