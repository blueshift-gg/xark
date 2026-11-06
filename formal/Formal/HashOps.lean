/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.Xor3
import Formal.Templates.Maj3
import Formal.Templates.Chi
import Formal.Templates.Ch
import Formal.Add32
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# `xark_bits::xor3`, `maj3`, `chi` and `ch`, proven over their exported rows

`Formal/Templates/{Xor3,Maj3,Chi,Ch}.lean` are the R1CS the frontend emits for one call
of each on three fresh variables `a, b, c` (`cargo xtask lean-export xor3` …): one row
each.

* `xor3`: `(z + 2a + 2b + 7c)·(a + b − 4c + 1) = 6a + 6b − 24c`, `z` hinted as bit 0 of
  `a + b + c` (Verified-zkEVM/clean PR #395, zkGolf T1);
* `maj3`: `(z + a + b − 9c + 3)·(a + b + 6c − 4) = −12`, `z` hinted as bit 1 of `a + b + c`;
* `chi`: `(z + 3a − b − c)·(4a + b + c − 3) = 4a + 2b`, `z` hinted as bit 1 of
  `2a + 1 − b + c` (Keccak's χ bit `a ⊕ (¬b ∧ c)`, zkGolf f8fd1e03);
* `ch`: `a·(b − c) = w`, output `c + w` (SHA-256's `Ch`, bellman `sha256_ch`).

For each, on input bits (`Assumptions`):

* `soundness`: every assignment satisfying the row outputs exactly the target bit. The
  first three rows are linear in `z` with a multiplier `a + b − 4c + 1`, `a + b + 6c − 4`
  or `4a + b + c − 3` that is one of `±1, ±2, ±3, ±4` on `{0,1}³`, so nonzero in `F`: the
  hinted `z` has exactly one value (bug checklist 8, the hint-bit bug class). `ch`'s
  output is `c + a·(b − c)` for any inputs (`sat_iff`).
* `outs_isBit`: the outputs are bits, so they discharge the bit `Assumptions` of the
  gadgets they feed (`lean-export --coverage`).

The input assumption (bits) is the caller's, and every production caller passes values
proven to be bits: in `xark-sha256`, the message bytes' `to_bits::<8>` bits, IV and
padding constants, and `reduce` outputs (`Reduce.spec_isBit`), rotated or shifted (a
shift fills constant `0`s); in `xark-keccak`, the bytes' bits, constant padding and
capacity lanes, and `xor3`/`chi` outputs, or `x`/`1 − x` of them after ι's folded XOR
with a constant; in `xark-blake2s`, the IV constants and `xor32`/`add32`/`reduce`
outputs. `lean-export --coverage` discharges the calls whose plugs are linear
combinations from these producers' `outs_isBit` / `spec_isBit`; the rest are plain
variables, the same producers' outputs.
-/

open Xark.Template Xark.R1cs
open Xark.Templates.Add32 (IsBit)

namespace Xark.HashOps

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- The three inputs are bits. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

theorem natCast_ne_zero {k : ℕ} (h0 : 0 < k) (hk : k < 2 ^ 253) : (k : F) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact lt_irrefl r (lt_of_le_of_lt (Nat.le_of_dvd h0 h) (lt_trans hk two_pow_lt_r))

theorem ne1 : (1 : F) ≠ 0 := one_ne_zero
theorem ne2 : (2 : F) ≠ 0 := by exact_mod_cast natCast_ne_zero (k := 2) (by norm_num) (by norm_num)
theorem ne3 : (3 : F) ≠ 0 := by exact_mod_cast natCast_ne_zero (k := 3) (by norm_num) (by norm_num)
theorem ne4 : (4 : F) ≠ 0 := by exact_mod_cast natCast_ne_zero (k := 4) (by norm_num) (by norm_num)

/-- A row linear in `w` with a nonzero multiplier pins `w`. -/
theorem pin {m w v : F} (hm : m ≠ 0) (h : m * (w - v) = 0) : w = v :=
  sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hm)

/-- Solve `h`, a row whose only unknown is `w`, for the goal `w = v`: the multiplier is
one of `±1 … ±4`. -/
macro "pin_row " h:ident : tactic => `(tactic| first
  | exact pin ne1 (by linear_combination $h:ident)
  | exact pin (neg_ne_zero.mpr ne1) (by linear_combination $h:ident)
  | exact pin ne2 (by linear_combination $h:ident)
  | exact pin (neg_ne_zero.mpr ne2) (by linear_combination $h:ident)
  | exact pin ne3 (by linear_combination $h:ident)
  | exact pin (neg_ne_zero.mpr ne3) (by linear_combination $h:ident)
  | exact pin ne4 (by linear_combination $h:ident)
  | exact pin (neg_ne_zero.mpr ne4) (by linear_combination $h:ident))

/-- The three inputs of a call on fresh variables. -/
theorem bits3 {p q s : F} (ha : Assumptions [p, q, s]) : IsBit p ∧ IsBit q ∧ IsBit s :=
  ⟨ha _ (by simp), ha _ (by simp), ha _ (by simp)⟩

/-- A spec's target bit, from a natural number that is `0` or `1`. -/
def natBit (n : ℕ) : F := if n = 1 then 1 else 0

theorem natBit_isBit (n : ℕ) : IsBit (natBit n) := by
  unfold natBit; split
  · exact Or.inr rfl
  · exact Or.inl rfl

end Xark.HashOps

namespace Xark.Templates.Xor3

open Xark.HashOps

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The input assumption: the three inputs are bits. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The spec: the result is the bit `a ⊕ b ⊕ c`. -/
def Spec (ins outs : List F) : Prop :=
  outs = [natBit (((ins.getD 0 0).val + (ins.getD 1 0).val + (ins.getD 2 0).val) % 2)]

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1), LC.var (.plug 2)] := by
  decide +kernel

theorem outputs_eq : template.outputs = [LC.var (.wit 0)] := by
  decide +kernel

theorem rows_eq : template.rows =
    [⟨⟨0, [(2, .plug 0), (2, .plug 1), (7, .plug 2), (1, .wit 0)]⟩,
      ⟨1, [(1, .plug 0), (1, .plug 1), (-4, .plug 2)]⟩,
      ⟨0, [(6, .plug 0), (6, .plug 1), (-24, .plug 2)]⟩⟩] := by
  decide +kernel

theorem ins_eq (σ : TVar → F) :
    template.ins σ = [σ (.plug 0), σ (.plug 1), σ (.plug 2)] := by
  simp [Template.ins, inputs_eq]

theorem outs_eq (σ : TVar → F) : template.outs σ = [σ (.wit 0)] := by
  simp [Template.outs, outputs_eq]

theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    (σ (.wit 0) + 2 * σ (.plug 0) + 2 * σ (.plug 1) + 7 * σ (.plug 2)) *
        (σ (.plug 0) + σ (.plug 1) - 4 * σ (.plug 2) + 1) =
      6 * σ (.plug 0) + 6 * σ (.plug 1) - 24 * σ (.plug 2) := by
  simp only [Template.Sat, rows_eq, Xark.R1cs.Sat, List.mem_singleton, forall_eq, Row.Sat,
    LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  constructor <;> intro h <;> linear_combination h

/-- **Soundness.** On input bits, every assignment satisfying the row outputs
`a ⊕ b ⊕ c`: the hinted bit has no other value. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  have hr := (sat_iff σ).mp h
  rw [ins_eq] at ha ⊢
  rw [outs_eq]
  obtain ⟨h0, h1, h2⟩ := bits3 ha
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rw [h0, h1, h2] at hr <;>
    simp only [Spec, List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2, ZMod.val_zero,
      ZMod.val_one, natBit, List.cons.injEq, and_true] <;> norm_num <;> pin_row hr

/-- **Its output is a bit** (on input bits). -/
theorem outs_isBit (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    ∀ v ∈ template.outs σ, IsBit v := by
  have hs := soundness σ ha h
  rw [Spec] at hs
  rw [hs]
  intro v hv
  rw [List.mem_singleton] at hv
  exact hv ▸ natBit_isBit _

end Xark.Templates.Xor3

namespace Xark.Templates.Maj3

open Xark.HashOps

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The input assumption: the three inputs are bits. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The spec: the result is the bit `maj(a, b, c)` (`1` iff at least two inputs are). -/
def Spec (ins outs : List F) : Prop :=
  outs = [natBit (((ins.getD 0 0).val + (ins.getD 1 0).val + (ins.getD 2 0).val) / 2)]

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1), LC.var (.plug 2)] := by
  decide +kernel

theorem outputs_eq : template.outputs = [LC.var (.wit 0)] := by
  decide +kernel

theorem rows_eq : template.rows =
    [⟨⟨3, [(1, .plug 0), (1, .plug 1), (-9, .plug 2), (1, .wit 0)]⟩,
      ⟨-4, [(1, .plug 0), (1, .plug 1), (6, .plug 2)]⟩, ⟨-12, []⟩⟩] := by
  decide +kernel

theorem ins_eq (σ : TVar → F) :
    template.ins σ = [σ (.plug 0), σ (.plug 1), σ (.plug 2)] := by
  simp [Template.ins, inputs_eq]

theorem outs_eq (σ : TVar → F) : template.outs σ = [σ (.wit 0)] := by
  simp [Template.outs, outputs_eq]

theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    (σ (.wit 0) + σ (.plug 0) + σ (.plug 1) - 9 * σ (.plug 2) + 3) *
        (σ (.plug 0) + σ (.plug 1) + 6 * σ (.plug 2) - 4) = -12 := by
  simp only [Template.Sat, rows_eq, Xark.R1cs.Sat, List.mem_singleton, forall_eq, Row.Sat,
    LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  constructor <;> intro h <;> linear_combination h

/-- **Soundness.** On input bits, every assignment satisfying the row outputs
`maj(a, b, c)`: the hinted bit has no other value. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  have hr := (sat_iff σ).mp h
  rw [ins_eq] at ha ⊢
  rw [outs_eq]
  obtain ⟨h0, h1, h2⟩ := bits3 ha
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rw [h0, h1, h2] at hr <;>
    simp only [Spec, List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2, ZMod.val_zero,
      ZMod.val_one, natBit, List.cons.injEq, and_true] <;> norm_num <;> pin_row hr

-- `simp` leaves the bit argument as a sum `congr 1; ring` reorders.
/-- **Its output is a bit** (on input bits). -/
theorem outs_isBit (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    ∀ v ∈ template.outs σ, IsBit v := by
  have hs := soundness σ ha h
  rw [Spec] at hs
  rw [hs]
  intro v hv
  rw [List.mem_singleton] at hv
  exact hv ▸ natBit_isBit _

end Xark.Templates.Maj3

namespace Xark.Templates.Chi

open Xark.HashOps

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The input assumption: the three inputs are bits. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The spec: the result is Keccak's χ bit `a ⊕ (¬b ∧ c)`. -/
def Spec (ins outs : List F) : Prop :=
  outs = [natBit (((ins.getD 0 0).val + (1 - (ins.getD 1 0).val) * (ins.getD 2 0).val) % 2)]

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1), LC.var (.plug 2)] := by
  decide +kernel

theorem outputs_eq : template.outputs = [LC.var (.wit 0)] := by
  decide +kernel

theorem rows_eq : template.rows =
    [⟨⟨0, [(3, .plug 0), (-1, .plug 1), (-1, .plug 2), (1, .wit 0)]⟩,
      ⟨-3, [(4, .plug 0), (1, .plug 1), (1, .plug 2)]⟩, ⟨0, [(4, .plug 0), (2, .plug 1)]⟩⟩] := by
  decide +kernel

theorem ins_eq (σ : TVar → F) :
    template.ins σ = [σ (.plug 0), σ (.plug 1), σ (.plug 2)] := by
  simp [Template.ins, inputs_eq]

theorem outs_eq (σ : TVar → F) : template.outs σ = [σ (.wit 0)] := by
  simp [Template.outs, outputs_eq]

theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    (σ (.wit 0) + 3 * σ (.plug 0) - σ (.plug 1) - σ (.plug 2)) *
        (4 * σ (.plug 0) + σ (.plug 1) + σ (.plug 2) - 3) = 4 * σ (.plug 0) + 2 * σ (.plug 1) := by
  simp only [Template.Sat, rows_eq, Xark.R1cs.Sat, List.mem_singleton, forall_eq, Row.Sat,
    LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  constructor <;> intro h <;> linear_combination h

/-- **Soundness.** On input bits, every assignment satisfying the row outputs
`a ⊕ (¬b ∧ c)`: the hinted bit has no other value. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  have hr := (sat_iff σ).mp h
  rw [ins_eq] at ha ⊢
  rw [outs_eq]
  obtain ⟨h0, h1, h2⟩ := bits3 ha
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rw [h0, h1, h2] at hr <;>
    simp only [Spec, List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2, ZMod.val_zero,
      ZMod.val_one, natBit, List.cons.injEq, and_true] <;> norm_num <;> pin_row hr

-- `simp` leaves the bit argument as a sum `congr 1; ring` reorders.
/-- **Its output is a bit** (on input bits). -/
theorem outs_isBit (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    ∀ v ∈ template.outs σ, IsBit v := by
  have hs := soundness σ ha h
  rw [Spec] at hs
  rw [hs]
  intro v hv
  rw [List.mem_singleton] at hv
  exact hv ▸ natBit_isBit _

end Xark.Templates.Chi

namespace Xark.Templates.Ch

open Xark.HashOps

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The input assumption: the three inputs are bits. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The spec: the result is SHA-256's choice bit, `f` where `e = 1` and `g` where not. -/
def Spec (ins outs : List F) : Prop :=
  outs = [if ins.getD 0 0 = 1 then ins.getD 1 0 else ins.getD 2 0]

theorem inputs_eq : template.inputs = [LC.var (.plug 0), LC.var (.plug 1), LC.var (.plug 2)] := by
  decide +kernel

theorem outputs_eq : template.outputs = [⟨0, [(1, .plug 2), (1, .wit 0)]⟩] := by
  decide +kernel

theorem rows_eq : template.rows =
    [⟨LC.var (.plug 0), ⟨0, [(1, .plug 1), (-1, .plug 2)]⟩, LC.var (.wit 0)⟩] := by
  decide +kernel

theorem ins_eq (σ : TVar → F) :
    template.ins σ = [σ (.plug 0), σ (.plug 1), σ (.plug 2)] := by
  simp [Template.ins, inputs_eq]

/-- The row holds iff the output is `g + e·(f − g)`, whatever the inputs. -/
theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    σ (.plug 0) * (σ (.plug 1) - σ (.plug 2)) = σ (.wit 0) := by
  simp only [Template.Sat, rows_eq, Xark.R1cs.Sat, List.mem_singleton, forall_eq, Row.Sat,
    LC.eval, LC.var, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  constructor <;> intro h <;> linear_combination h

theorem outs_eq (σ : TVar → F) (h : template.Sat σ) :
    template.outs σ = [σ (.plug 2) + σ (.plug 0) * (σ (.plug 1) - σ (.plug 2))] := by
  rw [(sat_iff σ).mp h]
  simp [Template.outs, outputs_eq, LC.eval]

/-- **Soundness.** On input bits, every assignment satisfying the row outputs `Ch(e, f, g)`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [outs_eq σ h]
  rw [ins_eq] at ha ⊢
  obtain ⟨h0, -, -⟩ := bits3 ha
  rcases h0 with h0 | h0 <;> simp [Spec, h0]

/-- **Its output is a bit** (on input bits). -/
theorem outs_isBit (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    ∀ v ∈ template.outs σ, IsBit v := by
  have hs := soundness σ ha h
  rw [Spec] at hs
  rw [hs]
  rw [ins_eq] at ha ⊢
  obtain ⟨-, h1, h2⟩ := bits3 ha
  intro v hv
  rw [List.mem_singleton] at hv
  subst hv
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  split
  · exact h1
  · exact h2

end Xark.Templates.Ch
