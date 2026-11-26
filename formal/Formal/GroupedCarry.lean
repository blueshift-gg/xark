/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.GroupedColumnStep
import Formal.GroupedColumns
import Formal.ToBits

set_option linter.style.header false

/-!
# From a group carry's field element to its integer

`grouped_column_step` returns `k = num * 2^-164` as a field element, where
`num = S + cb - 2^88 + 2^252`; `Formal/GroupedColumnStep.lean` proves `k < 2^89`.
This file closes the arithmetic between those two statements:

* `outputs_eq`: the exported template's output **is** `num * 2^-164` — its five plug
  coefficients are `2^-164` times `1, 2^82, -1, -2^82, 1` and its constant is
  `2^-164` times `2^252 - 2^88`, checked against the template by `decide +kernel`.
* `carry_row`: when `num` does not wrap (`0 ≤ num < r`), `k`'s representative below
  `2^89` makes `2^164 * k = num` hold **over the integers**, not only mod `r`:
  `2^164 * k.val < 2^253 < r`, so both sides of the field identity are canonical.

That integer equality is the `CarrySpec` row `Formal/GroupedColumns.lean`'s
telescope consumes. The bounds on `num` (the column sum's `< 2^251.7` and the
carry's `< 2^89`) come from the limb range checks; this file takes them as the
`0 ≤ num` and `num < r` hypotheses.
-/

namespace Xark.Rsa.GroupedCarry

open Xark.Template Xark.R1cs
open Xark.Templates.GroupedColumnStep
open Xark.Rsa.GroupedColumns (Q W BI OFF)

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- `2^-164 mod r`, the constant multiply `xark_rsa::grouped_columns` uses to read a
group carry from its numerator (`gadgets/xark-rsa/src/lib.rs`, `INV_GROUP`). -/
def INV_GROUP : F :=
  11761852403780205603504176608903144981443942272354872058493689129916111935102

/-- `2^82` in the field. -/
def wF : F := ((2 ^ 82 : ℕ) : F)

/-- Multiply every coefficient of a combination by `c`. -/
def _root_.Xark.R1cs.LC.mulConst (l : LC) (c : F) : LC :=
  ⟨c * l.const, l.terms.map fun t => (c * t.1, t.2)⟩

theorem sum_map_mul (ts : List (F × TVar)) (c : F) (σ : TVar → F) :
    ((ts.map fun t => (c * t.1, t.2)).map fun t => t.1 * σ t.2).sum =
      c * (ts.map fun t => t.1 * σ t.2).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

theorem eval_mulConst (l : LC) (c : F) (σ : TVar → F) :
    (l.mulConst c).eval σ = c * l.eval σ := by
  obtain ⟨k, ts⟩ := l
  simp only [Xark.R1cs.LC.mulConst, LC.eval, sum_map_mul]
  ring

/-- The numerator `grouped_column_step` builds:
`(lhs0 - rhs0) + 2^82·(lhs1 - rhs1) + cb_prev - 2^88 + 2^252`. -/
def numLC : LC :=
  ⟨((2 ^ 252 - 2 ^ 88 : ℕ) : F),
    [(1, .plug 0), (wF, .plug 1), (-1, .plug 2), (-wF, .plug 3), (1, .plug 4)]⟩

/-- **The exported output is the carry.** The template's output combination is the
numerator scaled by `2^-164`: the constants `1, 2^82, -1, -2^82, 1` on the plugs and
`2^252 - 2^88` are the Rust expression's. -/
theorem outputs_eq : template.outputs = [numLC.mulConst INV_GROUP] := by
  decide +kernel

/-- `2^164 · 2^-164 = 1` in the field. -/
theorem Q_mul_inv : ((2 ^ 164 : ℕ) : F) * INV_GROUP = 1 := by decide

/-- **The carry is the integer quotient.** If the numerator is a canonical field
element (`num < r`) and the carry's representative is below `2^89`, then
`2^164 * k` is below `2^253 < r` too, so the field identity `num = 2^164 · k`
holds between canonical representatives and is an equality of naturals. -/
theorem carry_of_step (num : ℕ) (k : F) (hnum : num < r) (hk : k.val < 2 ^ 89)
    (h : (num : F) = ((2 ^ 164 : ℕ) : F) * k) : num = 2 ^ 164 * k.val := by
  have hpow : 2 ^ 164 * 2 ^ 89 = 2 ^ 253 := by norm_num
  have hQ : 2 ^ 164 * k.val < r := by
    have h1 : 2 ^ 164 * k.val < 2 ^ 164 * 2 ^ 89 :=
      Nat.mul_lt_mul_of_pos_left hk (by positivity)
    rw [hpow] at h1
    exact lt_trans h1 (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num))
  have hval := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hnum, ZMod.val_mul,
    ZMod.val_natCast_of_lt (Xark.Templates.ToBits.two_pow_lt_r' (by norm_num)),
    Nat.mod_eq_of_lt hQ] at hval
  exact hval

/-- **A `CarrySpec` row.** With no wrap in the numerator (`0 ≤ num < r`), the
step's carry satisfies the integer equation `num = 2^164 · k` the telescope uses. -/
theorem carry_row (num : ℤ) (k : F) (h0 : 0 ≤ num) (hlt : num < (r : ℤ))
    (hcast : (num : F) = ((2 ^ 164 : ℕ) : F) * k) (hk : k.val < 2 ^ 89) :
    num = Q * (k.val : ℤ) := by
  have hnum : num.toNat < r := by
    have h : (num.toNat : ℤ) = num := Int.toNat_of_nonneg h0
    exact_mod_cast (show (num.toNat : ℤ) < (r : ℤ) by omega)
  have hnat : ((num.toNat : ℕ) : F) = (num : F) := by
    have h := congrArg (fun z : ℤ => (z : F)) (Int.toNat_of_nonneg h0)
    simpa only [Int.cast_natCast] using h
  have hcast' : ((num.toNat : ℕ) : F) = ((2 ^ 164 : ℕ) : F) * k := by
    rw [hnat]
    exact hcast
  have h := carry_of_step num.toNat k hnum hk hcast'
  have h2 : (num.toNat : ℤ) = ((2 ^ 164 : ℕ) : ℤ) * (k.val : ℤ) := by
    rw [h]; push_cast; ring
  rw [Int.toNat_of_nonneg h0] at h2
  rwa [show ((2 ^ 164 : ℕ) : ℤ) = Q by norm_num [Q]] at h2

/-- The same row written as `grouped_columns` computes it:
`S + cb - 2^88 + 2^252 = 2^164 · k`. -/
theorem step_row (S cb : ℤ) (k : F) (hk : k.val < 2 ^ 89)
    (h0 : 0 ≤ S + cb - BI + OFF) (hlt : S + cb - BI + OFF < (r : ℤ))
    (hcast : (((S + cb - BI + OFF : ℤ)) : F) = ((2 ^ 164 : ℕ) : F) * k) :
    S + cb - BI + OFF = Q * (k.val : ℤ) :=
  carry_row (S + cb - BI + OFF) k h0 hlt hcast hk

end Xark.Rsa.GroupedCarry
