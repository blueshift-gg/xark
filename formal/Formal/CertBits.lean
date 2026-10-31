/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Template
import Formal.ToBits
import Formal.Add32
import Formal.RequireLt

set_option linter.style.header false

/-!
# A `to_bits` decomposition inside a template

`Field::to_bits::<m + 1>(x)` called inside a larger gadget emits `m` booleanity rows for bits
`1..m` (at `wit o..o+m−1`) and one row forcing the low bit `x − Σ 2^(i+1)·bᵢ` to be a bit
(`bitRows`). `bits_sound`: the rows force `x < 2^(m+1)`. Shared by the certificate
proofs (`MulCertR1`, `MulCertK1`, the point-op checks) and `FakeGlvK1`/`FakeGlvR1`.
-/

namespace Xark.Templates.MulCertK1

open Xark.Template Xark.R1cs

/-- The bit decomposition of `x` into `m + 1` bits, bits `1..m` at `wit (o + i)`, as
`Field::to_bits` emits it inside the call (`Formal/ToBits.lean`). -/
def lowOf (x : LC) (o m : ℕ) : LC :=
  ⟨x.const, x.terms ++ (List.range m).map fun i => (-((2 ^ (i + 1) : ℕ) : F), .wit (o + i))⟩

def boolRow (v : ℕ) : Row := ⟨LC.var (.wit v), LC.var (.wit v), LC.var (.wit v)⟩

def bitRows (x : LC) (o m : ℕ) : List Row :=
  (List.range m).map (fun i => boolRow (o + i)) ++
    [⟨lowOf x o m, ⟨x.const - 1, (lowOf x o m).terms⟩, ⟨0, []⟩⟩]

def bitHints (x : LC) (o m : ℕ) : List Hint :=
  (List.range m).map fun i => .bit (o + i) x (i + 1)

instance : Fact (Nat.Prime r) := bn254_r_prime

open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt testBit_word word_testBit
  sum_map_range bit_eq_testBit)

theorem eval_lowOf (x : LC) (o m : ℕ) (σ : TVar → F) :
    (lowOf x o m).eval σ =
      x.eval σ - ∑ i ∈ Finset.range m, ((2 ^ (i + 1) : ℕ) : F) * σ (.wit (o + i)) := by
  simp only [lowOf, LC.eval, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    sum_map_range, neg_mul, Finset.sum_neg_distrib]
  ring

theorem sat_bitRows (x : LC) (o m : ℕ) (σ : TVar → F) : Xark.R1cs.Sat (bitRows x o m) σ ↔
    (∀ i < m, σ (.wit (o + i)) * σ (.wit (o + i)) = σ (.wit (o + i))) ∧
      (lowOf x o m).eval σ * ((lowOf x o m).eval σ - 1) = 0 := by
  have hB : (⟨x.const - 1, (lowOf x o m).terms⟩ : LC).eval σ = (lowOf x o m).eval σ - 1 := by
    simp only [LC.eval, lowOf]; ring
  simp only [Xark.R1cs.Sat, bitRows, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa [Row.Sat, boolRow] using h _ (Or.inl ⟨i, hi, rfl⟩)
    · have := h _ (Or.inr rfl)
      simp only [Row.Sat, hB] at this
      simpa [LC.eval] using this
  · rintro ⟨hb, hl⟩ row (⟨i, hi, rfl⟩ | rfl)
    · simpa [Row.Sat, boolRow] using hb i hi
    · simp only [Row.Sat, hB]
      simpa [LC.eval] using hl

/-- Rows that hold make the decomposed value `x` below `2^(m+1)`. -/
theorem bits_sound (x : LC) (o m : ℕ) (hm : m + 1 ≤ 253) (σ : TVar → F)
    (h : Xark.R1cs.Sat (bitRows x o m) σ) : (x.eval σ).val < 2 ^ (m + 1) := by
  obtain ⟨hb, hl⟩ := (sat_bitRows x o m σ).mp h
  have hw : ∀ i < m, IsBit (σ (.wit (o + i))) := fun i hi => isBit_of_mul_self (hb i hi)
  have hlow : IsBit ((lowOf x o m).eval σ) := ToBits.isBit_of_mul_sub_one hl
  let v : ℕ → ℕ := fun i =>
    if i = 0 then ((lowOf x o m).eval σ).val else (σ (.wit (o + (i - 1)))).val
  have hv : ∀ i < m + 1, v i ≤ 1 := fun i hi => by
    by_cases h0 : i = 0
    · simpa [v, h0] using isBit_val hlow
    · simpa [v, h0] using isBit_val (hw (i - 1) (by omega))
  have hW := word_lt v (m + 1) hv
  have hcast : ((∑ i ∈ Finset.range (m + 1), 2 ^ i * v i : ℕ) : F) = x.eval σ := by
    rw [Finset.sum_range_succ']
    push_cast
    simp only [v, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, if_true, one_mul,
      ZMod.natCast_val, ZMod.cast_id', id]
    rw [eval_lowOf]
    push_cast
    ring
  rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hW (ToBits.two_pow_lt_r' hm))]
  exact hW

/-- A limb form the caller passes (`8p_j + x_j − y_j`, `x_j + y_j + z_j`, …) is read
exactly: a non-negative integer below `r` is its own canonical value. -/
theorem val_intCast {z : ℤ} (h0 : 0 ≤ z) (h1 : z < 2 ^ 253) : (((z : F).val : ℕ) : ℤ) = z := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hn : n < r := lt_trans (by exact_mod_cast h1) two_pow_lt_r
  rw [Int.cast_natCast, ZMod.val_natCast_of_lt hn]

/-- An integer in `(−r, r)` that is `0` in `Fr` is `0`. -/
theorem lift (x : ℤ) (h : (x : F) = 0) (hl : -(r : ℤ) < x) (hu : x < r) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x r).mp h) (abs_lt.mpr ⟨hl, hu⟩)

theorem r_eq : (r : ℤ) =
    21888242871839275222246405745257275088548364400416034343698204186575808495617 := by
  simp [r]

theorem val_cast {n : ℕ} (h : n < r) : ((n : ℕ) : F).val = n := ZMod.val_natCast_of_lt h

end Xark.Templates.MulCertK1
