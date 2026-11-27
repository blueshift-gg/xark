/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.Words
import Formal.RangeDerived

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# `convert_wide`'s glue rows

`convert_wide` is a plain function (no `#[gadget]`): in the 17×121 circuit its rows are
the big glue segment s36. This file models one `range_derived::<W>` block the way the
frontend lowers it over *circuit* variables — `W - 1` booleanity rows and the top row
`top · (top − 2^(W−1)) = 0` — and proves the block bounds its value, the glue-level
analogue of `Xark.Templates.RangeDerived.block_sound`. The convert proof applies it to
the block rows and then telescopes the carry equations with `Xark.Rsa.Convert`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt sum_map_range cast_sum)

/-- Bit `i`'s variable in a glue block whose first bit is `base`. -/
def gbit (base i : ℕ) : ℕ := base + 2 * i

/-- `Σᵢ 2ⁱ·bᵢ` over a block's `W - 1` low bits. -/
def gacc (base W : ℕ) : GLC :=
  ⟨0, (List.range (W - 1)).map fun i => (((2 ^ i : ℕ) : F), gbit base i)⟩

def gnegTerms (l : List (F × ℕ)) : List (F × ℕ) := l.map fun t => (-t.1, t.2)

/-- `top = v − Σᵢ 2ⁱ·bᵢ`. -/
def gtopA (v base W : ℕ) : GLC :=
  let terms : List (F × ℕ) := (1, v) :: gnegTerms (gacc base W).terms
  ⟨0, terms⟩

/-- `top − 2^(W−1)`. -/
def gtopB (v base W : ℕ) : GLC :=
  ⟨(gtopA v base W).const - ((2 ^ (W - 1) : ℕ) : F), (gtopA v base W).terms⟩

def gboolRow (base i : ℕ) : GRow :=
  ⟨LC.var (gbit base i), LC.var (gbit base i), LC.var (gbit base i)⟩

/-- The block's rows: one booleanity row per low bit, then `top · (top − 2^(W−1)) = 0`. -/
def gblockRows (v base W : ℕ) : List GRow :=
  (List.range (W - 1)).map (gboolRow base) ++
    [⟨gtopA v base W, gtopB v base W, ⟨0, []⟩⟩]

theorem gblock_sound (v base W : ℕ) (hW : W ≤ 253) (hW1 : 1 ≤ W) (σ : ℕ → F)
    (h : Sat (gblockRows v base W) σ) : (σ v).val < 2 ^ W := by
  have hbits : ∀ i, i < W - 1 → IsBit (σ (gbit base i)) := by
    intro i hi
    have hmem : gboolRow base i ∈ gblockRows v base W := by
      rw [gblockRows]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hrow := h _ hmem
    refine isBit_of_mul_self ?_
    simpa [Row.Sat, gboolRow, LC.var, LC.eval] using hrow
  have hrow : (gtopA v base W).eval σ * (gtopB v base W).eval σ = 0 := by
    have hmem : (⟨gtopA v base W, gtopB v base W, ⟨0, []⟩⟩ : GRow) ∈ gblockRows v base W := by
      rw [gblockRows]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have := h _ hmem
    simpa only [Row.Sat, LC.eval, List.map_nil, List.sum_nil, add_zero] using this
  have hB : (gtopB v base W).eval σ = (gtopA v base W).eval σ - ((2 ^ (W - 1) : ℕ) : F) := by
    simp only [gtopB, LC.eval]
    ring
  rw [hB] at hrow
  have htop : (gtopA v base W).eval σ = 0 ∨
      (gtopA v base W).eval σ = ((2 ^ (W - 1) : ℕ) : F) := by
    rcases mul_eq_zero.mp hrow with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linear_combination h')
  let w : ℕ → ℕ := fun i => (σ (gbit base i)).val
  have hwb : ∀ i < W - 1, w i ≤ 1 := fun i hi => isBit_val (hbits i hi)
  have hWlt := word_lt w (W - 1) hwb
  have hcast : ((∑ i ∈ Finset.range (W - 1), 2 ^ i * w i : ℕ) : F) =
      (gacc base W).eval σ := by
    simp only [gacc, LC.eval, List.map_map, Function.comp_def, sum_map_range]
    push_cast
    simp only [w, gbit, ZMod.natCast_zmod_val]
    ring
  have hlt : ((gacc base W).eval σ).val < 2 ^ (W - 1) := by
    rw [← hcast,
      ZMod.val_natCast_of_lt
        (lt_trans hWlt (Xark.Templates.ToBits.two_pow_lt_r' (by omega)))]
    exact hWlt
  have hneg : (List.map (fun t => t.1 * σ t.2) (gnegTerms (gacc base W).terms)).sum =
      - (List.map (fun t => t.1 * σ t.2) (gacc base W).terms).sum := by
    induction (gacc base W).terms with
    | nil => simp [gnegTerms]
    | cons t ts ih => simp [gnegTerms] at ih ⊢; rw [ih]; ring
  have hvLC : σ v = (gacc base W).eval σ + (gtopA v base W).eval σ := by
    simp only [gtopA, LC.eval, List.map_cons, List.sum_cons, zero_add]
    rw [hneg]
    simp only [gacc]
    ring
  have hpow : 2 ^ (W - 1) + 2 ^ (W - 1) = 2 ^ W := by
    have h : W = (W - 1) + 1 := by omega
    calc 2 ^ (W - 1) + 2 ^ (W - 1) = 2 ^ (W - 1) * 2 := by ring
      _ = 2 ^ ((W - 1) + 1) := (pow_succ 2 (W - 1)).symm
      _ = 2 ^ W := by rw [← h]
  rw [hvLC, ZMod.val_add]
  have h2 : ((gacc base W).eval σ).val + ((gtopA v base W).eval σ).val < 2 ^ W := by
    rcases htop with h0 | h1
    · rw [h0, ZMod.val_zero, add_zero]
      exact lt_trans hlt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    · rw [h1, ZMod.val_natCast_of_lt (Xark.Templates.ToBits.two_pow_lt_r' (by omega))]
      omega
  rw [Nat.mod_eq_of_lt (lt_trans h2 (Xark.Templates.ToBits.two_pow_lt_r' hW))]
  exact h2

/-- The glue row `k` of s36 (`convert_wide`'s rows). -/
def growAt (k : ℕ) : GRow :=
  (Rsa2048Words.s36.rows).getD k ⟨⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩⟩

/-- `Sat` transfers to a slice of a satisfied list. -/
theorem sat_slice {σ : ℕ → F} {l : List GRow} (h : Sat l σ) {a b : ℕ} {m : List GRow}
    (hm : m = (l.drop a).take b) : Sat m σ := by
  subst hm
  intro r hr
  exact h r (List.mem_of_mem_drop (List.mem_of_mem_take hr))

/-- **A field zero that is an integer below `r` in absolute value is zero.** The convert
rows are cast integer combinations of an input limb (`< 2^121`), a previous carry
(`< 2^118`), a carry (`< 2^118`) and an output limb (`< 2^82`); the combination is
below `2^200 < r`. -/
theorem int_eq_zero_of_cast (E : ℤ) (h : (E : F) = 0) (hlo : -((r : ℤ)) < E)
    (hhi : E < (r : ℤ)) : E = 0 := by
  have hr0 : ((r : ℕ) : F) = 0 := ZMod.natCast_self r
  by_cases h0 : (0 : ℤ) ≤ E
  · have hval : ((E.toNat : ℕ) : ℤ) = E := Int.toNat_of_nonneg h0
    have hcast : ((E.toNat : ℕ) : F) = 0 := by
      rw [← hval] at h
      simpa only [Int.cast_natCast] using h
    have hv := ZMod.val_natCast_of_lt (n := r) (a := E.toNat) (by omega : E.toNat < r)
    rw [hcast, ZMod.val_zero] at hv
    omega
  · have h0' : E < 0 := by omega
    have h1 : (0 : ℤ) ≤ E + (r : ℤ) := by omega
    have h2 : E + (r : ℤ) < (r : ℤ) := by omega
    have hcast : ((E + (r : ℤ) : ℤ) : F) = 0 := by
      push_cast
      rw [h, hr0]
      ring
    have hval : ((E + (r : ℤ)).toNat : ℤ) = E + (r : ℤ) := Int.toNat_of_nonneg h1
    have hcast' : (((E + (r : ℤ)).toNat : ℕ) : F) = 0 := by
      rw [← hval] at hcast
      simpa only [Int.cast_natCast] using hcast
    have hv := ZMod.val_natCast_of_lt (n := r) (a := (E + (r : ℤ)).toNat) (by omega)
    rw [hcast', ZMod.val_zero] at hv
    omega

/-- A `gblockRows` slice of s36 is satisfied. -/
theorem gblock_sat {σ : ℕ → F} (h : Sat Rsa2048Words.s36.rows σ) {v base W k : ℕ}
    (hm : gblockRows v base W = (Rsa2048Words.s36.rows.drop k).take W) :
    Sat (gblockRows v base W) σ :=
  sat_slice h hm

/-- Row `k` of s36 is satisfied. -/
theorem growAt_sat {σ : ℕ → F} (h : Sat Rsa2048Words.s36.rows σ) (k : ℕ)
    (hk : k < Rsa2048Words.s36.rows.length) : (growAt k).Sat σ := by
  rw [growAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact h _ (List.getElem_mem hk)

/-- The input reader's plug 0 is variable 0. -/
theorem n_plug0 : (wcallAt 0).env (.plug 0) = (LC.var 0 : GLC) := rfl

theorem pn_n0 (σ : ℕ → F) : pn (wcallAt 0) σ 0 = (σ 0).val := by
  simp [pn, Call.lift, n_plug0, LC.var, LC.eval]

theorem s36_block0_limb : gblockRows 16747 16748 82 = (Rsa2048Words.s36.rows.drop 1).take 82 := by
  decide +kernel

theorem s36_block0_carry :
    gblockRows 16746 16911 118 = (Rsa2048Words.s36.rows.drop 83).take 118 := by
  decide +kernel

/-- **Column 0 of `convert_wide(n)`**: `x_0 = W·carry_0 + limb_0` over the integers. -/
theorem col0_eq (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    ((σ 0).val : ℤ) = (W : ℤ) * ((σ 16746).val : ℤ) + ((σ 16747).val : ℤ) := by
  have hs : Sat Rsa2048Words.s36.rows σ := by
    have h' := wsegSat h (n := 36) (by decide)
    rwa [show wseg 36 = Rsa2048Words.s36 from rfl] at h'
  have hr := growAt_sat hs 0 (by decide)
  have hrow : growAt 0 =
      ⟨⟨0, [((1 : F), 0), (((-(2 ^ 82 : ℤ)) : F), 16746), ((-1 : F), 16747)]⟩,
        ⟨1, []⟩, ⟨0, []⟩⟩ := by decide +kernel
  rw [hrow] at hr
  have ha := by
    simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr
  have hlimb := gblock_sound 16747 16748 82 (by norm_num) (by norm_num) σ
    (gblock_sat hs s36_block0_limb)
  have hcarry := gblock_sound 16746 16911 118 (by norm_num) (by norm_num) σ
    (gblock_sat hs s36_block0_carry)
  have hx := n_limb_bound σ h (j := 0) (by norm_num)
  rw [pn_n0] at hx
  have hE : ((((σ 0).val : ℤ) - ((2 ^ 82 : ℤ)) * ((σ 16746).val : ℤ)
      - ((σ 16747).val : ℤ) : ℤ) : F) = 0 := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination ha
  have hb1 : ((σ 16746).val : ℤ) < 2 ^ 118 := by exact_mod_cast hcarry
  have hb2 : ((σ 16747).val : ℤ) < 2 ^ 82 := by exact_mod_cast hlimb
  have hb3 : ((σ 0).val : ℤ) < 2 ^ 121 := by exact_mod_cast hx
  have hb0 : (0 : ℤ) ≤ ((σ 16746).val : ℤ) := by positivity
  have hr' : (2 : ℤ) ^ 200 < (r : ℤ) := by
    have := Xark.Templates.ToBits.two_pow_lt_r' (n := 200) (by norm_num)
    exact_mod_cast this
  have hlo : -((r : ℤ)) < ((σ 0).val : ℤ) - ((2 ^ 82 : ℤ)) * ((σ 16746).val : ℤ)
      - ((σ 16747).val : ℤ) := by nlinarith
  have hhi : ((σ 0).val : ℤ) - ((2 ^ 82 : ℤ)) * ((σ 16746).val : ℤ)
      - ((σ 16747).val : ℤ) < (r : ℤ) := by nlinarith
  have hzero := int_eq_zero_of_cast _ hE hlo hhi
  show ((σ 0).val : ℤ) = (W : ℤ) * ((σ 16746).val : ℤ) + ((σ 16747).val : ℤ)
  rw [show (W : ℤ) = 2 ^ 82 by simp [W]]
  linarith

/-- `Sat` of s36's rows from the whole circuit. -/
theorem s36_sat {σ : ℕ → F} (h : Sat Rsa2048Words.circuit σ) :
    Sat Rsa2048Words.s36.rows σ := by
  have h' := wsegSat h (n := 36) (by decide)
  rwa [show wseg 36 = Rsa2048Words.s36 from rfl] at h'

/-- A carry row with an input term and the previous carry. -/
theorem convert_col_x (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ)
    (k : ℕ) (hk : k < Rsa2048Words.s36.rows.length) (e : ℕ) (he : e ≤ 121)
    (x prev carry limb : ℕ)
    (hrow : growAt k =
      ⟨⟨0, [(((2 ^ e : ℤ) : F), x), ((1 : F), prev), ((-W : F), carry), ((-1 : F), limb)]⟩,
        ⟨1, []⟩, ⟨0, []⟩⟩)
    (hx : (σ x).val < 2 ^ 121) (hp : (σ prev).val < 2 ^ 118)
    (hc : (σ carry).val < 2 ^ 118) (hl : (σ limb).val < 2 ^ 82) :
    (2 ^ e : ℤ) * ((σ x).val : ℤ) + ((σ prev).val : ℤ) =
      (W : ℤ) * ((σ carry).val : ℤ) + ((σ limb).val : ℤ) := by
  have hr := growAt_sat (s36_sat h) k hk
  rw [hrow] at hr
  have ha := by
    simpa [Xark.R1cs.Row.Sat, Xark.R1cs.LC.eval] using hr
  let E : ℤ := (2 ^ e : ℤ) * ((σ x).val : ℤ) + ((σ prev).val : ℤ)
      - (W : ℤ) * ((σ carry).val : ℤ) - ((σ limb).val : ℤ)
  have hE : (E : F) = 0 := by
    dsimp [E]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination ha
  have hb1 : ((σ prev).val : ℤ) < 2 ^ 118 := by exact_mod_cast hp
  have hb2 : ((σ carry).val : ℤ) < 2 ^ 118 := by exact_mod_cast hc
  have hb3 : ((σ limb).val : ℤ) < 2 ^ 82 := by exact_mod_cast hl
  have hb4 : ((σ x).val : ℤ) < 2 ^ 121 := by exact_mod_cast hx
  have hpow : ((2 : ℤ) ^ e) ≤ 2 ^ 121 :=
    pow_le_pow_right₀ (by norm_num) he
  have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ e := pow_nonneg (by norm_num) e
  have hstep : ((2 : ℤ) ^ e) * ((σ x).val : ℤ) ≤ ((2 : ℤ) ^ e) * 2 ^ 121 :=
    mul_le_mul_of_nonneg_left (le_of_lt hb4) hpow0
  have hmul : ((2 : ℤ) ^ e) * ((σ x).val : ℤ) ≤ 2 ^ 242 := by
    refine le_trans hstep ?_
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hWcarry : (W : ℤ) * ((σ carry).val : ℤ) < 2 ^ 200 := by
    have hW' : (W : ℤ) = 2 ^ 82 := by simp [W]
    rw [hW']
    have h := mul_lt_mul_of_pos_left hb2 (by norm_num : (0 : ℤ) < 2 ^ 82)
    have h2 : ((2 : ℤ) ^ 82 * 2 ^ 118) = 2 ^ 200 := by rw [← pow_add]
    rwa [h2] at h
  have hp0 : (0 : ℤ) ≤ ((σ prev).val : ℤ) := by positivity
  have h200 : (2 : ℤ) ^ 200 < (r : ℤ) := by
    have h := Xark.Templates.ToBits.two_pow_lt_r' (n := 200) (by norm_num)
    have h' := Nat.cast_lt (α := ℤ).mpr h
    simpa [Nat.cast_pow] using h'
  have h243 : (2 : ℤ) ^ 243 < (r : ℤ) := by
    have h := Xark.Templates.ToBits.two_pow_lt_r' (n := 243) (by norm_num)
    have h' := Nat.cast_lt (α := ℤ).mpr h
    simpa [Nat.cast_pow] using h'
  have hlo : -((r : ℤ)) < E := by
    dsimp [E]
    nlinarith [hWcarry, hb3, hp0, h200]
  have hW0 : (0 : ℤ) ≤ (W : ℤ) := by
    rw [show (W : ℤ) = 2 ^ 82 by simp [W]]
    positivity
  have hc0 : (0 : ℤ) ≤ (W : ℤ) * ((σ carry).val : ℤ) := mul_nonneg hW0 (by positivity)
  have hl0 : (0 : ℤ) ≤ ((σ limb).val : ℤ) := by positivity
  have hhi : E < (r : ℤ) := by
    dsimp [E]
    nlinarith [hmul, hb1, hc0, hl0, h243]
  have hzero := int_eq_zero_of_cast _ hE hlo hhi
  linarith

end Xark.Circuits.Rsa2048
