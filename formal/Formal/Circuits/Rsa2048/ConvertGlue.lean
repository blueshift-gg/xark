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

end Xark.Circuits.Rsa2048
