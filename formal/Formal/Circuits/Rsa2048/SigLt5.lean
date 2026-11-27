/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.SigLt4
import Formal.Circuits.Rsa2048.Bits
import Formal.RequireLt25x82

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# `sig < n`

`s545` is `require_lt::<25, 82>(sig, m₋₁)`: the first 25 of its 50 plugs are `sig`'s
packed limbs, the last 25 are `m₋₁ = chainN − 1`. The range check's `Spec` is a
`limbs` comparison, so `sig ≤ chainN − 1`; the modulus is at least `2^2047`, so
`sig < chainN`. -/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- A plug as an input linear combination evaluates to the plug's field value. -/
theorem plug_eval (σ' : TVar → F) (j : ℕ) :
    (Xark.R1cs.LC.eval (⟨0, [(1, .plug j)]⟩ : LC) σ') = σ' (.plug j) := by
  simp [Xark.R1cs.LC.eval]

/-- The range check's 50 inputs, as the field values they read. -/
theorem req_ins (σ' : TVar → F) :
    Xark.Templates.RequireLt25x82.template.ins σ'
      = (List.range 25).map (fun j => σ' (.plug j))
        ++ (List.range 25).map (fun j => σ' (.plug (25 + j))) := by
  rw [Template.ins, Xark.Templates.RequireLt25x82.is_model.1]
  have hin : Xark.Templates.RequireLt.inputs 25 (Xark.Templates.RequireLt.plugM 25)
      = (List.range 25).map (fun j => (⟨0, [(1, .plug j)]⟩ : LC))
        ++ (List.range 25).map (fun j => (⟨0, [(1, .plug (25 + j))]⟩ : LC)) := by
    simp [Xark.Templates.RequireLt.inputs, Xark.Templates.RequireLt.plugM]
  rw [hin, List.map_append]
  simp only [List.map_map, Function.comp_def, plug_eval]

/-- The assumption's `take 25` is the check's first operand. -/
theorem req_ins_take (σ' : TVar → F) :
    (Xark.Templates.RequireLt25x82.template.ins σ').take 25
      = (List.range 25).map (fun j => σ' (.plug j)) := by
  rw [req_ins]
  simp

/-- The first 25 plugs of s545 are s548's: the check compares `sig` with `m − 1`. -/
theorem first25_window :
    ((callAt 545).plugs.drop 0).take 25 = ((callAt 548).plugs.drop 0).take 25 := by
  decide +kernel

/-- `sig`'s limbs, the range check's first operand, are below `2^82`. -/
theorem first25_bound (σ : ℕ → F)
    (hbit : ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1)
    {j : ℕ} (hj : j < 25) :
    ((ZLC.toF ((callAt 545).plugs.getD j (LC.cst 0))).eval σ).val < 2 ^ 82 := by
  have hgd : (callAt 545).plugs.getD j (LC.cst 0)
      = (callAt 548).plugs.getD (0 + j) (LC.cst 0) :=
    getD_of_window0 hj first25_window (LC.cst 0)
  rw [hgd, Nat.zero_add]
  interval_cases j
  · exact sigBound0 σ hbit
  · exact sigBound1 σ hbit
  · exact sigBound2 σ hbit
  · exact sigBound3 σ hbit
  · exact sigBound4 σ hbit
  · exact sigBound5 σ hbit
  · exact sigBound6 σ hbit
  · exact sigBound7 σ hbit
  · exact sigBound8 σ hbit
  · exact sigBound9 σ hbit
  · exact sigBound10 σ hbit
  · exact sigBound11 σ hbit
  · exact sigBound12 σ hbit
  · exact sigBound13 σ hbit
  · exact sigBound14 σ hbit
  · exact sigBound15 σ hbit
  · exact sigBound16 σ hbit
  · exact sigBound17 σ hbit
  · exact sigBound18 σ hbit
  · exact sigBound19 σ hbit
  · exact sigBound20 σ hbit
  · exact sigBound21 σ hbit
  · exact sigBound22 σ hbit
  · exact sigBound23 σ hbit
  · exact sigBound24 σ hbit

/-- The natural `limbs` sum, cast to `ℤ` and read in base `W = 2^82`. -/
theorem limbs_cast (a : ℕ → ℕ) (n : ℕ) :
    ((Xark.Templates.RequireLt.limbs a 82 n : ℕ) : ℤ)
      = ∑ j ∈ Finset.range n, (a j : ℤ) * W ^ j := by
  rw [Xark.Templates.RequireLt.limbs, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_mul]
  rfl

/-- **The range check's `Spec`**: `sig ≤ chainN − 1`. -/
theorem sig_le_minus_one (σ : ℕ → F) (h : Sat circuit σ) :
    val (limb sq0 σ 0) ≤ chainN σ - 1 := by
  have hb := hbit σ h
  have hsat : Xark.Templates.RequireLt25x82.template.Sat ((callAt 545).lift σ) := by
    have hc := call_sat_of h 545 (callAt 545) rfl (by decide)
    rwa [show (callAt 545).t = Xark.Templates.RequireLt25x82.template from rfl] at hc
  have ha : Xark.Templates.RequireLt25x82.Assumptions
      (Xark.Templates.RequireLt25x82.template.ins ((callAt 545).lift σ)) := by
    intro v hv
    rw [req_ins_take] at hv
    rcases List.mem_map.mp hv with ⟨j, hj, rfl⟩
    exact first25_bound σ hb (List.mem_range.mp hj)
  have hspec := Xark.Templates.RequireLt25x82.soundness ((callAt 545).lift σ) ha hsat
  have hle0 : Xark.Templates.RequireLt.limbs
        (fun j => (((callAt 545).lift σ) (.plug j)).val) 82 25
      ≤ Xark.Templates.RequireLt.limbs
        (fun j => ((Xark.Templates.RequireLt.plugM 25 j).eval ((callAt 545).lift σ)).val)
        82 25 := by
    rw [← Xark.Templates.RequireLt.spec_iff Xark.Templates.RequireLt25x82.is_model]
    exact hspec
  have hle : Xark.Templates.RequireLt.limbs
        (fun j => (((callAt 545).lift σ) (.plug j)).val) 82 25
      ≤ Xark.Templates.RequireLt.limbs
        (fun j => (((callAt 545).lift σ) (.plug (25 + j))).val) 82 25 := by
    simpa [Xark.Templates.RequireLt.plugM, Xark.R1cs.LC.eval] using hle0
  have hleZ : ((Xark.Templates.RequireLt.limbs
        (fun j => (((callAt 545).lift σ) (.plug j)).val) 82 25 : ℕ) : ℤ)
      ≤ ((Xark.Templates.RequireLt.limbs
        (fun j => (((callAt 545).lift σ) (.plug (25 + j))).val) 82 25 : ℕ) : ℤ) := by
    exact_mod_cast hle
  rw [limbs_cast, limbs_cast] at hleZ
  have hleft : val (limb (callAt 545) σ 0)
      = ∑ j ∈ Finset.range 25, ((((callAt 545).lift σ) (.plug j)).val : ℤ) * W ^ j := by
    simp [val, limb, pv]
  have hright : val (limb (callAt 545) σ 25)
      = ∑ j ∈ Finset.range 25, ((((callAt 545).lift σ) (.plug (25 + j))).val : ℤ) * W ^ j :=
    rfl
  rw [← hleft, ← hright, val_minus_one σ h] at hleZ
  rw [val_limb_eq (c := callAt 545) (c' := sq0) (off := 0) (off' := 0) σ first25_window] at hleZ
  exact hleZ

/-- **`sig < n`**, at the limb level. -/
theorem chainSig_lt_chainN (σ : ℕ → F) (h : Sat circuit σ) :
    val (limb sq0 σ 0) < chainN σ := by
  have hle := sig_le_minus_one σ h
  have hpos : 0 < chainN σ :=
    lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2 ^ 2047) (n_bits σ h).1
  omega

/-- **`sig < n`** over the signature's bytes and the modulus' limb vector. -/
theorem chainSig_bytes_lt_chainN (σ : ℕ → F) (h : Sat circuit σ) :
    (∑ i ∈ Finset.range 256, ((σ (256 + i)).val : ℤ) * 256 ^ (255 - i)) < chainN σ := by
  rw [← chainSig_eq_bytes σ h]
  exact chainSig_lt_chainN σ h

/-- **`sig < n`** over the public bytes: both operands are the big-endian integers the
circuit's inputs carry. -/
theorem chainSig_bytes_lt_bytes (σ : ℕ → F) (h : Sat circuit σ) :
    (∑ i ∈ Finset.range 256, ((σ (256 + i)).val : ℤ) * 256 ^ (255 - i))
      < ∑ i ∈ Finset.range 256, ((σ i).val : ℤ) * 256 ^ (255 - i) := by
  rw [← chainSig_eq_bytes σ h, ← chainN_eq_bytes σ h]
  exact chainSig_lt_chainN σ h

end Xark.Circuits.Rsa2048
