/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.FakeGlvCheck25519
import Formal.FakeGlvK1
import Formal.Ed25519Primes

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

/-!
# `xark_ed25519::fake_glv_check_25519`, proven over its exported rows

The scalar side of Ed25519's fake-GLV verifier (ePrint 2025/933, two-dimensional). Plugs:
`k = 0..3`, `S = 4..7` (4 × 64-bit limbs), `c_A = 8`, `c_B = 9` (`A = c_A − 2¹²⁹`,
`B = c_B − 2¹²⁹`), `W = 10..13`, the quotients `q₁ = 14..16`, `q₂ = 17..19` (limbs `64, 64, 6`
bits, `qᵢ − 2¹³³` the true quotient) and the biased carries `h₁ = 20..24`, `h₂ = 25..29`.
The rows: `to_bits` of `c_A`, `c_B` (130 bits, the outputs `d_A`, `d_B`), of `W`'s limbs (the
output `w_B`) and of the quotient limbs; `(c_B − 2¹²⁹)·w = 1`; and the two carry chains of
`A + k·B − q₁'·L` and `W + S·B − q₂'·L` in base `2⁶⁴` (`zero_chain`), the products `kᵢ·Bⱼ`,
`Sᵢ·Bⱼ` as hinted variables, each carry `h − 2⁶⁷` with `h < 2⁶⁸`.
-/

namespace Xark.Templates.FakeGlvCheck25519

open Xark.Template Xark.R1cs
open Xark.Templates.EcK1Check (norm eval_norm eval_var)
open Xark.Templates.MulCertK1 (bitRows lowOf)
export Xark.Templates.Add32 (IsBit)

/-! ### The model -/

def pv (i : ℕ) : LC := LC.var (.plug i)
def wv (i : ℕ) : LC := LC.var (.wit i)

/-- `L`'s 64-bit limbs. -/
def Lz (j : ℕ) : ℤ := [6346243789798364141, 1503914060200516822, 0, 1152921504606846976].getD j 0

def lsum (ls : List LC) : LC := ⟨(ls.map (·.const)).sum, ls.flatMap (·.terms)⟩
def lsc (c : F) (l : LC) : LC := ⟨c * l.const, l.terms.map fun t => (c * t.1, t.2)⟩
def l0 : LC := ⟨0, []⟩

/-- Limb `j` of `c − 2¹²⁹` read from `c`'s bits (`c` at plug `p`, bits `1..129` at `o..`). -/
def cLC (p o j : ℕ) : LC :=
  match j with
  | 0 => ⟨0, (1, .plug p) :: (List.range 66).map fun i => (-(2 ^ (64 + i) : F), .wit (o + 63 + i))⟩
  | 1 => ⟨0, (List.range 64).map fun i => ((2 ^ i : F), .wit (o + 63 + i))⟩
  | _ => ⟨-2, [(1, .wit (o + 127)), (2, .wit (o + 128))]⟩

def bLC (j : ℕ) : LC := cLC 9 129 j

/-- `qⱼ'` (the quotient's limb, the top one less `32 = 2¹³³/2¹²⁸`). -/
def qOff (j : ℕ) : F := if j = 2 then 32 else 0

/-- The pairs `(i, j)`, `i < 4`, `j < 3`, of column `m`. -/
def pairsOf (m : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun i => (List.range 3).filterMap fun j => if i + j = m then some (i, j) else none

/-- Column `m` of `a + x·B − q'·L`: `a`'s limb, the products `xᵢ·Bⱼ` (variables from `pw`),
`−Lᵢ·q'ⱼ` (`q` at plugs `qb..`). -/
def colLC (aT : ℕ → LC) (pw qb m : ℕ) : LC :=
  lsum (aT m :: (pairsOf m).map (fun p => wv (pw + 3 * p.1 + p.2)) ++
    (pairsOf m).map fun p => lsc (-(Lz p.1 : F)) ⟨-qOff p.2, [(1, .plug (qb + p.2))]⟩)

def carry (hb m : ℕ) : LC := ⟨-(2 ^ 67), [(1, .plug (hb + m))]⟩

def stepLC (aT : ℕ → LC) (pw qb hb m : ℕ) : LC :=
  lsum [colLC aT pw qb m, if m = 0 then l0 else carry hb (m - 1), lsc (-(2 ^ 64)) (carry hb m)]
def lastLC (aT : ℕ → LC) (pw qb hb : ℕ) : LC := lsum [colLC aT pw qb 5, carry hb 4]

def eqRow (l : LC) : Row := ⟨norm l, ⟨1, []⟩, ⟨0, []⟩⟩

def chainRows (aT : ℕ → LC) (pw qb hb w : ℕ) : List Row :=
  ((List.range 5).flatMap fun m =>
    bitRows (pv (hb + m)) (w + 67 * m) 67 ++ [eqRow (stepLC aT pw qb hb m)]) ++
    [eqRow (lastLC aT pw qb hb)]

def prodRows (pw xb : ℕ) : List Row :=
  (List.range 4).flatMap fun i => (List.range 3).map fun j => ⟨pv (xb + i), bLC j, wv (pw + 3 * i + j)⟩

def aT₁ (m : ℕ) : LC := if m < 3 then cLC 8 0 m else l0
def aT₂ (m : ℕ) : LC := if m < 4 then pv (10 + m) else l0

def bitBlock : List Row :=
  bitRows (pv 8) 0 129 ++ bitRows (pv 9) 129 129 ++
    ((List.range 4).flatMap fun i => bitRows (pv (10 + i)) (258 + 63 * i) 63) ++
    (List.range 2).flatMap fun t =>
      bitRows (pv (14 + 3 * t)) (510 + 131 * t) 63 ++ bitRows (pv (15 + 3 * t)) (573 + 131 * t) 63 ++
        bitRows (pv (16 + 3 * t)) (636 + 131 * t) 5

def invLC : LC := ⟨-(2 ^ 129), [(1, .plug 9)]⟩

def modelRows : List Row :=
  bitBlock ++ [⟨invLC, wv 772, ⟨1, []⟩⟩] ++ prodRows 774 0 ++ chainRows aT₁ 774 14 20 786 ++
    prodRows 1121 4 ++ chainRows aT₂ 1121 17 25 1133
def modelOutputs : List LC :=
  (lowOf (pv 8) 0 129 :: (List.range 129).map wv) ++
    (lowOf (pv 9) 129 129 :: (List.range 129).map fun i => wv (129 + i)) ++
    (List.range 4).flatMap fun i =>
      lowOf (pv (10 + i)) (258 + 63 * i) 63 :: (List.range 63).map fun b => wv (258 + 63 * i + b)

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows := by decide +kernel
set_option maxRecDepth 100000 in
theorem outputs_eq : template.outputs = modelOutputs := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 30).map fun j => LC.var (.plug j) := by
  decide +kernel

/-! ### Bits as integers -/

instance : Fact (Nat.Prime r) := bn254_r_prime

open Xark.Templates.Add32 (isBit_val isBit_of_mul_self word_lt sum_map_range)
open Finset

/-- `Σ_{i<n} 2ⁱ·bᵢ` over the variables `o..o + n − 1`, at their canonical values. -/
def bitval (σ : TVar → F) (o n : ℕ) : ℕ := ∑ i ∈ range n, 2 ^ i * (σ (.wit (o + i))).val

theorem bitval_lt (σ : TVar → F) (o n : ℕ) (hb : ∀ i < n, IsBit (σ (.wit (o + i)))) :
    bitval σ o n < 2 ^ n := word_lt _ n fun i hi => isBit_val (hb i hi)

theorem cast_bitval (σ : TVar → F) (o n : ℕ) :
    ((bitval σ o n : ℕ) : F) = ∑ i ∈ range n, 2 ^ i * σ (.wit (o + i)) := by
  simp [bitval]

theorem bools (x : LC) (o m : ℕ) (σ : TVar → F) (h : Xark.R1cs.Sat (bitRows x o m) σ) :
    (∀ i < m, IsBit (σ (.wit (o + i)))) ∧ IsBit ((lowOf x o m).eval σ) := by
  obtain ⟨hb, hl⟩ := (Xark.Templates.MulCertK1.sat_bitRows x o m σ).mp h
  exact ⟨fun i hi => isBit_of_mul_self (hb i hi), ToBits.isBit_of_mul_sub_one hl⟩

/-- `c − 2¹²⁹`'s limbs as integers: `[low + 2·b₀..₆₂, b₆₃..₁₂₆, b₁₂₇ + 2b₁₂₈ − 2]`. -/
def cz (σ : TVar → F) (p o : ℕ) : ℕ → ℤ
  | 0 => (((lowOf (pv p) o 129).eval σ).val : ℤ) + 2 * bitval σ o 63
  | 1 => bitval σ (o + 63) 64
  | _ => (bitval σ (o + 127) 2 : ℤ) - 2

theorem sum_split (g : ℕ → F) :
    ∑ i ∈ range 129, g i = ∑ i ∈ range 63, g i + ∑ i ∈ range 66, g (63 + i) := by
  rw [show 129 = 63 + 66 by rfl, Finset.sum_range_add]

theorem sum_split' (g : ℕ → F) :
    ∑ i ∈ range 66, g i = ∑ i ∈ range 64, g i + g 64 + g 65 := by
  rw [show 66 = 64 + 1 + 1 by rfl, Finset.sum_range_succ, Finset.sum_range_succ]

theorem sum_neg' (n : ℕ) (g : ℕ → F) : ∑ i ∈ range n, -g i = -∑ i ∈ range n, g i := by
  simp [Finset.sum_neg_distrib]

theorem two_sum (o : ℕ) (σ : TVar → F) (n : ℕ) :
    2 * ∑ i ∈ range n, 2 ^ i * σ (.wit (o + i)) = ∑ i ∈ range n, 2 ^ (i + 1) * σ (.wit (o + i)) := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem high_sum (o : ℕ) (σ : TVar → F) :
    ∑ i ∈ range 129, (2 : F) ^ (i + 1) * σ (.wit (o + i)) =
      ∑ i ∈ range 63, 2 ^ (i + 1) * σ (.wit (o + i)) +
        ∑ i ∈ range 66, 2 ^ (64 + i) * σ (.wit (o + 63 + i)) := by
  rw [show 129 = 63 + 66 by rfl, Finset.sum_range_add]
  congr 1

theorem eval_cLC (σ : TVar → F) (p o j : ℕ) (hj : j < 3) :
    (cLC p o j).eval σ = ((cz σ p o j : ℤ) : F) := by
  have hlow := Xark.Templates.MulCertK1.eval_lowOf (pv p) o 129 σ
  interval_cases j
  · simp only [cz, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
      ZMod.natCast_zmod_val, cast_bitval]
    rw [hlow, two_sum]
    simp only [cLC, LC.eval, List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
      sum_map_range, pv, eval_var, neg_mul, sum_neg', Nat.cast_pow, Nat.cast_ofNat, LC.var,
      List.map_nil, List.sum_nil, one_mul, zero_add, add_zero]
    linear_combination high_sum o σ
  · simp only [cLC, cz, LC.eval, List.map_map, Function.comp_def, sum_map_range, Int.cast_natCast,
      cast_bitval, zero_add]
  · simp only [cLC, cz, LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Int.cast_sub, Int.cast_natCast, cast_bitval, Int.cast_ofNat, Finset.sum_range_succ,
      Finset.sum_range_zero]
    ring_nf

theorem cz_bounds (σ : TVar → F) (p o : ℕ) (h : Xark.R1cs.Sat (bitRows (pv p) o 129) σ) :
    ∀ j < 3, -2 ≤ cz σ p o j ∧ cz σ p o j < 2 ^ 64 := by
  obtain ⟨hb, hl⟩ := bools _ o 129 σ h
  have b1 := bitval_lt σ o 63 fun i hi => hb i (by omega)
  have b2 := bitval_lt σ (o + 63) 64 fun i hi => by rw [add_assoc]; exact hb _ (by omega)
  have b3 := bitval_lt σ (o + 127) 2 fun i hi => by rw [add_assoc]; exact hb _ (by omega)
  have b0 := isBit_val hl
  intro j hj
  interval_cases j <;> simp only [cz] <;> omega

/-- `Σ 2^(64j)·cⱼ = c − 2¹²⁹` over the integers. -/
theorem cz_sum (σ : TVar → F) (p o : ℕ) (h : Xark.R1cs.Sat (bitRows (pv p) o 129) σ) :
    cz σ p o 0 + 2 ^ 64 * cz σ p o 1 + 2 ^ 128 * cz σ p o 2 = ((σ (.plug p)).val : ℤ) - 2 ^ 129 := by
  have hb := cz_bounds σ p o h
  obtain ⟨_, _⟩ := hb 0 (by norm_num); obtain ⟨_, _⟩ := hb 1 (by norm_num)
  obtain ⟨_, _⟩ := hb 2 (by norm_num)
  have hF : ((cz σ p o 0 + 2 ^ 64 * cz σ p o 1 + 2 ^ 128 * (cz σ p o 2 + 2) : ℤ) : F) =
      (((σ (.plug p)).val : ℤ) : F) := by
    push_cast
    rw [← eval_cLC σ p o 0 (by norm_num), ← eval_cLC σ p o 1 (by norm_num),
      ← eval_cLC σ p o 2 (by norm_num)]
    simp only [cLC, LC.eval, List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
      sum_map_range, List.map_nil, List.sum_nil, ZMod.natCast_val, ZMod.cast_id', id, sum_split',
      neg_mul, sum_neg', zero_add]
    have k3 : (2 : F) ^ 64 * ∑ i ∈ range 64, 2 ^ i * σ (.wit (o + 63 + i)) =
        ∑ i ∈ range 64, 2 ^ (64 + i) * σ (.wit (o + 63 + i)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [show o + 63 + 64 = o + 127 by omega, show o + 63 + 65 = o + 128 by omega]
    linear_combination k3
  have hv := Xark.Templates.MulCertK1.bits_sound _ o 129 (by norm_num) σ h
  simp only [pv, eval_var] at hv
  have hv' : ((σ (.plug p)).val : ℤ) < 2 ^ 130 := by exact_mod_cast hv
  have := Xark.Templates.MulCertK1.lift
    (cz σ p o 0 + 2 ^ 64 * cz σ p o 1 + 2 ^ 128 * (cz σ p o 2 + 2) - ((σ (.plug p)).val : ℤ))
    (by rw [Int.cast_sub, hF, sub_self])
    (by rw [Xark.Templates.MulCertK1.r_eq]; omega)
    (by rw [Xark.Templates.MulCertK1.r_eq]; omega)
  linarith

/-! ### The carry chains -/

theorem eval_lsum (ls : List LC) (σ : TVar → F) : (lsum ls).eval σ = (ls.map (·.eval σ)).sum := by
  induction ls with
  | nil => simp [lsum, LC.eval]
  | cons l ls ih =>
    simp only [lsum, LC.eval, List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
      List.sum_append] at ih ⊢
    rw [← ih]; ring

theorem eval_lsc (c : F) (l : LC) (σ : TVar → F) : (lsc c l).eval σ = c * l.eval σ := by
  simp only [lsc, LC.eval, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]
  ring

def qOffZ (j : ℕ) : ℤ := if j = 2 then 32 else 0

/-- Column `m` over the integers: `a`'s limb, `Σ xᵢ·bⱼ`, `−Σ Lᵢ·(qⱼ − offⱼ)`. -/
def colZ (az xz bz qz : ℕ → ℤ) (m : ℕ) : ℤ :=
  az m + ((pairsOf m).map fun p => xz p.1 * bz p.2).sum -
    ((pairsOf m).map fun p => Lz p.1 * (qz p.2 - qOffZ p.2)).sum

def stepZ (az xz bz qz hz : ℕ → ℤ) (m : ℕ) : ℤ :=
  colZ az xz bz qz m + (if m = 0 then 0 else hz (m - 1) - 2 ^ 67) - 2 ^ 64 * (hz m - 2 ^ 67)
def lastZ (az xz bz qz hz : ℕ → ℤ) : ℤ := colZ az xz bz qz 5 + (hz 4 - 2 ^ 67)

theorem lsum_neg {α : Type*} (l : List α) (f : α → F) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem mem_pairsOf (m : ℕ) (p : ℕ × ℕ) (hp : p ∈ pairsOf m) : p.1 < 4 ∧ p.2 < 3 := by
  simp only [pairsOf, List.mem_flatMap, List.mem_range, List.mem_filterMap] at hp
  obtain ⟨i, hi, j, hj, h⟩ := hp
  split_ifs at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨hi, hj⟩

/-- The chain's linear forms evaluate to the integer columns' casts. -/
theorem eval_stepLC (aT : ℕ → LC) (pw qb hb : ℕ) (σ : TVar → F) (az xz bz qz hz : ℕ → ℤ)
    (ha : ∀ m, (aT m).eval σ = ((az m : ℤ) : F))
    (hp : ∀ i < 4, ∀ j < 3, σ (.wit (pw + 3 * i + j)) = ((xz i * bz j : ℤ) : F))
    (hq : ∀ j, σ (.plug (qb + j)) = ((qz j : ℤ) : F)) (hh : ∀ m, σ (.plug (hb + m)) = ((hz m : ℤ) : F))
    (m : ℕ) :
    (stepLC aT pw qb hb m).eval σ = ((stepZ az xz bz qz hz m : ℤ) : F) ∧
      (lastLC aT pw qb hb).eval σ = ((lastZ az xz bz qz hz : ℤ) : F) := by
  have hc : ∀ m, (colLC aT pw qb m).eval σ = ((colZ az xz bz qz m : ℤ) : F) := fun m => by
    have hP : ((pairsOf m).map fun p => σ (.wit (pw + 3 * p.1 + p.2))) =
        (pairsOf m).map fun p => ((xz p.1 * bz p.2 : ℤ) : F) := List.map_congr_left fun p hpm =>
      hp _ (mem_pairsOf m p hpm).1 _ (mem_pairsOf m p hpm).2
    simp only [colLC, eval_lsum, List.map_cons, List.map_append, List.sum_cons, List.sum_append,
      List.map_map, Function.comp_def, ha, wv, eval_var, hP, eval_lsc, colZ, Int.cast_add,
      Int.cast_sub, Int.cast_list_sum, Int.cast_mul]
    have hq' : ∀ p : ℕ × ℕ, (-(Lz p.1 : F)) * LC.eval ⟨-qOff p.2, [(1, .plug (qb + p.2))]⟩ σ =
        -(((Lz p.1 * (qz p.2 - qOffZ p.2) : ℤ) : F)) := fun p => by
      simp only [LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul,
        add_zero, hq, qOff, qOffZ]
      split_ifs <;> push_cast <;> ring
    simp only [hq']
    rw [sub_eq_add_neg, lsum_neg]
    congr 3
    refine List.map_congr_left fun p _ => ?_
    push_cast; ring
  have hcr : ∀ m, (carry hb m).eval σ = ((hz m - 2 ^ 67 : ℤ) : F) := fun m => by
    simp [carry, LC.eval, hh]; ring
  constructor
  · simp only [stepLC, eval_lsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hc,
      eval_lsc, hcr, stepZ]
    split_ifs
    · simp [l0, LC.eval]; ring
    · rw [hcr]; simp [l0, LC.eval]; ring
  · simp only [lastLC, eval_lsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hc,
      hcr, lastZ]
    push_cast; ring

theorem pairs_eq : pairsOf 0 = [(0, 0)] ∧ pairsOf 1 = [(0, 1), (1, 0)] ∧
    pairsOf 2 = [(0, 2), (1, 1), (2, 0)] ∧ pairsOf 3 = [(1, 2), (2, 1), (3, 0)] ∧
    pairsOf 4 = [(2, 2), (3, 1)] ∧ pairsOf 5 = [(3, 2)] := by decide

theorem Lz_eq : Lz 0 = 6346243789798364141 ∧ Lz 1 = 1503914060200516822 ∧ Lz 2 = 0 ∧
    Lz 3 = 1152921504606846976 := by decide

/-- `L`. -/
def Lnum : ℤ := 7237005577332262213973186563042994240857116359379907606001950938285454250989

/-- **The chain's integer content**: its six rows force `a + x·B = q'·L` over `ℤ`. -/
theorem chain_int (az xz bz qz hz : ℕ → ℤ) (h0 : az 4 = 0) (h1 : az 5 = 0)
    (hs : ∀ m < 5, stepZ az xz bz qz hz m = 0) (hl : lastZ az xz bz qz hz = 0) :
    az 0 + 2 ^ 64 * az 1 + 2 ^ 128 * az 2 + 2 ^ 192 * az 3 +
        (xz 0 + 2 ^ 64 * xz 1 + 2 ^ 128 * xz 2 + 2 ^ 192 * xz 3) * (bz 0 + 2 ^ 64 * bz 1 + 2 ^ 128 * bz 2) =
      (qz 0 + 2 ^ 64 * qz 1 + 2 ^ 128 * qz 2 - 2 ^ 133) * Lnum := by
  have e0 := hs 0 (by norm_num); have e1 := hs 1 (by norm_num); have e2 := hs 2 (by norm_num)
  have e3 := hs 3 (by norm_num); have e4 := hs 4 (by norm_num)
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pairs_eq
  obtain ⟨l0, l1, l2, l3⟩ := Lz_eq
  simp only [stepZ, lastZ, colZ, p0, p1, p2, p3, p4, p5, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, l0, l1, l2, l3, qOffZ, h0, h1] at e0 e1 e2 e3 e4 hl
  norm_num at e0 e1 e2 e3 e4 hl
  simp only [Lnum]
  linear_combination e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3 + 2 ^ 256 * e4 + 2 ^ 320 * hl

/-- Every column is below `2⁶⁴ + 6·2¹²⁸` in absolute value. -/
theorem colZ_bd (az xz bz qz : ℕ → ℤ) (ha : ∀ m < 6, -2 ≤ az m ∧ az m < 2 ^ 64)
    (hx : ∀ i < 4, 0 ≤ xz i ∧ xz i < 2 ^ 64) (hb : ∀ j < 3, -2 ≤ bz j ∧ bz j < 2 ^ 64)
    (hq : ∀ j < 3, 0 ≤ qz j ∧ qz j < 2 ^ 64) :
    ∀ m < 6, |colZ az xz bz qz m| ≤ 2 ^ 64 + 6 * 2 ^ 128 := by
  have hp : ∀ i < 4, ∀ j < 3, |xz i * bz j| ≤ 2 ^ 128 := fun i hi j hj => by
    obtain ⟨_, _⟩ := hx i hi; obtain ⟨_, _⟩ := hb j hj
    rw [abs_le]; constructor <;> nlinarith
  have hl : ∀ i < 4, ∀ j < 3, |Lz i * (qz j - qOffZ j)| ≤ 2 ^ 128 := fun i hi j hj => by
    obtain ⟨_, _⟩ := hq j hj
    have hL : 0 ≤ Lz i ∧ Lz i < 2 ^ 63 := by interval_cases i <;> decide
    have ho : 0 ≤ qOffZ j ∧ qOffZ j ≤ 32 := by unfold qOffZ; split_ifs <;> norm_num
    obtain ⟨_, _⟩ := hL; obtain ⟨_, _⟩ := ho
    rw [abs_le]; constructor <;> nlinarith
  have hmem : ∀ m, ∀ p ∈ pairsOf m, p.1 < 4 ∧ p.2 < 3 := mem_pairsOf
  have hlen : ∀ m < 6, (pairsOf m).length ≤ 3 := by decide
  have hsum : ∀ (l : List (ℕ × ℕ)) (f : ℕ × ℕ → ℤ), (∀ p ∈ l, |f p| ≤ 2 ^ 128) →
      |(l.map f).sum| ≤ l.length * 2 ^ 128 := fun l f hf => by
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := hf p (by simp); have := ih fun q hq => hf q (by simp [hq])
      calc |f p + (l.map f).sum| ≤ |f p| + |(l.map f).sum| := abs_add_le _ _
        _ ≤ _ := by push_cast; linarith
  intro m hm
  have h1 := hsum (pairsOf m) (fun p => xz p.1 * bz p.2) fun p hpm =>
    hp _ (hmem m p hpm).1 _ (hmem m p hpm).2
  have h2 := hsum (pairsOf m) (fun p => Lz p.1 * (qz p.2 - qOffZ p.2)) fun p hpm =>
    hl _ (hmem m p hpm).1 _ (hmem m p hpm).2
  have h3 : ((pairsOf m).length : ℤ) ≤ 3 := by exact_mod_cast hlen m hm
  have h4 : |az m| ≤ 2 ^ 64 := by obtain ⟨_, _⟩ := ha m hm; rw [abs_le]; constructor <;> linarith
  unfold colZ
  calc |az m + ((pairsOf m).map fun p => xz p.1 * bz p.2).sum -
        ((pairsOf m).map fun p => Lz p.1 * (qz p.2 - qOffZ p.2)).sum|
      ≤ |az m| + |((pairsOf m).map fun p => xz p.1 * bz p.2).sum| +
        |((pairsOf m).map fun p => Lz p.1 * (qz p.2 - qOffZ p.2)).sum| := by
        refine (abs_sub _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ _ := by nlinarith

/-- A step's or the last row's value is far below `r`, so its row holds over `ℤ`. -/
theorem stepZ_bound (az xz bz qz hz : ℕ → ℤ) (ha : ∀ m < 6, -2 ≤ az m ∧ az m < 2 ^ 64)
    (hx : ∀ i < 4, 0 ≤ xz i ∧ xz i < 2 ^ 64) (hb : ∀ j < 3, -2 ≤ bz j ∧ bz j < 2 ^ 64)
    (hq : ∀ j < 3, 0 ≤ qz j ∧ qz j < 2 ^ 64) (hh : ∀ m < 5, 0 ≤ hz m ∧ hz m < 2 ^ 68) :
    (∀ m < 5, |stepZ az xz bz qz hz m| < 2 ^ 134) ∧ |lastZ az xz bz qz hz| < 2 ^ 134 := by
  have hcol := colZ_bd az xz bz qz ha hx hb hq
  constructor
  · intro m hm
    have := hcol m (by omega)
    obtain ⟨_, _⟩ := hh m hm
    rw [abs_lt]; rw [abs_le] at this
    unfold stepZ
    split_ifs with h0
    · constructor <;> linarith
    · obtain ⟨_, _⟩ := hh (m - 1) (by omega); constructor <;> linarith
  · have := hcol 5 (by norm_num)
    obtain ⟨_, _⟩ := hh 4 (by norm_num)
    rw [abs_lt]; rw [abs_le] at this
    unfold lastZ; constructor <;> linarith

/-! ### Soundness -/

theorem sat_append (a b : List Row) (σ : TVar → F) :
    Xark.R1cs.Sat (a ++ b) σ ↔ Xark.R1cs.Sat a σ ∧ Xark.R1cs.Sat b σ := by
  simp only [Xark.R1cs.Sat, List.mem_append, or_imp, forall_and]

theorem sat_flatMap {α : Type*} (l : List α) (f : α → List Row) (σ : TVar → F) :
    Xark.R1cs.Sat (l.flatMap f) σ ↔ ∀ x ∈ l, Xark.R1cs.Sat (f x) σ := by
  simp only [Xark.R1cs.Sat, List.mem_flatMap]
  exact ⟨fun h x hx r hr => h r ⟨x, hx, hr⟩, fun h r ⟨x, hx, hr⟩ => h x hx r hr⟩

theorem sat_single (r : Row) (σ : TVar → F) : Xark.R1cs.Sat [r] σ ↔ r.Sat σ := by
  simp [Xark.R1cs.Sat]

theorem sat_eqRow (l : LC) (σ : TVar → F) : (eqRow l).Sat σ ↔ l.eval σ = 0 := by
  simp only [Row.Sat, eqRow, eval_norm]
  simp [LC.eval]

/-- A range check's plug is below `2^(m+1)`. -/
theorem plug_lt (i o m : ℕ) (hm : m + 1 ≤ 253) (σ : TVar → F) (h : Xark.R1cs.Sat (bitRows (pv i) o m) σ) :
    (σ (.plug i)).val < 2 ^ (m + 1) := by
  have := Xark.Templates.MulCertK1.bits_sound _ o m hm σ h
  rwa [pv, eval_var] at this

theorem plug_lt' (i o m : ℕ) (hm : m + 1 ≤ 253) (σ : TVar → F)
    (h : Xark.R1cs.Sat (bitRows (pv i) o m) σ) : ((σ (.plug i)).val : ℤ) < 2 ^ (m + 1) := by
  exact_mod_cast plug_lt i o m hm σ h

/-- The product rows hold iff every product variable is its product. -/
theorem sat_prodRows (pw xb : ℕ) (σ : TVar → F) (h : Xark.R1cs.Sat (prodRows pw xb) σ) :
    ∀ i < 4, ∀ j < 3, σ (.wit (pw + 3 * i + j)) = σ (.plug (xb + i)) * (bLC j).eval σ := by
  intro i hi j hj
  have := h _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩)
  simp only [Row.Sat, pv, wv, eval_var] at this
  exact this.symm

/-- **A chain's rows force its integer identity**, given the product variables' and plugs'
integer values within their bounds. -/
theorem chain_sound (aT : ℕ → LC) (pw qb hb w : ℕ) (σ : TVar → F) (az xz bz qz : ℕ → ℤ)
    (h : Xark.R1cs.Sat (chainRows aT pw qb hb w) σ)
    (ha : ∀ m, (aT m).eval σ = ((az m : ℤ) : F)) (ha4 : az 4 = 0) (ha5 : az 5 = 0)
    (hab : ∀ m < 6, -2 ≤ az m ∧ az m < 2 ^ 64)
    (hp : ∀ i < 4, ∀ j < 3, σ (.wit (pw + 3 * i + j)) = ((xz i * bz j : ℤ) : F))
    (hx : ∀ i < 4, 0 ≤ xz i ∧ xz i < 2 ^ 64) (hbb : ∀ j < 3, -2 ≤ bz j ∧ bz j < 2 ^ 64)
    (hq : ∀ j, σ (.plug (qb + j)) = ((qz j : ℤ) : F)) (hqb : ∀ j < 3, 0 ≤ qz j ∧ qz j < 2 ^ 64) :
    az 0 + 2 ^ 64 * az 1 + 2 ^ 128 * az 2 + 2 ^ 192 * az 3 +
        (xz 0 + 2 ^ 64 * xz 1 + 2 ^ 128 * xz 2 + 2 ^ 192 * xz 3) * (bz 0 + 2 ^ 64 * bz 1 + 2 ^ 128 * bz 2) =
      (qz 0 + 2 ^ 64 * qz 1 + 2 ^ 128 * qz 2 - 2 ^ 133) * Lnum := by
  rw [chainRows, sat_append, sat_flatMap, sat_single, sat_eqRow] at h
  obtain ⟨hs, hl⟩ := h
  have hs' : ∀ m < 5, Xark.R1cs.Sat (bitRows (pv (hb + m)) (w + 67 * m) 67) σ ∧
      (stepLC aT pw qb hb m).eval σ = 0 := fun m hm => by
    have := hs m (List.mem_range.mpr hm)
    rw [sat_append, sat_single, sat_eqRow] at this
    exact this
  set hz : ℕ → ℤ := fun m => ((σ (.plug (hb + m))).val : ℤ)
  have hh : ∀ m, σ (.plug (hb + m)) = ((hz m : ℤ) : F) := fun m => by simp [hz]
  have hhb : ∀ m < 5, 0 ≤ hz m ∧ hz m < 2 ^ 68 := fun m hm =>
    ⟨Int.natCast_nonneg _, lt_of_lt_of_le (plug_lt' _ _ 67 (by norm_num) σ (hs' m hm).1) (by norm_num)⟩
  obtain ⟨bs, bl⟩ := stepZ_bound az xz bz qz hz hab hx hbb hqb hhb
  have ev := fun m => eval_stepLC aT pw qb hb σ az xz bz qz hz ha hp hq hh m
  have r_lt : (2 : ℤ) ^ 134 < r := by rw [Xark.Templates.MulCertK1.r_eq]; norm_num
  refine chain_int az xz bz qz hz ha4 ha5 (fun m hm => ?_) ?_
  · have e := (ev m).1; rw [(hs' m hm).2] at e
    have := bs m hm; rw [abs_lt] at this
    exact Xark.Templates.MulCertK1.lift _ e.symm (by linarith) (by linarith)
  · have e := (ev 0).2; rw [hl] at e
    rw [abs_lt] at bl
    exact Xark.Templates.MulCertK1.lift _ e.symm (by linarith) (by linarith)

/-- The input assumption: the limbs of `k` and `S` (plugs `0..7`) are below `2⁶⁴`. In
`eddsa_verify` they are recomposed from the scalars' boolean bits (`limbs64`). -/
def Assumptions (ins : List F) : Prop := ∀ i < 8, (ins.getD i 0).val < 2 ^ 64

def ival (ins : List F) (i : ℕ) : ℤ := ((ins.getD i 0).val : ℤ)
/-- A 4-limb number from input `b`. -/
def N4 (ins : List F) (b : ℕ) : ℤ :=
  ival ins b + 2 ^ 64 * ival ins (b + 1) + 2 ^ 128 * ival ins (b + 2) + 2 ^ 192 * ival ins (b + 3)

/-- The outputs: the 130 bits of `c_A`, of `c_B`, then the 64 bits of each limb of `W`. -/
def digits (ins : List F) : List F :=
  (List.range 130).map (bitOf (ins.getD 8 0)) ++ (List.range 130).map (bitOf (ins.getD 9 0)) ++
    (List.range 4).flatMap fun i => (List.range 64).map (bitOf (ins.getD (10 + i) 0))

/-- `c_A`, `c_B < 2¹³⁰`, `W`'s limbs below `2⁶⁴`, the outputs their bits, and for
`A = c_A − 2¹²⁹`, `B = c_B − 2¹²⁹`: `A + k·B ≡ 0`, `W + S·B ≡ 0 (mod L)` and `B ≠ 0`. -/
def Spec (ins outs : List F) : Prop :=
  ival ins 8 < 2 ^ 130 ∧ ival ins 9 < 2 ^ 130 ∧ (∀ i < 4, ival ins (10 + i) < 2 ^ 64) ∧
    outs = digits ins ∧ Lnum ∣ (ival ins 8 - 2 ^ 129) + N4 ins 0 * (ival ins 9 - 2 ^ 129) ∧
    Lnum ∣ N4 ins 10 + N4 ins 4 * (ival ins 9 - 2 ^ 129) ∧ ival ins 9 ≠ 2 ^ 129

theorem getD_ins (σ : TVar → F) (i : ℕ) (hi : i < 30) : (template.ins σ).getD i 0 = σ (.plug i) := by
  rw [Template.ins, inputs_eq, List.getD_eq_getElem _ _ (by simpa using hi)]; simp [eval_var]

theorem ival_eq (σ : TVar → F) (i : ℕ) (hi : i < 30) :
    ival (template.ins σ) i = ((σ (.plug i)).val : ℤ) := by rw [ival, getD_ins σ i hi]

open Xark.Templates.FakeGlvCheckK1 (bits_out)

set_option maxRecDepth 100000 in
theorem outs_eq (σ : TVar → F) (hb : Xark.R1cs.Sat bitBlock σ) :
    template.outs σ = digits (template.ins σ) := by
  simp only [bitBlock, sat_append, sat_flatMap] at hb
  obtain ⟨⟨⟨h8, h9⟩, hw⟩, -⟩ := hb
  rw [Template.outs, outputs_eq, modelOutputs, digits, getD_ins σ 8 (by norm_num),
    getD_ins σ 9 (by norm_num)]
  simp only [List.map_append, List.map_cons, List.map_map, Function.comp_def, wv, eval_var,
    List.map_flatMap, pv]
  have o8 := bits_out (pv 8) 0 129 (by norm_num) σ h8
  have o9 := bits_out (pv 9) 129 129 (by norm_num) σ h9
  simp only [zero_add, pv, eval_var, show 129 + 1 = 130 from rfl] at o8 o9
  rw [o8, o9]
  refine congrArg (List.map (bitOf (σ (.plug 8))) (List.range 130) ++
    List.map (bitOf (σ (.plug 9))) (List.range 130) ++ ·) (List.flatMap_congr fun i hi => ?_)
  have hi := List.mem_range.mp hi
  have := bits_out (pv (10 + i)) (258 + 63 * i) 63 (by norm_num) σ (hw i (List.mem_range.mpr hi))
  simp only [pv, eval_var] at this
  rw [getD_ins σ _ (by omega)]
  exact this

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [Template.Sat, rows_eq, modelRows] at h
  simp only [sat_append, sat_single] at h
  obtain ⟨⟨⟨⟨⟨hbb, hinv⟩, hp1⟩, hc1⟩, hp2⟩, hc2⟩ := h
  have hbb' := hbb
  simp only [bitBlock, sat_append, sat_flatMap] at hbb'
  obtain ⟨⟨⟨h8, h9⟩, hw⟩, hq⟩ := hbb'
  have hq' : ∀ t < 2, Xark.R1cs.Sat (bitRows (pv (14 + 3 * t)) (510 + 131 * t) 63) σ ∧
      Xark.R1cs.Sat (bitRows (pv (15 + 3 * t)) (573 + 131 * t) 63) σ ∧
      Xark.R1cs.Sat (bitRows (pv (16 + 3 * t)) (636 + 131 * t) 5) σ := fun t ht => by
    have := hq t (List.mem_range.mpr ht); exact ⟨this.1.1, this.1.2, this.2⟩
  have hk : ∀ i < 8, ((σ (.plug i)).val : ℤ) < 2 ^ 64 := fun i hi => by
    have := ha i hi; rw [getD_ins σ i (by omega)] at this; exact_mod_cast this
  set vz : ℕ → ℤ := fun i => ((σ (.plug i)).val : ℤ)
  have hvz : ∀ i, σ (.plug i) = ((vz i : ℤ) : F) := fun i => by simp [vz]
  have hbz := cz_bounds σ 9 129 h9
  have haz := cz_bounds σ 8 0 h8
  have prods : ∀ pw xb, Xark.R1cs.Sat (prodRows pw xb) σ →
      ∀ i < 4, ∀ j < 3, σ (.wit (pw + 3 * i + j)) = ((vz (xb + i) * cz σ 9 129 j : ℤ) : F) :=
    fun pw xb hp i hi j hj => by
      rw [sat_prodRows pw xb σ hp i hi j hj, show bLC j = cLC 9 129 j from rfl, eval_cLC σ 9 129 j hj,
        hvz]; push_cast; ring
  have qlt : ∀ t < 2, ∀ j < 3, 0 ≤ vz (14 + 3 * t + j) ∧ vz (14 + 3 * t + j) < 2 ^ 64 := by
    intro t ht j hj
    obtain ⟨a, b, c⟩ := hq' t ht
    refine ⟨Int.natCast_nonneg _, ?_⟩
    interval_cases j
    · simp only [vz, add_zero]
      exact lt_of_lt_of_le (plug_lt' _ _ 63 (by norm_num) σ a) (by norm_num)
    · simp only [vz]; rw [show 14 + 3 * t + 1 = 15 + 3 * t by omega]
      exact lt_of_lt_of_le (plug_lt' _ _ 63 (by norm_num) σ b) (by norm_num)
    · simp only [vz]; rw [show 14 + 3 * t + 2 = 16 + 3 * t by omega]
      exact lt_of_lt_of_le (plug_lt' _ _ 5 (by norm_num) σ c) (by norm_num)
  have wlt : ∀ i < 4, vz (10 + i) < 2 ^ 64 := fun i hi => by
    simp only [vz]
    exact lt_of_lt_of_le (plug_lt' _ _ 63 (by norm_num) σ (hw i (List.mem_range.mpr hi))) (by norm_num)
  -- chain 1: A + k·B = q₁'·L
  have e1 := chain_sound aT₁ 774 14 20 786 σ (fun m => if m < 3 then cz σ 8 0 m else 0) vz
    (cz σ 9 129) (fun j => vz (14 + j)) hc1
    (fun m => by unfold aT₁; split_ifs with hm
                 · exact eval_cLC σ 8 0 m hm
                 · simp [l0, LC.eval])
    (by simp) (by simp)
    (fun m hm => by split_ifs with h3
                    · exact haz m h3
                    · norm_num)
    (fun i hi j hj => by rw [prods 774 0 hp1 i hi j hj, zero_add])
    (fun i hi => ⟨Int.natCast_nonneg _, hk i (by omega)⟩) hbz (fun j => hvz _)
    (fun j hj => by simpa using qlt 0 (by norm_num) j hj)
  -- chain 2: W + S·B = q₂'·L
  have e2 := chain_sound aT₂ 1121 17 25 1133 σ (fun m => if m < 4 then vz (10 + m) else 0)
    (fun i => vz (4 + i)) (cz σ 9 129) (fun j => vz (17 + j)) hc2
    (fun m => by unfold aT₂; split_ifs with hm
                 · rw [pv, eval_var, hvz]
                 · simp [l0, LC.eval])
    (by simp) (by simp)
    (fun m hm => by split_ifs with h3
                    · exact ⟨by linarith [show (0 : ℤ) ≤ vz (10 + m) from Int.natCast_nonneg _], wlt m h3⟩
                    · norm_num)
    (fun i hi j hj => prods 1121 4 hp2 i hi j hj)
    (fun i hi => ⟨Int.natCast_nonneg _, hk (4 + i) (by omega)⟩) hbz (fun j => hvz _)
    (fun j hj => by simpa [show 17 + j = 14 + 3 * 1 + j by omega] using qlt 1 (by norm_num) j hj)
  simp only [show (0 : ℕ) < 3 from by norm_num, show (1 : ℕ) < 3 from by norm_num,
    show (2 : ℕ) < 3 from by norm_num, show ¬(3 : ℕ) < 3 from by norm_num, if_true, if_false,
    show (0 : ℕ) < 4 from by norm_num, show (1 : ℕ) < 4 from by norm_num,
    show (2 : ℕ) < 4 from by norm_num, show (3 : ℕ) < 4 from by norm_num] at e1 e2
  have sA := cz_sum σ 8 0 h8
  have sB := cz_sum σ 9 129 h9
  have r8 := plug_lt' 8 0 129 (by norm_num) σ h8
  have r9 := plug_lt' 9 129 129 (by norm_num) σ h9
  simp only [ival_eq σ _ (by omega : (8 : ℕ) < 30), ival_eq σ _ (by omega : (9 : ℕ) < 30), Spec, N4]
  refine ⟨lt_of_lt_of_le r8 (by norm_num), lt_of_lt_of_le r9 (by norm_num), fun i hi => by
      rw [ival_eq σ _ (by omega)]; exact wlt i hi, outs_eq σ hbb, ?_, ?_, ?_⟩
  · simp only [ival_eq σ _ (by omega : (0 : ℕ) < 30), ival_eq σ _ (by omega : (1 : ℕ) < 30),
      ival_eq σ _ (by omega : (2 : ℕ) < 30), ival_eq σ _ (by omega : (3 : ℕ) < 30)]
    refine ⟨vz 14 + 2 ^ 64 * vz 15 + 2 ^ 128 * vz 16 - 2 ^ 133, ?_⟩
    simp only [vz] at e1 sA sB ⊢
    rw [← sA, ← sB]; linear_combination e1
  · simp only [ival_eq σ _ (by omega : (4 : ℕ) < 30), ival_eq σ _ (by omega : (5 : ℕ) < 30),
      ival_eq σ _ (by omega : (6 : ℕ) < 30), ival_eq σ _ (by omega : (7 : ℕ) < 30),
      ival_eq σ _ (by omega : (10 : ℕ) < 30), ival_eq σ _ (by omega : (11 : ℕ) < 30),
      ival_eq σ _ (by omega : (12 : ℕ) < 30), ival_eq σ _ (by omega : (13 : ℕ) < 30)]
    refine ⟨vz 17 + 2 ^ 64 * vz 18 + 2 ^ 128 * vz 19 - 2 ^ 133, ?_⟩
    simp only [vz] at e2 sB ⊢
    rw [← sB]; linear_combination e2
  · intro h0
    rw [Row.Sat] at hinv
    simp only [invLC, wv, eval_var, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, one_mul, add_zero] at hinv
    have : σ (.plug 9) = 2 ^ 129 := by
      rw [← ZMod.natCast_zmod_val (σ (.plug 9))]
      have : (σ (.plug 9)).val = 2 ^ 129 := by exact_mod_cast h0
      rw [this]; push_cast; ring
    rw [this] at hinv
    simp at hinv

end Xark.Templates.FakeGlvCheck25519

namespace Xark.FakeGlv

/-- **The group side of cofactored fake GLV.** In a group that `h·n` kills (`n` prime, as
Ed25519's `8·L`), the circuit's `[h]·(A·Q − B·R − W·G) = O` with `A ≡ −k·B`, `W ≡ −S·B (mod n)`
and `B ≢ 0` (`FakeGlvCheck25519.soundness`) is exactly the cofactored equation
`[h]·([S]G − [k]Q − R) = O`: `[h]·(…)` lies in the `n`-torsion, where `B` is invertible. So
a torsion offset is accepted exactly when cofactored verification accepts it. -/
theorem verify_sound_cofactored {G : Type*} [AddCommGroup G] (n h : ℕ) (hp : n.Prime)
    (hn : ∀ x : G, ((h * n : ℕ) : ℤ) • x = 0) (g q R : G) (A B W s k : ℤ)
    (hA : (n : ℤ) ∣ A + k * B) (hW : (n : ℤ) ∣ W + s * B) (hB : ¬(n : ℤ) ∣ B)
    (hx : (h : ℤ) • (A • q - B • R - W • g) = 0) : (h : ℤ) • (s • g - k • q - R) = 0 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨w, hw⟩ := hW
  have e : (h : ℤ) • (A • q - B • R - W • g) =
      B • ((h : ℤ) • (s • g - k • q - R)) + a • (((h * n : ℕ) : ℤ) • q) -
        w • (((h * n : ℕ) : ℤ) • g) := by
    rw [show A = n * a - k * B by linarith, show W = n * w - s * B by linarith]
    push_cast
    simp only [smul_add, smul_sub, sub_smul, smul_smul]
    module
  rw [e, hn q, hn g, smul_zero, smul_zero, add_zero, sub_zero] at hx
  have hY : (n : ℤ) • ((h : ℤ) • (s • g - k • q - R)) = 0 := by
    rw [smul_smul, mul_comm, ← Nat.cast_mul, hn]
  obtain ⟨u, v, huv⟩ :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hB
  rw [← one_smul ℤ ((h : ℤ) • (s • g - k • q - R)), ← huv, add_smul, mul_smul, mul_smul, hY, hx,
    smul_zero, smul_zero, add_zero]

end Xark.FakeGlv
