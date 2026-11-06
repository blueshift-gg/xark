/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.EcAddK1Check
import Formal.Templates.EcDoubleAddK1Check
import Formal.Templates.OnCurveK1Check
import Formal.MulCertK1
import Formal.EcK1
import Formal.RequireLt8x32
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Set
import Mathlib.Data.List.GetD

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_bignum::ec_add_k1_check`, `ec_double_add_k1_check`, `on_curve_k1_check`

The secp256k1 point-op templates over 8 × 32-bit limbs, modelled as `Formal/EcR1Check.lean`
models the P-256 ones: `to_bits::<32>` range checks of the hinted coordinates, then
`mul_cert_k1` certificates whose operands are linear forms of the plugs (limb-wise,
differences biased by `2p`, `b2_k1`). Each certificate is `MulCertK1.rows` with its plugs
replaced by the operand forms and its variables shifted (`certRows`); `rows_eq`
checks by `decide +kernel` that the export is the model. Every operand limb stays in
`[0, 2³⁴)` (`lo_hi`), `MulCertK1.Assumptions`, given input limbs below `2³²` (`y_S`, `y_Q`
below `2³³`, so a caller may pass `2p − y` for `−y`).

* `EcAddK1Check.soundness` / `EcDoubleAddK1Check.soundness`: every hinted limb below `2³²`,
  the guard `x_P ≠ x_Q` (bug checklist 1), and the result is `P + Q` / `(A + S) + A` for
  affine inputs. `outs_lt`: the outputs are below `2³²` with no assumption.
* `OnCurveK1Check.soundness`: `(x, y)` is a nonsingular point of `y² = x³ + 7` in `ZMod p`.
  Canonicity (`x, y < p`) is `require_lt::<8, 32>`'s, called first by `on_curve_k1`
  (`x_lt_p` below).
-/

namespace Xark.Templates.EcK1Check

open Xark.Template Xark.R1cs
open Xark.Templates.EcK1Check (view rowSub sat_rowSub nsub eval_nsub
  OpD OpD.lc OpD.z OpD.lo OpD.hi opZ opZ_mem eval_var vw vw_plug getD_mem_take)
open Xark.Templates.MulCertR1 (num8)

/-! ### A certificate inside a larger template -/

def certRows (f : ℕ → LC) (o : ℕ) : List Row := MulCertK1.rows.map (rowSub (view f o))

abbrev Bd (d : ℕ → OpD) (σ : TVar → F) : Prop := ∀ m < 24, 0 ≤ (d m).z σ ∧ (d m).z σ < 2 ^ 34

theorem vw_assumptions (d : ℕ → OpD) (o : ℕ) (σ : TVar → F) (hb : Bd d σ) :
    MulCertK1.Assumptions (MulCertK1.template.ins (vw d o σ)) := by
  intro v hv
  rw [MulCertK1.ins_eq] at hv
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hv
  have hm := List.mem_range.mp hm
  have h1 := vw_plug d o σ m ⟨(hb m hm).1, lt_trans (hb m hm).2 (by norm_num)⟩
  have := (hb m hm).2
  omega

/-- A certificate's `Spec` is the congruence on its operands' integer values. -/
theorem spec_iff (d : ℕ → OpD) (o : ℕ) (σ : TVar → F) (hb : Bd d σ) :
    MulCertK1.Spec (MulCertK1.template.ins (vw d o σ)) ↔
      ((num8 fun j => (d j).z σ : ℤ) : EcK1.K) * ((num8 fun j => (d (8 + j)).z σ : ℤ) : EcK1.K) =
        ((num8 fun j => (d (16 + j)).z σ : ℤ) : EcK1.K) := by
  have e : ∀ k < 3, (num8 fun j => MulCertK1.lz (MulCertK1.template.ins (vw d o σ)) (8 * k + j)) =
      num8 fun j => (d (8 * k + j)).z σ := fun k hk =>
    MulCertR1.num8_congr _ _ fun j hj => by
      rw [MulCertK1.lz_ins _ _ (by omega), MulCertR1.vZ,
        vw_plug d o σ _ ⟨(hb _ (by omega)).1, lt_trans (hb _ (by omega)).2 (by norm_num)⟩]
  have e0 := e 0 (by norm_num); have e1 := e 1 (by norm_num); have e2 := e 2 (by norm_num)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at e0 e1 e2
  rw [MulCertK1.Spec, e0, e1, show (8 * 2 : ℕ) = 16 from rfl] at *
  rw [e2]

theorem cert_sound (d : ℕ → OpD) (o : ℕ) (σ : TVar → F)
    (h : Xark.R1cs.Sat (certRows (fun m => (d m).lc) o) σ) (hb : Bd d σ) :
    ((num8 fun j => (d j).z σ : ℤ) : EcK1.K) * ((num8 fun j => (d (8 + j)).z σ : ℤ) : EcK1.K) =
      ((num8 fun j => (d (16 + j)).z σ : ℤ) : EcK1.K) := by
  have hs : MulCertK1.template.Sat (vw d o σ) := by
    rw [Template.Sat, MulCertK1.rows_eq]; exact (sat_rowSub _ _ σ).mp h
  exact (spec_iff d o σ hb).mp (MulCertK1.soundness _ (vw_assumptions d o σ hb) hs)

/-! ### Range checks, operands as coordinate forms -/

/-- The `to_bits::<32>` checks of the `cnt` plugs from `base`: bits `1..31` of limb `b` at `31b..`. -/
def rangeRows (base cnt : ℕ) : List Row :=
  (List.range cnt).flatMap fun b => MulCertK1.bitRows (LC.var (.plug (base + b))) (31 * b) 31

/-- After `cnt` range-checked limbs, certificate `n`'s variables start at `31·cnt + 102n`. -/
def off (cnt n : ℕ) : ℕ := 31 * cnt + 102 * n

theorem sat_model (base cnt c : ℕ) (d : ℕ → ℕ → OpD) (σ : TVar → F) :
    Xark.R1cs.Sat (rangeRows base cnt ++ (List.range c).flatMap fun n =>
      certRows (fun m => (d n m).lc) (off cnt n)) σ ↔
    (∀ b < cnt, Xark.R1cs.Sat (MulCertK1.bitRows (LC.var (.plug (base + b))) (31 * b) 31) σ) ∧
      ∀ n < c, Xark.R1cs.Sat (certRows (fun m => (d n m).lc) (off cnt n)) σ := by
  simp only [Xark.R1cs.Sat, rangeRows, List.mem_append, List.mem_flatMap, List.mem_range]
  constructor
  · intro h
    exact ⟨fun b hb r hr => h r (Or.inl ⟨b, hb, hr⟩), fun n hn r hr => h r (Or.inr ⟨n, hn, hr⟩)⟩
  · rintro ⟨h1, h2⟩ r (⟨b, hb, hr⟩ | ⟨n, hn, hr⟩)
    exacts [h1 b hb r hr, h2 n hn r hr]

theorem range_sound (base cnt : ℕ) (σ : TVar → F)
    (h : ∀ b < cnt, Xark.R1cs.Sat (MulCertK1.bitRows (LC.var (.plug (base + b))) (31 * b) 31) σ) :
    ∀ i, base ≤ i → i < base + cnt → (σ (.plug i)).val < 2 ^ 32 := fun i hlo hi => by
  have := MulCertK1.bits_sound _ _ 31 (by norm_num) σ (h (i - base) (by omega))
  rwa [eval_var, show base + (i - base) = i by omega] at this

/-- An operand as a vector form: constant limbs plus `Σ c·(coordinate k)`, limb-wise. -/
abbrev VOp := (ℕ → ℤ) × List (ℤ × ℕ)
/-- Its limb `j`: coordinate `k`'s limb `j` is plug `8k + j`. -/
def VOp.at (v : VOp) (j : ℕ) : OpD := (v.1 j, v.2.map fun t => (t.1, 8 * t.2 + j))
/-- A certificate's 24 operand limbs from its three vector forms. -/
def opsOf (V : ℕ → VOp) (m : ℕ) : OpD := (V (m / 8)).at (m % 8)

/-- Coordinate `k` as an integer, and in `ZMod p`. -/
def Yz (σ : TVar → F) (k : ℕ) : ℤ := num8 fun j => ((σ (.plug (8 * k + j))).val : ℤ)
def Y (σ : TVar → F) (k : ℕ) : EcK1.K := (Yz σ k : EcK1.K)
/-- A vector form's value in `ZMod p`. -/
def ev (σ : TVar → F) (v : VOp) : EcK1.K :=
  ((num8 v.1 : ℤ) : EcK1.K) + (v.2.map fun t => (t.1 : EcK1.K) * Y σ t.2).sum

theorem num8_add (f g : ℕ → ℤ) : num8 (fun j => f j + g j) = num8 f + num8 g := by
  simp only [num8, mul_add, Finset.sum_add_distrib]

theorem num8_smul (c : ℤ) (f : ℕ → ℤ) : num8 (fun j => c * f j) = c * num8 f := by
  simp only [num8, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem num8_at (v : VOp) (σ : TVar → F) :
    num8 (fun j => (v.at j).z σ) = num8 v.1 + (v.2.map fun t => t.1 * Yz σ t.2).sum := by
  obtain ⟨c, ts⟩ := v
  simp only [VOp.at, OpD.z, opZ, List.map_map, Function.comp_def]
  induction ts generalizing c with
  | nil => simp
  | cons t ts ih =>
    have := ih fun j => c j + t.1 * ((σ (.plug (8 * t.2 + j))).val : ℤ)
    simp only [List.map_cons, List.sum_cons] at this ⊢
    rw [show (fun j => c j + (t.1 * ((σ (.plug (8 * t.2 + j))).val : ℤ) +
        (ts.map fun x => x.1 * ((σ (.plug (8 * x.2 + j))).val : ℤ)).sum)) =
      fun j => (c j + t.1 * ((σ (.plug (8 * t.2 + j))).val : ℤ)) +
        (ts.map fun x => x.1 * ((σ (.plug (8 * x.2 + j))).val : ℤ)).sum from
      funext fun j => by ring, this, num8_add, num8_smul]
    simp only [Yz]; ring

theorem num8_opsOf (V : ℕ → VOp) (σ : TVar → F) (a : ℕ) :
    (num8 fun j => (opsOf V (8 * a + j)).z σ) = num8 fun j => ((V a).at j).z σ :=
  MulCertR1.num8_congr _ _ fun j hj => by
    simp only [opsOf, show (8 * a + j) / 8 = a by omega, show (8 * a + j) % 8 = j by omega]

theorem cast_num8_at (V : ℕ → VOp) (σ : TVar → F) (a : ℕ) :
    ((num8 fun j => (opsOf V (8 * a + j)).z σ : ℤ) : EcK1.K) = ev σ (V a) := by
  rw [num8_opsOf, num8_at, ev]
  simp only [Int.cast_add, Int.cast_list_sum, List.map_map, Function.comp_def, Int.cast_mul, Y]

/-- A certificate on vector-form operands is `ev a · ev b = ev t` in `ZMod p`. -/
theorem certV_sound (V : ℕ → VOp) (o : ℕ) (σ : TVar → F)
    (h : Xark.R1cs.Sat (certRows (fun m => (opsOf V m).lc) o) σ) (hb : Bd (opsOf V) σ) :
    ev σ (V 0) * ev σ (V 1) = ev σ (V 2) := by
  have := cert_sound (opsOf V) o σ h hb
  rwa [show (fun j => (opsOf V j).z σ) = fun j => (opsOf V (8 * 0 + j)).z σ by simp,
    show (fun j => (opsOf V (8 + j)).z σ) = fun j => (opsOf V (8 * 1 + j)).z σ by simp,
    show (fun j => (opsOf V (16 + j)).z σ) = fun j => (opsOf V (8 * 2 + j)).z σ by simp,
    cast_num8_at, cast_num8_at, cast_num8_at] at this

/-- The plugs' bounds give every certificate operand its `2³⁴` bound. -/
theorem ops_bounds (V : ℕ → ℕ → VOp) (σ : TVar → F) (np c : ℕ) (bd : ℕ → ℤ)
    (hv : ∀ i < np, ((σ (.plug i)).val : ℤ) ≤ bd i)
    (hidx : ∀ n < c, ∀ m < 24, ∀ t ∈ (opsOf (V n) m).2, t.2 < np)
    (hlh : ∀ n < c, ∀ m < 24, 0 ≤ (opsOf (V n) m).lo bd ∧ (opsOf (V n) m).hi bd < 2 ^ 34) :
    ∀ n < c, Bd (opsOf (V n)) σ := fun n hn m hm => by
  have h := opZ_mem bd (opsOf (V n) m).1 (opsOf (V n) m).2 σ fun t ht => hv t.2 (hidx n hn m hm t ht)
  exact ⟨(hlh n hn m hm).1.trans h.1, h.2.trans_lt (hlh n hn m hm).2⟩

/-! ### Constants -/

/-- `2p` limb-wise (`b2_k1`), the unit, zero and `2p − 7` (`on_curve_k1_check`'s target). -/
def b2C (j : ℕ) : ℤ := [8589932638, 8589934588, 8589934590, 8589934590, 8589934590, 8589934590,
  8589934590, 8589934590].getD j 0
def unitC (j : ℕ) : ℤ := if j = 0 then 1 else 0
def zeroC (_ : ℕ) : ℤ := 0
def b7C (j : ℕ) : ℤ := [8589932631, 8589934588, 8589934590, 8589934590, 8589934590, 8589934590,
  8589934590, 8589934590].getD j 0

theorem p_zero : ((MulCertK1.pZ : ℤ) : EcK1.K) = 0 := by
  rw [← MulCertK1.pZ_eq]; push_cast; exact ZMod.natCast_self _

theorem ev_b2 : ((num8 b2C : ℤ) : EcK1.K) = 0 := by
  rw [show num8 b2C = 2 * MulCertK1.pZ by
    simp only [num8, Finset.sum_range_succ, Finset.sum_range_zero, b2C, MulCertK1.pZ]; norm_num]
  push_cast; rw [p_zero, mul_zero]
theorem ev_unit : ((num8 unitC : ℤ) : EcK1.K) = 1 := by
  simp [num8, unitC]
theorem ev_zero : ((num8 zeroC : ℤ) : EcK1.K) = 0 := by simp [num8, zeroC]
theorem ev_b7 : ((num8 b7C : ℤ) : EcK1.K) = -7 := by
  rw [show num8 b7C = 2 * MulCertK1.pZ - 7 by
    simp only [num8, Finset.sum_range_succ, Finset.sum_range_zero, b7C, MulCertK1.pZ]; norm_num]
  push_cast; rw [p_zero]; ring

/-- Plug bounds: limbs below `2³²` except the plugs `[lo, lo + 8)` (a `y` the caller may pass
as `2p − y`), below `2³³`. -/
def bdY (lo i : ℕ) : ℤ := if lo ≤ i ∧ i < lo + 8 then 2 ^ 33 - 1 else 2 ^ 32 - 1

end Xark.Templates.EcK1Check

namespace Xark.Templates.EcAddK1Check

open Xark.Template Xark.R1cs Xark.Templates.EcK1Check WeierstrassCurve.Affine
open Xark.Templates.EcK1Check (getD_mem_take OpD.lo OpD.hi)
open Xark.Templates.MulCertR1 (num8)
export Xark.Templates.Add32 (IsBit)

/-- Coordinates: `P = (0, 1)`, `Q = (2, 3)`, `w = 4`, `λ = 5`, `(x₃, y₃) = (6, 7)`; certificate
`n`'s operands `(a, b, t)`. -/
def V (n a : ℕ) : VOp :=
  match n, a with
  | 0, 0 => (zeroC, [(1, 4)]) | 0, 1 => (b2C, [(1, 2), (-1, 0)]) | 0, _ => (unitC, [])
  | 1, 0 => (zeroC, [(1, 5)]) | 1, 1 => (b2C, [(1, 2), (-1, 0)]) | 1, _ => (b2C, [(1, 3), (-1, 1)])
  | 2, 0 => (zeroC, [(1, 5)]) | 2, 1 => (zeroC, [(1, 5)]) | 2, _ => (zeroC, [(1, 6), (1, 0), (1, 2)])
  | _, 0 => (zeroC, [(1, 5)]) | _, 1 => (b2C, [(1, 0), (-1, 6)]) | _, _ => (zeroC, [(1, 7), (1, 1)])

def modelRows : List Row :=
  rangeRows 32 32 ++ (List.range 4).flatMap fun n => certRows (fun m => (opsOf (V n) m).lc) (off 32 n)

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 64).map fun j => LC.var (.plug j) := by
  decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem getD_ins (σ : TVar → F) (i : ℕ) (hi : i < 64) : (template.ins σ).getD i 0 = σ (.plug i) := by
  rw [Template.ins, inputs_eq, List.getD_eq_getElem _ _ (by simpa using hi)]; simp

theorem idx : ∀ n < 4, ∀ m < 24, ∀ t ∈ (opsOf (V n) m).2, t.2 < 64 := by decide +kernel
theorem lo_hi : ∀ n < 4, ∀ m < 24, 0 ≤ (opsOf (V n) m).lo (bdY 24) ∧ (opsOf (V n) m).hi (bdY 24) < 2 ^ 34 := by
  decide +kernel

/-- The input assumption: `P`'s and `x_Q`'s limbs (plugs `0..23`) below `2³²`, `y_Q`'s
(plugs `24..31`) below `2³³`. `ecdsa_verify_packed` enforces it on every call
(`formal/coverage-allowlist.txt`). -/
def Assumptions (ins : List F) : Prop :=
  (∀ v ∈ ins.take 24, v.val < 2 ^ 32) ∧ ∀ v ∈ ins.take 32, v.val < 2 ^ 33

/-- Coordinate `k` of the inputs in `ZMod p`. -/
def X (ins : List F) (k : ℕ) : EcK1.K := ((num8 fun j => ((ins.getD (8 * k + j) 0).val : ℤ) : ℤ) : EcK1.K)

/-- Every hinted limb is below `2³²`, `x_P ≠ x_Q`, and for affine `P`, `Q` the point
`(x₃, y₃)` is `P + Q`. -/
def Spec (ins : List F) : Prop :=
  (∀ i, 32 ≤ i → i < 64 → (ins.getD i 0).val < 2 ^ 32) ∧ X ins 0 ≠ X ins 2 ∧
    ∀ (hP : secp256k1Curve.Nonsingular (X ins 0) (X ins 1))
      (hQ : secp256k1Curve.Nonsingular (X ins 2) (X ins 3)),
      ∃ h : secp256k1Curve.Nonsingular (X ins 6) (X ins 7),
        Point.some _ _ hP + Point.some _ _ hQ = Point.some _ _ h

theorem X_eq (σ : TVar → F) (k : ℕ) (hk : k < 8) : X (template.ins σ) k = Y σ k := by
  simp only [X, Y, Yz]
  rw [MulCertR1.num8_congr _ _ fun j hj => by rw [getD_ins σ _ (by omega)]]

theorem plug_bd (σ : TVar → F) (h24 : ∀ i < 24, (σ (.plug i)).val < 2 ^ 32)
    (h32 : ∀ i < 32, (σ (.plug i)).val < 2 ^ 33)
    (hr : ∀ i, 32 ≤ i → i < 64 → (σ (.plug i)).val < 2 ^ 32) :
    ∀ i < 64, ((σ (.plug i)).val : ℤ) ≤ bdY 24 i := by
  intro i hi
  simp only [bdY]
  split_ifs with h
  · have := h32 i (by omega); omega
  · by_cases h' : i < 24
    · have := h24 i h'; omega
    · have := hr i (by omega) hi; omega

theorem certs (σ : TVar → F)
    (hc : ∀ n < 4, Xark.R1cs.Sat (certRows (fun m => (opsOf (V n) m).lc) (off 32 n)) σ)
    (hb : ∀ n < 4, Bd (opsOf (V n)) σ) :
    Y σ 4 * (Y σ 2 - Y σ 0) = 1 ∧ Y σ 5 * (Y σ 2 - Y σ 0) = Y σ 3 - Y σ 1 ∧
      Y σ 5 ^ 2 = Y σ 6 + Y σ 0 + Y σ 2 ∧ Y σ 5 * (Y σ 0 - Y σ 6) = Y σ 7 + Y σ 1 := by
  have c := fun n (hn : n < 4) => certV_sound (V n) (off 32 n) σ (hc n hn) (hb n hn)
  have c0 := c 0 (by norm_num); have c1 := c 1 (by norm_num)
  have c2 := c 2 (by norm_num); have c3 := c 3 (by norm_num)
  simp only [V, ev, ev_b2, ev_unit, ev_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at c0 c1 c2 c3
  push_cast at c0 c1 c2 c3
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination c0
  · linear_combination c1
  · linear_combination c2
  · linear_combination c3

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  rw [Template.Sat, rows_eq, modelRows, sat_model] at h
  obtain ⟨hr, hc⟩ := h
  have h24 : ∀ i < 24, (σ (.plug i)).val < 2 ^ 32 := fun i hi => by
    rw [← getD_ins σ i (by omega)]
    exact ha.1 _ (getD_mem_take hi (by rw [Template.ins, inputs_eq]; simp; omega))
  have h32 : ∀ i < 32, (σ (.plug i)).val < 2 ^ 33 := fun i hi => by
    rw [← getD_ins σ i (by omega)]
    exact ha.2 _ (getD_mem_take hi (by rw [Template.ins, inputs_eq]; simp; omega))
  have hrg := range_sound 32 32 σ hr
  have hb := ops_bounds V σ 64 4 (bdY 24) (plug_bd σ h24 h32 hrg) idx lo_hi
  obtain ⟨e0, e1, e2, e3⟩ := certs σ hc hb
  refine ⟨fun i hlo hi => by rw [getD_ins σ i hi]; exact hrg i hlo hi, ?_, ?_⟩
  · rw [X_eq σ 0 (by norm_num), X_eq σ 2 (by norm_num)]; exact EcK1.guard_ne e0
  · rw [X_eq σ 0 (by norm_num), X_eq σ 1 (by norm_num), X_eq σ 2 (by norm_num),
      X_eq σ 3 (by norm_num), X_eq σ 6 (by norm_num), X_eq σ 7 (by norm_num)]
    intro hP hQ
    exact EcK1.add_sound hP hQ e0 e1 e2 e3

/-- **Output bound.** `ec_add_k1` returns plugs `48..63` (`x₃`, `y₃`); the call's own range
rows bound them below `2³²` with no input assumption. -/
theorem outs_lt (σ : TVar → F) (h : template.Sat σ) :
    ∀ i, 48 ≤ i → i < 64 → ((template.ins σ).getD i 0).val < 2 ^ 32 := by
  intro i hlo hi
  rw [Template.Sat, rows_eq, modelRows, sat_model] at h
  rw [getD_ins σ i hi]
  exact range_sound 32 32 σ h.1 i (by omega) (by omega)

end Xark.Templates.EcAddK1Check

namespace Xark.Templates.EcDoubleAddK1Check

open Xark.Template Xark.R1cs Xark.Templates.EcK1Check WeierstrassCurve.Affine
open Xark.Templates.EcK1Check (getD_mem_take OpD.lo OpD.hi)
open Xark.Templates.MulCertR1 (num8)
export Xark.Templates.Add32 (IsBit)

/-- Coordinates: `A = (0, 1)`, `S = (2, 3)`, `w = 4`, `λ₁ = 5`, `x_R = 6`, `λ₂ = 7`,
`(x₃, y₃) = (8, 9)`; certificate `n`'s operands `(a, b, t)`. -/
def V (n a : ℕ) : VOp :=
  match n, a with
  | 0, 0 => (zeroC, [(1, 4)]) | 0, 1 => (b2C, [(1, 2), (-1, 0)]) | 0, _ => (unitC, [])
  | 1, 0 => (zeroC, [(1, 5)]) | 1, 1 => (b2C, [(1, 2), (-1, 0)]) | 1, _ => (b2C, [(1, 3), (-1, 1)])
  | 2, 0 => (zeroC, [(1, 5)]) | 2, 1 => (zeroC, [(1, 5)]) | 2, _ => (zeroC, [(1, 6), (1, 0), (1, 2)])
  | 3, 0 => (zeroC, [(1, 5), (1, 7)]) | 3, 1 => (b2C, [(1, 0), (-1, 6)]) | 3, _ => (zeroC, [(2, 1)])
  | 4, 0 => (zeroC, [(1, 7)]) | 4, 1 => (zeroC, [(1, 7)]) | 4, _ => (zeroC, [(1, 8), (1, 6), (1, 0)])
  | _, 0 => (zeroC, [(1, 7)]) | _, 1 => (b2C, [(1, 0), (-1, 8)]) | _, _ => (zeroC, [(1, 9), (1, 1)])

def modelRows : List Row :=
  rangeRows 32 48 ++ (List.range 6).flatMap fun n => certRows (fun m => (opsOf (V n) m).lc) (off 48 n)

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 80).map fun j => LC.var (.plug j) := by
  decide +kernel

theorem outputs_eq : template.outputs = [] := by decide +kernel

theorem getD_ins (σ : TVar → F) (i : ℕ) (hi : i < 80) : (template.ins σ).getD i 0 = σ (.plug i) := by
  rw [Template.ins, inputs_eq, List.getD_eq_getElem _ _ (by simpa using hi)]; simp

theorem idx : ∀ n < 6, ∀ m < 24, ∀ t ∈ (opsOf (V n) m).2, t.2 < 80 := by decide +kernel
theorem lo_hi : ∀ n < 6, ∀ m < 24, 0 ≤ (opsOf (V n) m).lo (bdY 24) ∧ (opsOf (V n) m).hi (bdY 24) < 2 ^ 34 := by
  decide +kernel

/-- The input assumption: `A`'s and `x_S`'s limbs (plugs `0..23`) below `2³²`, `y_S`'s
(plugs `24..31`) below `2³³`. `ecdsa_verify_packed` enforces it on every call
(`formal/coverage-allowlist.txt`). -/
def Assumptions (ins : List F) : Prop :=
  (∀ v ∈ ins.take 24, v.val < 2 ^ 32) ∧ ∀ v ∈ ins.take 32, v.val < 2 ^ 33

def X (ins : List F) (k : ℕ) : EcK1.K := ((num8 fun j => ((ins.getD (8 * k + j) 0).val : ℤ) : ℤ) : EcK1.K)

/-- Every hinted limb is below `2³²`, `x_A ≠ x_S`, and for affine `A`, `S` the point
`(x₃, y₃)` is `(A + S) + A`. -/
def Spec (ins : List F) : Prop :=
  (∀ i, 32 ≤ i → i < 80 → (ins.getD i 0).val < 2 ^ 32) ∧ X ins 0 ≠ X ins 2 ∧
    ∀ (hA : secp256k1Curve.Nonsingular (X ins 0) (X ins 1))
      (hS : secp256k1Curve.Nonsingular (X ins 2) (X ins 3)),
      ∃ h : secp256k1Curve.Nonsingular (X ins 8) (X ins 9),
        Point.some _ _ h = Point.some _ _ hA + Point.some _ _ hS + Point.some _ _ hA

theorem X_eq (σ : TVar → F) (k : ℕ) (hk : k < 10) : X (template.ins σ) k = Y σ k := by
  simp only [X, Y, Yz]
  rw [MulCertR1.num8_congr _ _ fun j hj => by rw [getD_ins σ _ (by omega)]]

theorem plug_bd (σ : TVar → F) (h24 : ∀ i < 24, (σ (.plug i)).val < 2 ^ 32)
    (h32 : ∀ i < 32, (σ (.plug i)).val < 2 ^ 33)
    (hr : ∀ i, 32 ≤ i → i < 80 → (σ (.plug i)).val < 2 ^ 32) :
    ∀ i < 80, ((σ (.plug i)).val : ℤ) ≤ bdY 24 i := by
  intro i hi
  simp only [bdY]
  split_ifs with h
  · have := h32 i (by omega); omega
  · by_cases h' : i < 24
    · have := h24 i h'; omega
    · have := hr i (by omega) hi; omega

theorem certs (σ : TVar → F)
    (hc : ∀ n < 6, Xark.R1cs.Sat (certRows (fun m => (opsOf (V n) m).lc) (off 48 n)) σ)
    (hb : ∀ n < 6, Bd (opsOf (V n)) σ) :
    Y σ 4 * (Y σ 2 - Y σ 0) = 1 ∧ Y σ 5 * (Y σ 2 - Y σ 0) = Y σ 3 - Y σ 1 ∧
      Y σ 5 ^ 2 = Y σ 6 + Y σ 0 + Y σ 2 ∧ (Y σ 5 + Y σ 7) * (Y σ 0 - Y σ 6) = 2 * Y σ 1 ∧
      Y σ 7 ^ 2 = Y σ 8 + Y σ 6 + Y σ 0 ∧ Y σ 7 * (Y σ 0 - Y σ 8) = Y σ 9 + Y σ 1 := by
  have c := fun n (hn : n < 6) => certV_sound (V n) (off 48 n) σ (hc n hn) (hb n hn)
  have c0 := c 0 (by norm_num); have c1 := c 1 (by norm_num); have c2 := c 2 (by norm_num)
  have c3 := c 3 (by norm_num); have c4 := c 4 (by norm_num); have c5 := c 5 (by norm_num)
  simp only [V, ev, ev_b2, ev_unit, ev_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at c0 c1 c2 c3 c4 c5
  push_cast at c0 c1 c2 c3 c4 c5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination c0
  · linear_combination c1
  · linear_combination c2
  · linear_combination c3
  · linear_combination c4
  · linear_combination c5

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  rw [Template.Sat, rows_eq, modelRows, sat_model] at h
  obtain ⟨hr, hc⟩ := h
  have h24 : ∀ i < 24, (σ (.plug i)).val < 2 ^ 32 := fun i hi => by
    rw [← getD_ins σ i (by omega)]
    exact ha.1 _ (getD_mem_take hi (by rw [Template.ins, inputs_eq]; simp; omega))
  have h32 : ∀ i < 32, (σ (.plug i)).val < 2 ^ 33 := fun i hi => by
    rw [← getD_ins σ i (by omega)]
    exact ha.2 _ (getD_mem_take hi (by rw [Template.ins, inputs_eq]; simp; omega))
  have hrg := range_sound 32 48 σ hr
  have hb := ops_bounds V σ 80 6 (bdY 24) (plug_bd σ h24 h32 hrg) idx lo_hi
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := certs σ hc hb
  refine ⟨fun i hlo hi => by rw [getD_ins σ i hi]; exact hrg i hlo hi, ?_, ?_⟩
  · rw [X_eq σ 0 (by norm_num), X_eq σ 2 (by norm_num)]; exact EcK1.guard_ne e0
  · simp only [X_eq σ _ (by norm_num : 0 < 10), X_eq σ _ (by norm_num : 1 < 10),
      X_eq σ _ (by norm_num : 2 < 10), X_eq σ _ (by norm_num : 3 < 10),
      X_eq σ _ (by norm_num : 8 < 10), X_eq σ _ (by norm_num : 9 < 10)]
    intro hA hS
    exact DoubleAdd.dblAdd_sound EcK1.short hA hS (w := -Y σ 4) (l1 := Y σ 5) (l2 := Y σ 7)
      (xR := Y σ 6) (by linear_combination e0) (by linear_combination -Y σ 4 * e1 + Y σ 5 * e0)
      (by linear_combination -e2) e3 (by linear_combination -e4) (by linear_combination e5)

/-- **Output bound.** `ec_double_add_k1` returns plugs `64..79` (`x₃`, `y₃`), below `2³²` by
the call's own range rows. -/
theorem outs_lt (σ : TVar → F) (h : template.Sat σ) :
    ∀ i, 64 ≤ i → i < 80 → ((template.ins σ).getD i 0).val < 2 ^ 32 := by
  intro i hlo hi
  rw [Template.Sat, rows_eq, modelRows, sat_model] at h
  rw [getD_ins σ i hi]
  exact range_sound 32 48 σ h.1 i (by omega) (by omega)

end Xark.Templates.EcDoubleAddK1Check

namespace Xark.Templates.OnCurveK1Check

open Xark.Template Xark.R1cs Xark.Templates.EcK1Check WeierstrassCurve.Affine
open Xark.Templates.EcK1Check (getD_mem_take OpD.lo OpD.hi)
open Xark.Templates.MulCertR1 (num8)
export Xark.Templates.Add32 (IsBit)

/-- Coordinates `x = 0`, `y = 1`, `s = 2`, `z = 3`; certificate `n`'s operands. -/
def V (n a : ℕ) : VOp :=
  match n, a with
  | 0, 0 => (zeroC, [(1, 0)]) | 0, 1 => (zeroC, [(1, 0)]) | 0, _ => (zeroC, [(1, 2)])
  | 1, 0 => (zeroC, [(1, 1)]) | 1, 1 => (zeroC, [(1, 1)]) | 1, _ => (zeroC, [(1, 3)])
  | _, 0 => (zeroC, [(1, 2)]) | _, 1 => (zeroC, [(1, 0)]) | _, _ => (b7C, [(1, 3)])

def modelRows : List Row :=
  rangeRows 16 16 ++ (List.range 3).flatMap fun n => certRows (fun m => (opsOf (V n) m).lc) (off 16 n)

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 32).map fun j => LC.var (.plug j) := by
  decide +kernel

theorem getD_ins (σ : TVar → F) (i : ℕ) (hi : i < 32) : (template.ins σ).getD i 0 = σ (.plug i) := by
  rw [Template.ins, inputs_eq, List.getD_eq_getElem _ _ (by simpa using hi)]; simp

def b32 (_ : ℕ) : ℤ := 2 ^ 32 - 1
theorem idx : ∀ n < 3, ∀ m < 24, ∀ t ∈ (opsOf (V n) m).2, t.2 < 32 := by decide +kernel
theorem lo_hi : ∀ n < 3, ∀ m < 24, 0 ≤ (opsOf (V n) m).lo b32 ∧ (opsOf (V n) m).hi b32 < 2 ^ 34 := by
  decide +kernel

/-- The input assumption: `x`'s and `y`'s limbs (plugs `0..15`) below `2³²`. `on_curve_k1`'s
callers enforce it: `unpack8`'s and `ecdsa_verify_packed`'s `range_check_limbs::<8, 32>` (`formal/coverage-allowlist.txt`). -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins.take 16, v.val < 2 ^ 32

def X (ins : List F) (k : ℕ) : EcK1.K := ((num8 fun j => ((ins.getD (8 * k + j) 0).val : ℤ) : ℤ) : EcK1.K)

/-- `s`, `z` limbs below `2³²`, and `(x, y)` a nonsingular point of secp256k1. -/
def Spec (ins : List F) : Prop :=
  (∀ i < 32, (ins.getD i 0).val < 2 ^ 32) ∧ secp256k1Curve.Nonsingular (X ins 0) (X ins 1)

theorem X_eq (σ : TVar → F) (k : ℕ) (hk : k < 4) : X (template.ins σ) k = Y σ k := by
  simp only [X, Y, Yz]
  rw [MulCertR1.num8_congr _ _ fun j hj => by rw [getD_ins σ _ (by omega)]]

/-- A solution of `y² = x³ + 7` is nonsingular: secp256k1 has no point with `y = 0`. -/
theorem nonsingular_of_eq {x y : EcK1.K} (h : y ^ 2 = x ^ 3 + 7) :
    secp256k1Curve.Nonsingular x y := by
  have heq : secp256k1Curve.Equation x y := by
    rw [equation_iff']
    simp only [secp256k1Curve_a₁, secp256k1Curve_a₂, secp256k1Curve_a₃, secp256k1Curve_a₄,
      secp256k1Curve_a₆]
    linear_combination h
  refine ⟨heq, Or.inr ?_⟩
  simp only [evalEval_polynomialY, secp256k1Curve_a₁, secp256k1Curve_a₃]
  intro h0
  have hy : y = 0 := by
    have : (2 : EcK1.K) * y = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left EcK1.two_ne_zero
  exact EcK1.noTwoTorsion x (hy ▸ heq)

theorem certs (σ : TVar → F)
    (hc : ∀ n < 3, Xark.R1cs.Sat (certRows (fun m => (opsOf (V n) m).lc) (off 16 n)) σ)
    (hb : ∀ n < 3, Bd (opsOf (V n)) σ) :
    Y σ 0 * Y σ 0 = Y σ 2 ∧ Y σ 1 * Y σ 1 = Y σ 3 ∧
      Y σ 2 * Y σ 0 = Y σ 3 - 7 := by
  have c := fun n (hn : n < 3) => certV_sound (V n) (off 16 n) σ (hc n hn) (hb n hn)
  have c0 := c 0 (by norm_num); have c1 := c 1 (by norm_num); have c2 := c 2 (by norm_num)
  simp only [V, ev, ev_b7, ev_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at c0 c1 c2
  push_cast at c0 c1 c2
  exact ⟨by linear_combination c0, by linear_combination c1, by linear_combination c2⟩

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  rw [Template.Sat, rows_eq, modelRows, sat_model] at h
  obtain ⟨hr, hc⟩ := h
  have hrg := range_sound 16 16 σ hr
  have hv : ∀ i < 32, (σ (.plug i)).val < 2 ^ 32 := by
    intro i hi
    by_cases h16 : i < 16
    · rw [← getD_ins σ i hi]
      exact ha _ (getD_mem_take h16 (by rw [Template.ins, inputs_eq]; simpa using hi))
    · exact hrg i (by omega) hi
  have hb := ops_bounds V σ 32 3 b32 (fun i hi => by have := hv i hi; simp only [b32]; omega) idx lo_hi
  obtain ⟨e0, e1, e2⟩ := certs σ hc hb
  refine ⟨fun i hi => by rw [getD_ins σ i hi]; exact hv i hi, ?_⟩
  rw [X_eq σ 0 (by norm_num), X_eq σ 1 (by norm_num)]
  exact nonsingular_of_eq (by linear_combination e1 - e2 - Y σ 0 * e0)

end Xark.Templates.OnCurveK1Check

namespace Xark.Templates.OnCurveK1Check

open Xark.Template

/-- secp256k1's `p − 1` as `require_lt::<8, 32>`'s constant plugs `8..15` (`M1_K1`). -/
def m1K1 : List (ℕ × F) := [(8, 4294966318), (9, 4294967294), (10, 4294967295), (11, 4294967295),
  (12, 4294967295), (13, 4294967295), (14, 4294967295), (15, 4294967295)]

/-- **The hinted point's `x` is canonical**, so `x_R + p` never stands in for `x_R`.
`on_curve_k1` runs `require_lt::<8, 32>(x, M1_K1)` (these rows) on `x`'s limbs, each below
`2³²` by the caller's `range_check_limbs::<8, 32>` (`ecdsa_verify_packed`'s rows on the hinted
`R`, `unpack8`'s on `Q`); every satisfying assignment then has `x < p`. `fake_glv_check_k1`
reads `x_R` from the same limbs, so its `x_R = r + t·n` (`t ∈ {0, 1}`) is over `x_R < p`. -/
theorem x_lt_p (σ : TVar → F) (hx : ∀ j < 8, (σ (.plug j)).val < 2 ^ 32)
    (h : (RequireLt8x32.template.inst (Template.consts m1K1)).Sat σ) :
    RequireLt.limbs (fun j => (σ (.plug j)).val) 32 8 < Xark.secp256k1_p := by
  rw [Template.sat_inst] at h
  set τ := Template.env (Template.consts m1K1) σ with hτ
  have hlo : ∀ j < 8, τ (.plug j) = σ (.plug j) := by
    intro j hj
    interval_cases j <;> simp [hτ, m1K1, Template.consts, Template.env]
  have hins : ∀ j < 8, (RequireLt8x32.template.ins τ).getD j 0 = σ (.plug j) := fun j hj => by
    rw [RequireLt.ins_x RequireLt8x32.is_model τ hj, hlo j hj]
  have ha : RequireLt.Assumptions 8 32 (RequireLt8x32.template.ins τ) := by
    intro j hj; rw [hins j hj]; exact hx j hj
  have key := (RequireLt.spec_iff RequireLt8x32.is_model τ).mp
    (RequireLt.soundness RequireLt8x32.is_model (by norm_num) (by norm_num) (by norm_num) τ ha h)
  have e : RequireLt.limbs (fun j => (τ (.plug j)).val) 32 8 =
      RequireLt.limbs (fun j => (σ (.plug j)).val) 32 8 :=
    Finset.sum_congr rfl fun j hj => by simp only; rw [hlo j (Finset.mem_range.mp hj)]
  rw [e] at key
  have hhi : ∀ j < 8, (τ (.plug (8 + j))).val = ([4294966318, 4294967294, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295,
        4294967295] : List ℕ).getD j 0 := by
    intro j hj
    interval_cases j <;> simp [hτ, m1K1, Template.consts, Template.env, Xark.Templates.val_ofNat]
  have hm : RequireLt.limbs (fun j => ((RequireLt.plugM 8 j).eval τ).val) 32 8 =
      Xark.secp256k1_p - 1 := by
    have hc : RequireLt.limbs (fun j => ((RequireLt.plugM 8 j).eval τ).val) 32 8 =
        RequireLt.limbs (fun j => ([4294966318, 4294967294, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295,
        4294967295] : List ℕ).getD j 0) 32 8 :=
      Finset.sum_congr rfl fun j hj => by
        simp only
        rw [show (RequireLt.plugM 8 j).eval τ = τ (.plug (8 + j)) by
          simp [RequireLt.plugM, Xark.R1cs.LC.eval], hhi j (Finset.mem_range.mp hj)]
    rw [hc]; simp [RequireLt.limbs, Finset.sum_range_succ, Xark.secp256k1_p]
  have hp : 0 < Xark.secp256k1_p := by norm_num [Xark.secp256k1_p]
  omega

end Xark.Templates.OnCurveK1Check
