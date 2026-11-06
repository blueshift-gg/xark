/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.MulCert25519
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Calls of `mul_cert_25519` inside a template

A call's operands are linear forms of the caller's plugs (`OpD`). The frontend folds a
product whose operand is a constant (a zero operand, or a constant such as `d⁻¹`) into
a linear form, so a call emits rows only for its *real* products (both operands
non-constant), numbered in order, then the quotient, the bits and the closing row.
`callRows` models exactly that: `mul_cert_25519`'s rows with each variable
replaced by its value in the caller (`view`), the dropped products by their linear forms.
-/

namespace Xark.Templates.EdCheck

open Xark.Template Xark.R1cs
open Xark.Templates.EcK1Check (sub norm nsub rowSub eval_nsub sat_rowSub
  op opZ eval_op OpD OpD.lc OpD.z OpD.lo OpD.hi opZ_mem eval_var getD_mem_take)

namespace MC
export Xark.Templates.MulCert25519 (aLC bLC kLC tLC eLC rows)
end MC

/-- An operand's limbs as plug substitutions (`mul_cert_25519`'s operands read plugs only). -/
def pview (f : ℕ → LC) : TVar → LC
  | .plug m => f m
  | .wit _ => ⟨0, []⟩

def opA (f : ℕ → LC) (i j : ℕ) : LC := nsub (pview f) (MC.aLC i j)
def opB (f : ℕ → LC) (i j : ℕ) : LC := nsub (pview f) (MC.bLC i j)

/-- Product `(j, i)` gets a row and a variable iff both operands are non-constant. -/
def real (f : ℕ → LC) (p : ℕ × ℕ) : Bool :=
  !(opA f p.2 p.1).terms.isEmpty && !(opB f p.2 p.1).terms.isEmpty

/-- The products in the gadget's order. -/
def pairs : List (ℕ × ℕ) := (List.range 15).flatMap fun j => (List.range 3).map fun i => (j, i)

/-- The real products, in order. -/
def reals (f : ℕ → LC) : List (ℕ × ℕ) := pairs.filter (real f)

/-- Product `(j, i)`'s rank among the real ones. -/
def rank (f : ℕ → LC) (j i : ℕ) : ℕ := ((pairs.take (3 * j + i)).filter (real f)).length

def nReal (f : ℕ → LC) : ℕ := (reals f).length

/-- A folded product: one operand is a constant. -/
def cprod (A B : LC) : LC :=
  if A.terms.isEmpty then ⟨A.const * B.const, B.terms.map fun t => (A.const * t.1, t.2)⟩
  else ⟨A.const * B.const, A.terms.map fun t => (B.const * t.1, t.2)⟩

/-- `mul_cert_25519`'s variables seen from a call with operands `f` and first variable `o`. -/
def view (f : ℕ → LC) (o : ℕ) : TVar → LC
  | .plug m => f m
  | .wit w =>
    if w < 45 then
      if real f (w / 3, w % 3) then LC.var (.wit (o + rank f (w / 3) (w % 3)))
      else cprod (opA f (w % 3) (w / 3)) (opB f (w % 3) (w / 3))
    else LC.var (.wit (o + nReal f + (w - 45)))

/-- The rows after the products: bits of `K + 2⁵¹`, of `T + 2⁵⁰`, the closing row. -/
def tailRows : List Row :=
  Xark.Templates.MulCertK1.bitRows MC.kLC 47 51 ++ Xark.Templates.MulCertK1.bitRows MC.tLC 98 50 ++
    [⟨MC.eLC, ⟨1, []⟩, ⟨0, []⟩⟩]

def callRows (f : ℕ → LC) (o : ℕ) : List Row :=
  (reals f).map (fun p => ⟨opA f p.2 p.1, opB f p.2 p.1, LC.var (.wit (o + rank f p.1 p.2))⟩) ++
    tailRows.map (rowSub (view f o))

/-- The variables a call takes. -/
def callWits (f : ℕ → LC) : ℕ := nReal f + 103

/-- The range checks of the `cnt` plugs from `base`: bits `1..31` of limb `b` at `31b..`. -/
def rangeRows (base cnt : ℕ) : List Row :=
  (List.range cnt).flatMap fun b =>
    Xark.Templates.MulCertK1.bitRows (LC.var (.plug (base + b))) (31 * b) 31

/-- Calls `n < c` with operands `d n`, after `cnt` range-checked limbs. -/
def offs (d : ℕ → ℕ → OpD) (cnt : ℕ) : ℕ → ℕ
  | 0 => 31 * cnt
  | n + 1 => offs d cnt n + callWits fun m => (d n m).lc

def modelRows (base cnt c : ℕ) (d : ℕ → ℕ → OpD) : List Row :=
  rangeRows base cnt ++ (List.range c).flatMap fun n => callRows (fun m => (d n m).lc) (offs d cnt n)

/-! ### Operands -/

/-- `p = 2²⁵⁵ − 19` limb-wise (8 × 32). -/
def pl (j : ℕ) : ℤ := if j = 0 then 2 ^ 32 - 19 else if j = 7 then 2 ^ 31 - 1 else 2 ^ 32 - 1

/-- Limb `j` of `c + Σ kᵢ·vᵢ` for coordinate vectors `vᵢ` (plugs `8vᵢ..8vᵢ + 7`). -/
def vec (c : ℕ → ℤ) (ts : List (ℤ × ℕ)) (j : ℕ) : OpD := (c j, ts.map fun t => (t.1, 8 * t.2 + j))
/-- A coordinate limb `plug (8k + j)`. -/
def co (k j : ℕ) : OpD := (0, [(1, 8 * k + j)])
/-- `4p + c` limb-wise (`c` a small constant in limb 0). -/
def b4 (c : ℤ) (j : ℕ) : ℤ := 4 * pl j + if j = 0 then c else 0
/-- The small constant `c` (limb 0). -/
def sm (c : ℤ) (j : ℕ) : ℤ := if j = 0 then c else 0
/-- The zero operand. -/
def zo : OpD := (0, [])
/-- A constant's limb. -/
def cst (v : ℕ) (j : ℕ) : OpD := (((v / 2 ^ (32 * j)) % 2 ^ 32 : ℕ), [])

/-- `d⁻¹ mod p`. -/
def dInv : ℕ := 29203323570479832313932222820853031755424015489030106335172286495629888845891



/-! ### A call's rows hold iff the certificate's do, at the call's view -/

open Xark.Templates.MulCert25519 (ev pv eval_aLC eval_bLC)

/-- The certificate's variables' values seen from the caller's assignment. -/
def vs (f : ℕ → LC) (o : ℕ) (σ : TVar → F) : TVar → F := fun v => (view f o v).eval σ

theorem eval_opA (f : ℕ → LC) (o i j : ℕ) (σ : TVar → F) :
    (opA f i j).eval σ = (MC.aLC i j).eval (vs f o σ) := by
  rw [opA, eval_nsub, eval_aLC, eval_aLC]; rfl

theorem eval_opB (f : ℕ → LC) (o i j : ℕ) (σ : TVar → F) :
    (opB f i j).eval σ = (MC.bLC i j).eval (vs f o σ) := by
  rw [opB, eval_nsub, eval_bLC, eval_bLC]; rfl

theorem eval_cprod (A B : LC) (h : A.terms = [] ∨ B.terms = []) (σ : TVar → F) :
    (cprod A B).eval σ = A.eval σ * B.eval σ := by
  obtain ⟨a, ta⟩ := A
  obtain ⟨b, tb⟩ := B
  simp only at h
  unfold cprod
  split_ifs with hA
  · simp only [List.isEmpty_iff] at hA
    subst hA
    simp only [LC.eval, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left,
      List.map_nil, List.sum_nil, add_zero]
    ring
  · have hB : tb = [] := h.resolve_left (by simpa using hA)
    subst hB
    simp only [LC.eval, List.map_map, Function.comp_def, List.map_nil, List.sum_nil, add_zero]
    rw [show (fun x : F × TVar => b * x.1 * σ x.2) = fun x => b * (x.1 * σ x.2) by
      funext x; ring, List.sum_map_mul_left]
    ring

theorem mem_pairs (j i : ℕ) : (j, i) ∈ pairs ↔ j < 15 ∧ i < 3 := by
  simp [pairs]

theorem sat_callRows (f : ℕ → LC) (o : ℕ) (σ : TVar → F) : Xark.R1cs.Sat (callRows f o) σ ↔
    (∀ p ∈ reals f, (opA f p.2 p.1).eval σ * (opB f p.2 p.1).eval σ =
      σ (.wit (o + rank f p.1 p.2))) ∧ Xark.R1cs.Sat tailRows (vs f o σ) := by
  rw [callRows, show vs f o σ = fun v => (view f o v).eval σ from rfl, ← sat_rowSub]
  simp only [Xark.R1cs.Sat, List.mem_append, List.mem_map]
  constructor
  · intro h
    exact ⟨fun p hp => by simpa [Row.Sat, LC.eval, LC.var] using h _ (Or.inl ⟨p, hp, rfl⟩),
      fun r hr => h r (Or.inr hr)⟩
  · rintro ⟨h1, h2⟩ r (⟨p, hp, rfl⟩ | hr)
    · simpa [Row.Sat, LC.eval, LC.var] using h1 p hp
    · exact h2 r hr

theorem sat_tailRows (σ : TVar → F) : Xark.R1cs.Sat tailRows σ ↔
    Xark.R1cs.Sat (Xark.Templates.MulCertK1.bitRows MC.kLC 47 51) σ ∧
      Xark.R1cs.Sat (Xark.Templates.MulCertK1.bitRows MC.tLC 98 50) σ ∧ MC.eLC.eval σ = 0 := by
  simp only [Xark.R1cs.Sat, tailRows, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun r hr => h r (Or.inl (Or.inl hr)), fun r hr => h r (Or.inl (Or.inr hr)),
      by simpa [Row.Sat, LC.eval] using h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2, h3⟩ r ((hr | hr) | rfl)
    exacts [h1 r hr, h2 r hr, by simpa [Row.Sat, LC.eval] using h3]

/-- The certificate's product rows hold at the view when the call's real ones do. -/
theorem prods_of (f : ℕ → LC) (o : ℕ) (σ : TVar → F)
    (h : ∀ p ∈ reals f, (opA f p.2 p.1).eval σ * (opB f p.2 p.1).eval σ =
      σ (.wit (o + rank f p.1 p.2))) :
    ∀ j < 15, ∀ i < 3, (MC.aLC i j).eval (vs f o σ) * (MC.bLC i j).eval (vs f o σ) =
      vs f o σ (.wit (3 * j + i)) := by
  intro j hj i hi
  rw [← eval_opA f o, ← eval_opB f o]
  have h45 : 3 * j + i < 45 := by omega
  have hd : (3 * j + i) / 3 = j := by omega
  have hm : (3 * j + i) % 3 = i := by omega
  simp only [vs, view, if_pos h45, hd, hm]
  split_ifs with hr
  · rw [eval_var]
    exact h (j, i) (List.mem_filter.mpr ⟨(mem_pairs j i).mpr ⟨hj, hi⟩, hr⟩)
  · rw [eval_cprod]
    simp only [real, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      not_and_or] at hr
    rcases hr with hr | hr
    · left; simpa using hr
    · right; simpa using hr

/-- **A call is sound**: its rows hold only if the certificate's rows hold at its view. -/
theorem call_sound (f : ℕ → LC) (o : ℕ) (σ : TVar → F) (h : Xark.R1cs.Sat (callRows f o) σ) :
    Xark.Templates.MulCert25519.template.Sat (vs f o σ) := by
  rw [sat_callRows] at h
  rw [Template.Sat, Xark.Templates.MulCert25519.rows_eq, Xark.Templates.MulCert25519.sat_rows]
  exact ⟨prods_of f o σ h.1, (sat_tailRows _).mp h.2⟩


/-! ### Operands, the model, the range checks -/

/-- `OpD` operands as linear forms. -/
abbrev fd (d : ℕ → OpD) : ℕ → LC := fun m => (d m).lc

theorem vs_plug (d : ℕ → OpD) (o : ℕ) (σ : TVar → F) (m : ℕ) :
    vs (fd d) o σ (.plug m) = (((d m).z σ : ℤ) : F) := by
  simp only [vs, view, OpD.lc, OpD.z, eval_op]

theorem val_z (d : ℕ → OpD) (o : ℕ) (σ : TVar → F) (m : ℕ)
    (hb : 0 ≤ (d m).z σ ∧ (d m).z σ < 2 ^ 36) :
    (((vs (fd d) o σ (.plug m)).val : ℕ) : ℤ) = (d m).z σ := by
  rw [vs_plug]; exact Xark.Templates.MulCertK1.val_intCast hb.1 (lt_trans hb.2 (by norm_num))

theorem assumptions_of (d : ℕ → OpD) (o : ℕ) (σ : TVar → F)
    (hb : ∀ m < 56, 0 ≤ (d m).z σ ∧ (d m).z σ < 2 ^ 36) :
    Xark.Templates.MulCert25519.Assumptions
      (Xark.Templates.MulCert25519.template.ins (vs (fd d) o σ)) := by
  intro v hv
  rw [Xark.Templates.MulCert25519.ins_eq] at hv
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hv
  have hm := List.mem_range.mp hm
  have := val_z d o σ m (hb m hm)
  have := (hb m hm).2
  omega

open Xark.Ed25519 (Fp)

/-- Operand `o` (`a₁ = 0`, …, `t = 48`) of a call as a number in `ZMod p`. -/
def N (d : ℕ → OpD) (o : ℕ) (σ : TVar → F) : Fp :=
  Xark.Templates.MulCert25519.num fun l => (((d (o + l)).z σ : ℤ) : Fp)

/-- A call's certificate is the congruence on its operands' integer values. -/
theorem spec_iff (d : ℕ → OpD) (o : ℕ) (σ : TVar → F)
    (hb : ∀ m < 56, 0 ≤ (d m).z σ ∧ (d m).z σ < 2 ^ 36) :
    Xark.Templates.MulCert25519.Spec (Xark.Templates.MulCert25519.template.ins (vs (fd d) o σ)) ↔
      N d 0 σ * N d 8 σ - N d 16 σ * N d 24 σ - N d 32 σ * N d 40 σ = N d 48 σ := by
  have hX : ∀ k ≤ 48, Xark.Templates.MulCert25519.X
      (Xark.Templates.MulCert25519.template.ins (vs (fd d) o σ)) k = N d k σ := by
    intro k hk
    simp only [Xark.Templates.MulCert25519.X, N, Xark.Templates.MulCert25519.num]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [Finset.mem_range] at hl
    rw [Xark.Templates.MulCert25519.limb, Xark.Templates.MulCert25519.getD_ins _ _ (by omega),
      ← Int.cast_natCast, val_z d o σ _ (hb _ (by omega))]
  rw [Xark.Templates.MulCert25519.Spec, hX 0 (by norm_num), hX 8 (by norm_num),
    hX 16 (by norm_num), hX 24 (by norm_num), hX 32 (by norm_num), hX 40 (by norm_num),
    hX 48 (by norm_num)]

theorem cert_sound (d : ℕ → OpD) (o : ℕ) (σ : TVar → F)
    (h : Xark.R1cs.Sat (callRows (fd d) o) σ) (hb : ∀ m < 56, 0 ≤ (d m).z σ ∧ (d m).z σ < 2 ^ 36) :
    N d 0 σ * N d 8 σ - N d 16 σ * N d 24 σ - N d 32 σ * N d 40 σ = N d 48 σ :=
  (spec_iff d o σ hb).mp (Xark.Templates.MulCert25519.soundness _ (assumptions_of d o σ hb)
    (call_sound _ o σ h))

theorem sat_model (base cnt c : ℕ) (d : ℕ → ℕ → OpD) (σ : TVar → F) :
    Xark.R1cs.Sat (modelRows base cnt c d) σ ↔
    (∀ b < cnt, Xark.R1cs.Sat
      (Xark.Templates.MulCertK1.bitRows (LC.var (.plug (base + b))) (31 * b) 31) σ) ∧
      ∀ n < c, Xark.R1cs.Sat (callRows (fd (d n)) (offs d cnt n)) σ := by
  simp only [Xark.R1cs.Sat, modelRows, rangeRows, List.mem_append, List.mem_flatMap,
    List.mem_range]
  constructor
  · intro h
    exact ⟨fun b hb r hr => h r (Or.inl ⟨b, hb, hr⟩), fun n hn r hr => h r (Or.inr ⟨n, hn, hr⟩)⟩
  · rintro ⟨h1, h2⟩ r (⟨b, hb, hr⟩ | ⟨n, hn, hr⟩)
    exacts [h1 b hb r hr, h2 n hn r hr]

theorem range_sound (base b : ℕ) (σ : TVar → F)
    (h : Xark.R1cs.Sat
      (Xark.Templates.MulCertK1.bitRows (LC.var (.plug (base + b))) (31 * b) 31) σ) :
    (σ (.plug (base + b))).val < 2 ^ 32 := by
  have := Xark.Templates.MulCertK1.bits_sound _ _ 31 (by norm_num) σ h
  rwa [eval_var] at this

/-! ### Operand values -/

/-- Coordinate vector `k` (plugs `8k..8k + 7`) as a number in `ZMod p`. -/
def Y (σ : TVar → F) (k : ℕ) : Fp :=
  Xark.Templates.MulCert25519.num fun l => (((σ (.plug (8 * k + l))).val : ℤ) : Fp)

theorem sum_list {R : Type*} [CommRing R] (ts : List (ℤ × ℕ)) (g : ℕ → ℕ → R) :
    ∑ l ∈ Finset.range 8, 2 ^ (32 * l) * (ts.map fun t => (t.1 : R) * g t.2 l).sum =
      (ts.map fun t => (t.1 : R) * ∑ l ∈ Finset.range 8, 2 ^ (32 * l) * g t.2 l).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm]

set_option maxRecDepth 100000 in
/-- An operand `c + Σ kᵢ·vᵢ` is `num c + Σ kᵢ·Y vᵢ`. -/
theorem N_vec (d : ℕ → OpD) (o : ℕ) (σ : TVar → F) (c : ℕ → ℤ) (ts : List (ℤ × ℕ))
    (h : ∀ l < 8, d (o + l) = vec c ts l) :
    N d o σ = Xark.Templates.MulCert25519.num (fun l => ((c l : ℤ) : Fp)) +
      (ts.map fun t => (t.1 : Fp) * Y σ t.2).sum := by
  have e : N d o σ = ∑ l ∈ Finset.range 8, 2 ^ (32 * l) * (((c l : ℤ) : Fp) +
      (ts.map fun t => (t.1 : Fp) * (((σ (.plug (8 * t.2 + l))).val : ℤ) : Fp)).sum) := by
    simp only [N, Xark.Templates.MulCert25519.num]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [Finset.mem_range] at hl
    rw [h l hl]
    simp only [vec, OpD.z, opZ, List.map_map, Function.comp_def, Int.cast_add, Int.cast_list_sum,
      Int.cast_mul]
  rw [e]
  simp only [mul_add, Finset.sum_add_distrib, Y, Xark.Templates.MulCert25519.num]
  congr 1
  exact sum_list ts fun k l => (((σ (.plug (8 * k + l))).val : ℤ) : Fp)

/-- `p = 2²⁵⁵ − 19` limb-wise is `0` in `ZMod p`. -/
theorem num_pl : Xark.Templates.MulCert25519.num (fun l => ((pl l : ℤ) : Fp)) = 0 := by
  decide +kernel

theorem num_sm (c : ℤ) : Xark.Templates.MulCert25519.num (fun l => ((sm c l : ℤ) : Fp)) = c := by
  simp [Xark.Templates.MulCert25519.num, sm]

theorem num_b4 (c : ℤ) : Xark.Templates.MulCert25519.num (fun l => ((b4 c l : ℤ) : Fp)) = c := by
  have h0 := num_pl
  have h1 := num_sm c
  simp only [Xark.Templates.MulCert25519.num, Finset.sum_range_succ, Finset.sum_range_zero,
    b4, sm] at h0 h1 ⊢
  push_cast at h0 h1 ⊢
  linear_combination 4 * h0 + h1

/-- Zero limbs, and a constant's limbs. -/
def z0 : ℕ → ℤ := fun _ => 0
def cstv (v : ℕ) (j : ℕ) : ℤ := ((v / 2 ^ (32 * j)) % 2 ^ 32 : ℕ)

theorem num_z0 : Xark.Templates.MulCert25519.num (fun l => ((z0 l : ℤ) : Fp)) = 0 := by
  simp [Xark.Templates.MulCert25519.num, z0]

theorem num_dInv :
    Xark.Templates.MulCert25519.num (fun l => ((cstv dInv l : ℤ) : Fp)) = (dInv : Fp) := by
  decide +kernel

/-- `d·d⁻¹ = 1`. -/
theorem d_dInv : Xark.Ed25519.d * (dInv : Fp) = 1 := by decide


/-- The plugs' bounds give every certificate operand its `2³⁶` bound. -/
theorem ops_bounds (d : ℕ → ℕ → OpD) (σ : TVar → F) (np c : ℕ) (bd : ℕ → ℤ)
    (hv : ∀ i < np, ((σ (.plug i)).val : ℤ) ≤ bd i)
    (hidx : ∀ n < c, ∀ m < 56, ∀ t ∈ (d n m).2, t.2 < np)
    (hlh : ∀ n < c, ∀ m < 56, 0 ≤ (d n m).lo bd ∧ (d n m).hi bd < 2 ^ 36) :
    ∀ n < c, ∀ m < 56, 0 ≤ (d n m).z σ ∧ (d n m).z σ < 2 ^ 36 := fun n hn m hm => by
  have h := opZ_mem bd (d n m).1 (d n m).2 σ fun t ht => hv t.2 (hidx n hn m hm t ht)
  exact ⟨(hlh n hn m hm).1.trans h.1, h.2.trans_lt (hlh n hn m hm).2⟩

/-- The plug bound: below `base` (the inputs) `2³⁵`, from `base` (range-checked) `2³²`. -/
def bdOf (base : ℕ) (i : ℕ) : ℤ := if i < base then 2 ^ 35 - 1 else 2 ^ 32 - 1

/-- Every plug within its bound, from the inputs' assumption and the range rows. -/
theorem plugs_bd (base cnt _c : ℕ) (_d : ℕ → ℕ → OpD) (σ : TVar → F)
    (hin : ∀ i < base, (σ (.plug i)).val < 2 ^ 35)
    (hr : ∀ b < cnt, Xark.R1cs.Sat
      (Xark.Templates.MulCertK1.bitRows (LC.var (.plug (base + b))) (31 * b) 31) σ) :
    ∀ i < base + cnt, ((σ (.plug i)).val : ℤ) ≤ bdOf base i := fun i hi => by
  unfold bdOf
  split_ifs with h
  · have := hin i h; omega
  · have := range_sound base (i - base) σ (hr (i - base) (by omega))
    rw [show base + (i - base) = i by omega] at this
    omega


/-! ### Operands in blocks

A gadget's call `n` reads operand `b < 7` as `c + Σ kᵢ·vᵢ`, `blk n b = (c, [(kᵢ, vᵢ)])`. -/

abbrev Blk := ℕ → ℕ → (ℕ → ℤ) × List (ℤ × ℕ)

def ops' (blk : Blk) (n m : ℕ) : OpD := vec (blk n (m / 8)).1 (blk n (m / 8)).2 (m % 8)

/-- Operand `b` of call `n` in `ZMod p`. -/
def V (blk : Blk) (n b : ℕ) (σ : TVar → F) : Fp :=
  Xark.Templates.MulCert25519.num (fun l => (((blk n b).1 l : ℤ) : Fp)) +
    ((blk n b).2.map fun t => (t.1 : Fp) * Y σ t.2).sum

theorem N_blk (blk : Blk) (n b : ℕ) (σ : TVar → F) : N (ops' blk n) (8 * b) σ = V blk n b σ :=
  N_vec _ _ σ _ _ fun l hl => by
    simp only [ops', show (8 * b + l) / 8 = b by omega, show (8 * b + l) % 8 = l by omega]

theorem blk_sound (blk : Blk) (n o : ℕ) (σ : TVar → F)
    (h : Xark.R1cs.Sat (callRows (fd (ops' blk n)) o) σ)
    (hb : ∀ m < 56, 0 ≤ (ops' blk n m).z σ ∧ (ops' blk n m).z σ < 2 ^ 36) :
    V blk n 0 σ * V blk n 1 σ - V blk n 2 σ * V blk n 3 σ - V blk n 4 σ * V blk n 5 σ =
      V blk n 6 σ := by
  have := cert_sound _ o σ h hb
  simpa only [← N_blk] using this

/-- The inputs' value as coordinate vectors. -/
def X (ins : List F) (k : ℕ) : Fp :=
  Xark.Templates.MulCert25519.num fun l => (((ins.getD (8 * k + l) 0).val : ℤ) : Fp)


theorem getD_ins_of (t : Template) (np : ℕ) (h : t.inputs = (List.range np).map fun j => LC.var (.plug j))
    (σ : TVar → F) (i : ℕ) (hi : i < np) : (t.ins σ).getD i 0 = σ (.plug i) := by
  rw [Template.ins, h, List.getD_eq_getElem _ _ (by simpa using hi)]; simp

theorem X_of (t : Template) (np : ℕ) (h : t.inputs = (List.range np).map fun j => LC.var (.plug j))
    (σ : TVar → F) (k : ℕ) (hk : 8 * k + 8 ≤ np) : X (t.ins σ) k = Y σ k := by
  simp only [X, Y, Xark.Templates.MulCert25519.num]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [Finset.mem_range] at hl
  rw [getD_ins_of t np h σ _ (by omega)]


/-- Call `n`'s certificate equation. -/
def Eqn (blk : Blk) (n : ℕ) (σ : TVar → F) : Prop :=
  V blk n 0 σ * V blk n 1 σ - V blk n 2 σ * V blk n 3 σ - V blk n 4 σ * V blk n 5 σ = V blk n 6 σ

/-- **A gadget's model is sound**: on inputs below `2³⁵` its range-checked plugs are below
`2³²` and every call's certificate equation holds. -/
theorem model_sound (t : Template) (base cnt c : ℕ) (blk : Blk)
    (hin : t.inputs = (List.range (base + cnt)).map fun j => LC.var (.plug j))
    (hrows : t.rows = modelRows base cnt c (ops' blk))
    (hidx : ∀ n < c, ∀ m < 56, ∀ u ∈ (ops' blk n m).2, u.2 < base + cnt)
    (hlh : ∀ n < c, ∀ m < 56, 0 ≤ (ops' blk n m).lo (bdOf base) ∧ (ops' blk n m).hi (bdOf base) < 2 ^ 36)
    (σ : TVar → F) (ha : ∀ i < base, ((t.ins σ).getD i 0).val < 2 ^ 35) (h : t.Sat σ) :
    (∀ i, base ≤ i → i < base + cnt → ((t.ins σ).getD i 0).val < 2 ^ 32) ∧
      ∀ n < c, Eqn blk n σ := by
  rw [Template.Sat, hrows, sat_model] at h
  obtain ⟨hr, hc⟩ := h
  have hi : ∀ i < base, (σ (.plug i)).val < 2 ^ 35 := fun i h => by
    rw [← getD_ins_of t _ hin σ i (by omega)]; exact ha i h
  have hb := ops_bounds (ops' blk) σ _ c (bdOf base) (plugs_bd base cnt c (ops' blk) σ hi hr) hidx hlh
  refine ⟨fun i h1 h2 => ?_, fun n hn => blk_sound blk n _ σ (hc n hn) (hb n hn)⟩
  rw [getD_ins_of t _ hin σ i h2]
  have := range_sound base (i - base) σ (hr (i - base) (by omega))
  rwa [show base + (i - base) = i by omega] at this

end Xark.Templates.EdCheck
