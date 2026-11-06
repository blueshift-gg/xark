/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.FakeGlvK1
import Formal.Templates.FakeGlvCheckR1
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Tauto
import Mathlib.Data.List.GetD

set_option linter.style.header false
set_option linter.style.longLine false
set_option exponentiation.threshold 600

/-!
# `xark_secp256r1::fake_glv_check_r1`, proven over its exported rows

The scalar side of the P-256 fake-GLV verifier (ePrint 2025/933) with no endomorphism, so
the split is 2-dimensional. Plugs: `r = 0`, `s = 1`, `e = 2`, `x_R = 3` (4 × 64-bit limbs
each, plugs `0..15`), the hinted `a`, `b` (`16`, `17`; `A = a − 2¹²⁹`, `B = b − 2¹²⁹`), `C`
(`18..21`), the quotients `q₁` (`22`) and `q₂` (`23..27`), the biased carries `h₁`
(`28..30`) and `h₂` (`31..37`), and `t`, `u` (`38`, `39`). The rows:

* `to_bits::<130>` of `a`, `b` (its outputs: the digits), `to_bits::<64>` of each limb of `C`
  (its outputs: `C`'s 256 bits), `to_bits::<132>` of `q₁`, `to_bits::<64>` of each `q₂` limb;
* `(b − 2¹²⁹)·w = 1`;
* two carry chains (`zero_chain`): the columns of `a·s + b·r − 2¹²⁹(s + r) + 2¹³¹n − q₁n` and
  of `C·s + b·e − 2¹²⁹e + 2¹³¹n − q₂n` in base `2⁶⁴`, with the products as hinted product
  variables, each carry range-checked (`to_bits::<135>`, biased by `2¹³⁴`);
* `x_R = r + t·n` over 128-bit halves, `t`, `u` boolean.

The chains are modelled as in `Formal/FakeGlvK1.lean` (whose quadratic forms `QF` this
file reuses), for any number of columns.

`soundness`: on `r`, `s`, `e`, `x_R` limbs below `2⁶⁴`, every satisfying assignment has
`a, b < 2¹³⁰`, `C < 2²⁵⁶` with the outputs their bits, `A·s + B·r ≡ 0` and
`C·s + B·e ≡ 0 (mod n)`, `B ≢ 0 (mod n)` (`B ≠ 0` and `|B| ≤ 2¹²⁹ < n`), and
`x_R = r + t·n` with `t ∈ {0, 1}`. `Xark.FakeGlv.verify_sound` is the group side.
-/

namespace Xark.Templates.FakeGlvCheckR1

open Xark.Template Xark.R1cs Xark.Templates.EcK1Check
open Xark.Templates.FakeGlvCheckK1 (ZL pv wv pZ Mono QF qval qval_nil qval_cons qval_append qnorm
  qval_qnorm qval_eq qscale qval_qscale qmul qval_qmul qval_flatMap_zero qabs abs_qval_le pidx lin
  int_zero bits_out boolRow eqRow limbQ L4 qval_limbQ)
export Xark.Templates.Add32 (IsBit)

/-! ### The model -/

/-- P-256's group order `n`, limb-wise. -/
def nl (j : ℕ) : ℤ :=
  [17562291160714782033, 13611842547513532036, 18446744073709551615, 18446744069414584320].getD j 0

/-- `A = a − 2¹²⁹`, `B = b − 2¹²⁹`. -/
def aZ : ZL := (-(2 ^ 129), [(1, .plug 16)])
def bZ : ZL := (-(2 ^ 129), [(1, .plug 17)])

/-- Column `m`'s products: `a·s_m`, `b·r_m` (chain 1); `C_i·s_{m−i}`, then `b·e_m` (chain 2). -/
def cols₁ (m : ℕ) : List (ZL × ZL) := if m < 4 then [(pZ 16, pZ (4 + m)), (pZ 17, pZ m)] else []
def cols₂ (m : ℕ) : List (ZL × ZL) :=
  (((List.range 4).filter fun i => i ≤ m ∧ m - i < 4).map fun i => (pZ (18 + i), pZ (4 + m - i))) ++
    if m < 4 then [(pZ 17, pZ (8 + m))] else []

def ps₁ : List (ZL × ZL) := (List.range 4).flatMap cols₁
def ps₂ : List (ZL × ZL) := (List.range 8).flatMap cols₂

/-- Column `m`'s product variables, from `w`. -/
def colWits (cs : ℕ → List (ZL × ZL)) (w m : ℕ) : List ℕ :=
  (List.range (cs m).length).map fun k => w + ((List.range m).map fun j => (cs j).length).sum + k

def prodRows (w : ℕ) (ps : List (ZL × ZL)) : List Row :=
  ps.mapIdx fun i p => ⟨p.1.lc, p.2.lc, wv (w + i)⟩

/-- Column `m` of chain 1, `a·s + b·r − 2¹²⁹(s + r) + 2¹³¹n − q₁n`, and of chain 2,
`C·s + b·e − 2¹²⁹e + 2¹³¹n − q₂n`. -/
def col₁ (m : ℕ) : ZL :=
  (if m < 4 then 2 ^ 131 * nl m else 0,
    (colWits cols₁ 958 m).map (fun w => (1, .wit w)) ++
      if m < 4 then [(-(2 ^ 129), .plug (4 + m)), (-(2 ^ 129), .plug m), (-nl m, .plug 22)] else [])
def col₂ (m : ℕ) : ZL :=
  (if m < 4 then 2 ^ 131 * nl m else 0,
    (colWits cols₂ 1368 m).map (fun w => (1, .wit w)) ++
      (if m < 4 then [(-(2 ^ 129), .plug (8 + m))] else []) ++
      ((List.range 4).filter fun i => i ≤ m ∧ m - i < 5).map fun i => (-nl i, .plug (23 + m - i)))

/-- Step `m < N`: `col m + c_{m−1} − 2⁶⁴·c_m` with `c = h − 2¹³⁴`, `h` the plugs from `hb`. -/
def stepZL (col : ℕ → ZL) (hb m : ℕ) : ZL :=
  ((col m).1 + 2 ^ 198 - (if m = 0 then 0 else 2 ^ 134),
    (col m).2 ++ (if m = 0 then [] else [(1, .plug (hb + m - 1))]) ++ [(-(2 ^ 64), .plug (hb + m))])
/-- The last column: `col N + c_{N−1} = 0`. -/
def lastZL (col : ℕ → ZL) (hb N : ℕ) : ZL :=
  ((col N).1 - 2 ^ 134, (col N).2 ++ [(1, .plug (hb + N - 1))])

def chainRows (col : ℕ → ZL) (hb w N : ℕ) : List Row :=
  ((List.range N).flatMap fun m =>
    MulCertK1.bitRows (pv (hb + m)) (w + 134 * m) 134 ++ [eqRow (stepZL col hb m)]) ++
    [eqRow (lastZL col hb N)]

def nlo : ℤ := nl 0 + 2 ^ 64 * nl 1
def nhi : ℤ := nl 2 + 2 ^ 64 * nl 3

/-- The bit decompositions: `a`, `b` (130 bits), `C`'s limbs, `q₁` (132 bits), `q₂`'s limbs. -/
def bitBlock : List Row :=
  MulCertK1.bitRows (pv 16) 0 129 ++ MulCertK1.bitRows (pv 17) 129 129 ++
    ((List.range 4).flatMap fun i => MulCertK1.bitRows (pv (18 + i)) (258 + 63 * i) 63) ++
    MulCertK1.bitRows (pv 22) 510 131 ++
    (List.range 5).flatMap fun i => MulCertK1.bitRows (pv (23 + i)) (641 + 63 * i) 63

/-- `(b − 2¹²⁹)·w = 1`. -/
def invRow : Row := ⟨bZ.lc, wv 956, ⟨1, []⟩⟩

/-- `x_R = r + t·n` by halves, `t`, `u` the plugs `38`, `39`. -/
def lowZL : ZL :=
  (0, [(1, .plug 0), (2 ^ 64, .plug 1), (-1, .plug 12), (-(2 ^ 64), .plug 13), (nlo, .plug 38),
    (-(2 ^ 128), .plug 39)])
def highZL : ZL :=
  (0, [(-1, .plug 2), (-(2 ^ 64), .plug 3), (1, .plug 14), (2 ^ 64, .plug 15), (-nhi, .plug 38),
    (-1, .plug 39)])
def tRows : List Row := [boolRow 38, boolRow 39, eqRow lowZL, eqRow highZL]

def modelRows : List Row :=
  bitBlock ++ [invRow] ++ prodRows 958 ps₁ ++ chainRows col₁ 28 966 3 ++ prodRows 1368 ps₂ ++
    chainRows col₂ 31 1388 7 ++ tRows

def modelOutputs : List LC :=
  (MulCertK1.lowOf (pv 16) 0 129 :: (List.range 129).map fun i => wv i) ++
    (MulCertK1.lowOf (pv 17) 129 129 :: (List.range 129).map fun i => wv (129 + i)) ++
    (List.range 4).flatMap fun i =>
      MulCertK1.lowOf (pv (18 + i)) (258 + 63 * i) 63 ::
        (List.range 63).map fun b => wv (258 + 63 * i + b)

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows := by decide +kernel
set_option maxRecDepth 100000 in
theorem outputs_eq : template.outputs = modelOutputs := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 40).map fun j => LC.var (.plug j) := by
  decide +kernel


/-! ### Reading the rows as integer identities -/

/-- The product a variable holds: `ps₁` from `958`, `ps₂` from `1368`. -/
def prodOf (w : ℕ) : Option (ZL × ZL) :=
  if 1368 ≤ w then ps₂[w - 1368]? else if 958 ≤ w then ps₁[w - 958]? else none

/-- A term with its product variable replaced by the product. -/
def sub1 (t : ℤ × TVar) : QF :=
  match t.2 with
  | .plug i => [(t.1, [i])]
  | .wit w =>
    match prodOf w with
    | some p => qscale t.1 (qmul (lin p.1) (lin p.2))
    | none => []

def qsub (d : ZL) : QF := (d.1, []) :: d.2.flatMap sub1

def PlugOnly (d : ZL) : Bool := d.2.all fun t =>
  match t.2 with
  | .plug i => decide (i < 40)
  | .wit _ => false

/-- Every variable a plug or a product variable of plugs. -/
def Closed (d : ZL) : Bool := d.2.all fun t =>
  match t.2 with
  | .plug i => decide (i < 40)
  | .wit w =>
    match prodOf w with
    | some p => PlugOnly p.1 && PlugOnly p.2
    | none => false

theorem getD_ins (σ : TVar → F) (i : ℕ) (hi : i < 40) :
    (template.ins σ).getD i 0 = σ (.plug i) := by
  rw [Template.ins, inputs_eq, List.getD_eq_getElem _ _ (by simpa using hi)]; simp

/-- Input `i`'s canonical value. -/
def ival (ins : List F) (i : ℕ) : ℤ := ((ins.getD i 0).val : ℤ)
abbrev vals (σ : TVar → F) : ℕ → ℤ := ival (template.ins σ)

theorem cast_vals (σ : TVar → F) (i : ℕ) (hi : i < 40) : ((vals σ i : ℤ) : F) = σ (.plug i) := by
  rw [vals, ival, getD_ins σ i hi]; simp

theorem eval_terms (σ : TVar → F) (g : ℤ × TVar → QF) (ts : List (ℤ × TVar))
    (hg : ∀ t ∈ ts, (t.1 : F) * σ t.2 = ((qval (vals σ) (g t) : ℤ) : F)) :
    ((ts.map fun t => ((t.1 : F), t.2)).map fun t => t.1 * σ t.2).sum =
      ((qval (vals σ) (ts.flatMap g) : ℤ) : F) := by
  induction ts with
  | nil => simp [qval]
  | cons t ts ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.flatMap_cons, qval_append, Int.cast_add,
      hg t (by simp), ih fun t ht => hg t (by simp [ht])]

theorem eval_lc (σ : TVar → F) (g : ℤ × TVar → QF) (d : ZL)
    (hg : ∀ t ∈ d.2, (t.1 : F) * σ t.2 = ((qval (vals σ) (g t) : ℤ) : F)) :
    d.lc.eval σ = ((qval (vals σ) ((d.1, []) :: d.2.flatMap g) : ℤ) : F) := by
  rw [FakeGlvCheckK1.ZL.lc, eval_norm, qval_cons]
  simp only [LC.eval, List.map_nil, List.prod_nil, mul_one, Int.cast_add]
  rw [eval_terms σ g d.2 hg]

theorem eval_lin (σ : TVar → F) (d : ZL) (hd : PlugOnly d = true) :
    d.lc.eval σ = ((qval (vals σ) (lin d) : ℤ) : F) := by
  refine eval_lc σ _ d fun t ht => ?_
  simp only [PlugOnly, List.all_eq_true] at hd
  have := hd t ht
  obtain ⟨k, v⟩ := t
  cases v with
  | plug i =>
    simp only [decide_eq_true_eq] at this
    simp [qval, pidx, cast_vals σ i this]
  | wit w => simp at this

theorem mem_modelRows {x : Row} (h : x ∈ bitBlock ∨ x = invRow ∨ x ∈ prodRows 958 ps₁ ∨
    x ∈ chainRows col₁ 28 966 3 ∨ x ∈ prodRows 1368 ps₂ ∨ x ∈ chainRows col₂ 31 1388 7 ∨
    x ∈ tRows) : x ∈ modelRows := by
  simp only [modelRows, List.mem_append, List.mem_singleton]; tauto

/-- The product rows. -/
abbrev PSat (σ : TVar → F) : Prop := Xark.R1cs.Sat (prodRows 958 ps₁ ++ prodRows 1368 ps₂) σ

theorem psat_of (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ) : PSat σ := fun x hx => by
  rcases List.mem_append.mp hx with h | h
  exacts [hs x (mem_modelRows (Or.inr (Or.inr (Or.inl h)))),
    hs x (mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))]

theorem prod_row (σ : TVar → F) (hs : PSat σ) (w : ℕ) (p : ZL × ZL)
    (hp : prodOf w = some p) : σ (.wit w) = p.1.lc.eval σ * p.2.lc.eval σ := by
  have key : ∀ (base : ℕ) (ps : List (ZL × ZL)) (i : ℕ),
      (∀ x ∈ prodRows base ps, x ∈ prodRows 958 ps₁ ++ prodRows 1368 ps₂) → ps[i]? = some p →
        σ (.wit (base + i)) = p.1.lc.eval σ * p.2.lc.eval σ := by
    intro base ps i hsub hi
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
    have hm : (⟨ps[i].1.lc, ps[i].2.lc, wv (base + i)⟩ : Row) ∈ prodRows base ps := by
      rw [prodRows, List.mem_iff_getElem]
      exact ⟨i, by simpa using hlt, by simp⟩
    have := hs _ (hsub _ hm)
    simpa [Row.Sat, wv, LC.var, LC.eval] using this.symm
  unfold prodOf at hp
  split_ifs at hp with h1 h2
  · have := key 1368 ps₂ (w - 1368) (fun _ hx => List.mem_append_right _ hx) hp
    rwa [show 1368 + (w - 1368) = w by omega] at this
  · have := key 958 ps₁ (w - 958) (fun _ hx => List.mem_append_left _ hx) hp
    rwa [show 958 + (w - 958) = w by omega] at this

/-- A closed form's value is its substituted form's integer value. -/
theorem eval_qsub (σ : TVar → F) (hs : PSat σ) (d : ZL) (hd : Closed d = true) :
    d.lc.eval σ = ((qval (vals σ) (qsub d) : ℤ) : F) := by
  refine eval_lc σ sub1 d fun t ht => ?_
  simp only [Closed, List.all_eq_true] at hd
  have := hd t ht
  obtain ⟨k, v⟩ := t
  cases v with
  | plug i =>
    simp only [decide_eq_true_eq] at this
    simp [sub1, qval, cast_vals σ i this]
  | wit w =>
    cases hp : prodOf w with
    | none => simp [hp] at this
    | some p =>
      simp only [hp, Bool.and_eq_true] at this
      simp only [sub1, hp, qval_qscale, qval_qmul, Int.cast_mul]
      rw [prod_row σ hs w p hp, eval_lin σ p.1 this.1, eval_lin σ p.2 this.2]

/-- The plugs' bounds: `r`, `s`, `e`, `x_R` limbs below `2⁶⁴`, `a`, `b` below `2¹³⁰`, `C`'s
limbs below `2⁶⁴`, `q₁` below `2¹³²`, `q₂`'s limbs below `2⁶⁴`, the carries below `2¹³⁵`,
`t`, `u` bits. -/
def pB (i : ℕ) : ℤ :=
  if i < 16 then 2 ^ 64 - 1 else if i < 18 then 2 ^ 130 - 1 else if i < 22 then 2 ^ 64 - 1
  else if i < 23 then 2 ^ 132 - 1 else if i < 28 then 2 ^ 64 - 1 else if i < 38 then 2 ^ 135 - 1
  else if i < 40 then 1 else r

/-- A closed row `d = 0` with `qabs pB` below `r` is an integer identity. -/
theorem zero_of_row (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ)
    (hbd : ∀ i, 0 ≤ vals σ i ∧ vals σ i ≤ pB i) (d : ZL) (hd : Closed d = true)
    (hq : qabs pB (qsub d) < r) (hrow : eqRow d ∈ modelRows) : qval (vals σ) (qsub d) = 0 := by
  have := hs _ hrow
  simp only [Row.Sat, eqRow] at this
  rw [eval_qsub σ (psat_of σ hs) d hd] at this
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero, mul_one] at this
  exact int_zero this ((abs_qval_le _ _ hbd _).trans_lt hq)

/-! ### The readings -/

/-- P-256's group order. -/
def nZ : ℤ := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

/-- A 5 × 64-bit value from `b`. -/
def L5 (v : ℕ → ℤ) (b : ℕ) : ℤ := L4 v b + 2 ^ 256 * v (b + 4)
/-- `A = a − 2¹²⁹`, `B = b − 2¹²⁹`. -/
def Av (v : ℕ → ℤ) : ℤ := v 16 - 2 ^ 129
def Bv (v : ℕ → ℤ) : ℤ := v 17 - 2 ^ 129

def limb5Q (b : ℕ) : QF := limbQ b ++ [(2 ^ 256, [b + 4])]

/-- The chains' relations `A·s + B·r + 2¹³¹n − q₁n` and `C·s + B·e + 2¹³¹n − q₂n`. -/
def target₁ : QF :=
  qmul (lin aZ) (limbQ 4) ++ qmul (lin bZ) (limbQ 0) ++ [(2 ^ 131 * nZ, []), (-nZ, [22])]
def target₂ : QF :=
  qmul (limbQ 18) (limbQ 4) ++ qmul (lin bZ) (limbQ 8) ++ [(2 ^ 131 * nZ, [])] ++
    qscale (-nZ) (limb5Q 23)

/-- A chain's rows, weighted by `2^(64m)`. -/
def csum (col : ℕ → ZL) (hb N : ℕ) : QF :=
  (List.range N).flatMap (fun m => qscale (2 ^ (64 * m)) (qsub (stepZL col hb m))) ++
    qscale (2 ^ (64 * N)) (qsub (lastZL col hb N))

theorem qval_limb5Q (v : ℕ → ℤ) (b : ℕ) : qval v (limb5Q b) = L5 v b := by
  rw [limb5Q, qval_append, qval_limbQ, L5]; simp [qval]
theorem qval_aZ (v : ℕ → ℤ) : qval v (lin aZ) = Av v := by simp [lin, aZ, pidx, qval, Av]; ring
theorem qval_bZ (v : ℕ → ℤ) : qval v (lin bZ) = Bv v := by simp [lin, bZ, pidx, qval, Bv]; ring

theorem qval_target₁ (v : ℕ → ℤ) :
    qval v target₁ = Av v * L4 v 4 + Bv v * L4 v 0 + 2 ^ 131 * nZ - nZ * v 22 := by
  simp only [target₁, qval_append, qval_qmul, qval_aZ, qval_bZ, qval_limbQ, qval_cons, qval_nil,
    List.map_nil, List.prod_nil, List.map_cons, List.prod_cons]; ring
theorem qval_target₂ (v : ℕ → ℤ) :
    qval v target₂ = L4 v 18 * L4 v 4 + Bv v * L4 v 8 + 2 ^ 131 * nZ - nZ * L5 v 23 := by
  simp only [target₂, qval_append, qval_qmul, qval_bZ, qval_limbQ, qval_qscale, qval_limb5Q,
    qval_cons, qval_nil, List.map_nil, List.prod_nil]; ring

set_option maxRecDepth 100000 in
theorem csum₁ : qnorm (csum col₁ 28 3) = qnorm target₁ := by decide +kernel
set_option maxRecDepth 100000 in
theorem csum₂ : qnorm (csum col₂ 31 7) = qnorm target₂ := by decide +kernel

/-- `x_R − (r + t·n)` from the two half rows. -/
def xQ : QF := limbQ 0 ++ [(nZ, [38])] ++ qscale (-1) (limbQ 12)
theorem xsum : qnorm (qsub lowZL ++ qscale (-(2 ^ 128)) (qsub highZL)) = qnorm xQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem closed :
    (∀ m < 3, Closed (stepZL col₁ 28 m) = true ∧ qabs pB (qsub (stepZL col₁ 28 m)) < r) ∧
    (∀ m < 7, Closed (stepZL col₂ 31 m) = true ∧ qabs pB (qsub (stepZL col₂ 31 m)) < r) ∧
    Closed (lastZL col₁ 28 3) = true ∧ Closed (lastZL col₂ 31 7) = true ∧
    qabs pB (qsub (lastZL col₁ 28 3)) < r ∧ qabs pB (qsub (lastZL col₂ 31 7)) < r ∧
    Closed lowZL = true ∧ Closed highZL = true ∧ qabs pB (qsub lowZL) < r ∧
    qabs pB (qsub highZL) < r := by
  decide +kernel


/-! ### Soundness -/

open Xark.Templates.Add32 (isBit_of_mul_self)

theorem vals_nonneg (σ : TVar → F) (i : ℕ) : 0 ≤ vals σ i := by
  unfold vals ival; exact Int.natCast_nonneg _

theorem bit_plug (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ) (i o m : ℕ) (hm : m + 1 ≤ 253)
    (hi : i < 40) (hsub : ∀ x ∈ MulCertK1.bitRows (pv i) o m, x ∈ modelRows) :
    vals σ i < 2 ^ (m + 1) := by
  have := MulCertK1.bits_sound (pv i) o m hm σ fun x hx => hs x (hsub x hx)
  rw [vals, ival, getD_ins σ i hi]
  simp only [pv, eval_var] at this
  exact_mod_cast this

theorem bool_plug (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ) (i : ℕ) (hi : i < 40)
    (hm : boolRow i ∈ modelRows) : vals σ i = 0 ∨ vals σ i = 1 := by
  have := hs _ hm
  simp only [Row.Sat, boolRow, pv, eval_var] at this
  simp only [LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
  have hx : σ (.plug i) * σ (.plug i) = σ (.plug i) := by linear_combination -this
  rcases isBit_of_mul_self hx with h | h <;> rw [vals, ival, getD_ins σ i hi, h] <;> simp

theorem mem_bb_a : ∀ x ∈ MulCertK1.bitRows (pv 16) 0 129, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ hx)))))
theorem mem_bb_b : ∀ x ∈ MulCertK1.bitRows (pv 17) 129 129, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ hx)))))
theorem mem_bb_c (m : ℕ) (hm : m < 4) :
    ∀ x ∈ MulCertK1.bitRows (pv (18 + m)) (258 + 63 * m) 63, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, hx⟩)))))
theorem mem_bb_d : ∀ x ∈ MulCertK1.bitRows (pv 22) 510 131, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_left _ (List.mem_append_right _ hx)))
theorem mem_bb_e (m : ℕ) (hm : m < 5) :
    ∀ x ∈ MulCertK1.bitRows (pv (23 + m)) (641 + 63 * m) 63, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, hx⟩)))
theorem mem_chain_bits (col : ℕ → ZL) (hb w N m : ℕ) (hm : m < N) :
    ∀ x ∈ MulCertK1.bitRows (pv (hb + m)) (w + 134 * m) 134, x ∈ chainRows col hb w N := fun _ hx =>
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, List.mem_append_left _ hx⟩)
theorem mem_chain₁ {x : Row} (hx : x ∈ chainRows col₁ 28 966 3) : x ∈ modelRows :=
  mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inl hx))))
theorem mem_chain₂ {x : Row} (hx : x ∈ chainRows col₂ 31 1388 7) : x ∈ modelRows :=
  mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))
theorem mem_tRows (x : Row) (h : x ∈ tRows) : x ∈ modelRows :=
  mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- The input assumption: the limbs of `r`, `s`, `e`, `x_R` (plugs `0..15`) are below `2⁶⁴`.
`ecdsa_verify` enforces it (`unpack4`'s range checks, `range_check_limbs` on `R`;
`formal/coverage-allowlist.txt`). -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins.take 16, v.val < 2 ^ 64

/-- Every plug within `pB`. -/
theorem vals_bd (σ : TVar → F) (ha : Assumptions (template.ins σ))
    (hs : Xark.R1cs.Sat modelRows σ) : ∀ i, 0 ≤ vals σ i ∧ vals σ i ≤ pB i := by
  intro i
  refine ⟨vals_nonneg σ i, ?_⟩
  have hlen : (template.ins σ).length = 40 := by rw [Template.ins, inputs_eq]; simp
  unfold pB
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · have := ha _ (getD_mem_take h1 (by omega))
    simp only [vals, ival]; zify at this; linarith
  · rcases (show i = 16 ∨ i = 17 by omega) with rfl | rfl
    · have := bit_plug σ hs _ _ 129 (by norm_num) (by norm_num) mem_bb_a; norm_num at this; linarith
    · have := bit_plug σ hs _ _ 129 (by norm_num) (by norm_num) mem_bb_b; norm_num at this; linarith
  · obtain ⟨m, rfl⟩ : ∃ m, i = 18 + m := ⟨i - 18, by omega⟩
    have := bit_plug σ hs _ _ 63 (by norm_num) (by omega) (mem_bb_c m (by omega))
    norm_num at this; linarith
  · obtain rfl : i = 22 := by omega
    have := bit_plug σ hs _ _ 131 (by norm_num) (by norm_num) mem_bb_d; norm_num at this; linarith
  · obtain ⟨m, rfl⟩ : ∃ m, i = 23 + m := ⟨i - 23, by omega⟩
    have := bit_plug σ hs _ _ 63 (by norm_num) (by omega) (mem_bb_e m (by omega))
    norm_num at this; linarith
  · by_cases h31 : i < 31
    · obtain ⟨m, rfl⟩ : ∃ m, i = 28 + m := ⟨i - 28, by omega⟩
      have := bit_plug σ hs _ _ 134 (by norm_num) (by omega) fun _ hx =>
        mem_chain₁ (mem_chain_bits col₁ 28 966 3 m (by omega) _ hx)
      norm_num at this; linarith
    · obtain ⟨m, rfl⟩ : ∃ m, i = 31 + m := ⟨i - 31, by omega⟩
      have := bit_plug σ hs _ _ 134 (by norm_num) (by omega) fun _ hx =>
        mem_chain₂ (mem_chain_bits col₂ 31 1388 7 m (by omega) _ hx)
      norm_num at this; linarith
  · have hb : vals σ i = 0 ∨ vals σ i = 1 := by
      by_cases h38 : i = 38
      · subst h38; exact bool_plug σ hs 38 (by norm_num) (mem_tRows _ (.head _))
      · obtain rfl : i = 39 := by omega
        exact bool_plug σ hs 39 (by norm_num) (mem_tRows _ (.tail _ (.head _)))
    omega
  · have := ZMod.val_lt ((template.ins σ).getD i 0)
    simp only [vals, ival]; exact_mod_cast this.le

/-- A chain's rows make its weighted sum zero. -/
theorem chain_zero (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ)
    (hbd : ∀ i, 0 ≤ vals σ i ∧ vals σ i ≤ pB i) (col : ℕ → ZL) (hb w N : ℕ)
    (hsub : ∀ x ∈ chainRows col hb w N, x ∈ modelRows)
    (hc : ∀ m < N, Closed (stepZL col hb m) = true ∧ qabs pB (qsub (stepZL col hb m)) < r)
    (hl : Closed (lastZL col hb N) = true) (hlb : qabs pB (qsub (lastZL col hb N)) < r) :
    qval (vals σ) (csum col hb N) = 0 := by
  rw [csum, qval_append, qval_qscale, qval_flatMap_zero,
    zero_of_row σ hs hbd _ hl hlb (hsub _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))]
  · ring
  · intro m hm
    have hm := List.mem_range.mp hm
    rw [qval_qscale, zero_of_row σ hs hbd _ (hc m hm).1 (hc m hm).2 (hsub _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, List.mem_append_right _
        (List.mem_singleton.mpr rfl)⟩))), mul_zero]

/-- The outputs: the 130 bits of `a` and of `b` (the digits), then the 64 bits of each limb of
`C`. -/
def digits (ins : List F) : List F :=
  (List.range 130).map (bitOf (ins.getD 16 0)) ++ (List.range 130).map (bitOf (ins.getD 17 0)) ++
    (List.range 4).flatMap fun i => (List.range 64).map (bitOf (ins.getD (18 + i) 0))

/-- The outputs are the digits. -/
theorem outs_eq (σ : TVar → F) (h : Xark.R1cs.Sat modelRows σ) :
    template.outs σ = digits (template.ins σ) := by
  have blk : ∀ (b o k : ℕ), b < 40 → k + 1 ≤ 253 →
      (∀ x ∈ MulCertK1.bitRows (pv b) o k, x ∈ modelRows) →
      (MulCertK1.lowOf (pv b) o k :: (List.range k).map fun i => wv (o + i)).map (·.eval σ) =
        (List.range (k + 1)).map (bitOf ((template.ins σ).getD b 0)) := by
    intro b o k hb hk hsub
    have := bits_out (pv b) o k hk σ fun x hx => h x (hsub x hx)
    simp only [pv, eval_var] at this
    rw [getD_ins σ _ hb, ← this, List.map_cons, List.map_map]
    simp [pv, wv, Function.comp_def]
  rw [Template.outs, outputs_eq, modelOutputs,
    show ((List.range 129).map fun i => wv i) = (List.range 129).map fun i => wv (0 + i) by simp,
    digits, List.map_append, List.map_append, List.map_flatMap, List.flatMap_def, List.flatMap_def,
    blk 16 0 129 (by norm_num) (by norm_num) mem_bb_a, blk 17 129 129 (by norm_num) (by norm_num) mem_bb_b]
  refine congrArg _ (congrArg List.flatten (List.map_congr_left fun m hm => ?_))
  exact blk _ _ 63 (by have := List.mem_range.mp hm; omega) (by norm_num)
    (mem_bb_c m (List.mem_range.mp hm))

/-- `a, b < 2¹³⁰`, `C`'s limbs below `2⁶⁴`, the outputs their bits, `A·s + B·r ≡ 0` and
`C·s + B·e ≡ 0 (mod n)`, `B ≢ 0 (mod n)`, and `x_R = r + t·n` with `t ∈ {0, 1}` (as integers). -/
def Spec (ins outs : List F) : Prop :=
  (∀ m < 2, (ins.getD (16 + m) 0).val < 2 ^ 130) ∧ (∀ i < 4, (ins.getD (18 + i) 0).val < 2 ^ 64) ∧
    outs = digits ins ∧ nZ ∣ Av (ival ins) * L4 (ival ins) 4 + Bv (ival ins) * L4 (ival ins) 0 ∧
    nZ ∣ L4 (ival ins) 18 * L4 (ival ins) 4 + Bv (ival ins) * L4 (ival ins) 8 ∧ ¬nZ ∣ Bv (ival ins) ∧
    ∃ t : ℤ, (t = 0 ∨ t = 1) ∧ L4 (ival ins) 12 = L4 (ival ins) 0 + t * nZ

/-- `B ≢ 0 (mod n)` from `B ≠ 0` and `|B| ≤ 2¹²⁹ < n`. -/
theorem not_dvd_B (B : ℤ) (h0 : B ≠ 0) (hb : |B| ≤ 2 ^ 129) : ¬nZ ∣ B := fun hd =>
  h0 (Int.eq_zero_of_abs_lt_dvd hd (by unfold nZ; linarith))

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [Template.Sat, rows_eq] at h
  have hbd := vals_bd σ ha h
  obtain ⟨hc1, hc2, l1, l2, lb1, lb2, clo, chi, blo, bhi⟩ := closed
  have e1 := qval_eq csum₁ (vals σ)
  rw [chain_zero σ h hbd col₁ 28 966 3 (fun x hx => mem_chain₁ hx) hc1 l1 lb1, qval_target₁] at e1
  have e2 := qval_eq csum₂ (vals σ)
  rw [chain_zero σ h hbd col₂ 31 1388 7 (fun x hx => mem_chain₂ hx) hc2 l2 lb2, qval_target₂] at e2
  have ex := qval_eq xsum (vals σ)
  rw [qval_append, qval_qscale,
    zero_of_row σ h hbd _ clo blo (mem_tRows _ (.tail _ (.tail _ (.head _)))),
    zero_of_row σ h hbd _ chi bhi (mem_tRows _ (.tail _ (.tail _ (.tail _ (.head _)))))] at ex
  simp only [xQ, qval_append, qval_qscale, qval_limbQ, qval_cons, qval_nil, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil] at ex
  have ht := bool_plug σ h 38 (by norm_num) (mem_tRows _ (.head _))
  -- B ≠ 0, from `(b − 2¹²⁹)·w = 1`.
  have hB : Bv (vals σ) ≠ 0 := by
    intro h0
    have r1 := h _ (mem_modelRows (Or.inr (Or.inl rfl)))
    simp only [Row.Sat, invRow, wv, eval_var] at r1
    rw [eval_lin σ _ (by decide), qval_bZ, h0] at r1
    simp [LC.eval] at r1
  have hBb : |Bv (vals σ)| ≤ 2 ^ 129 := by
    have := hbd 17
    simp only [pB, show ¬(17 : ℕ) < 16 by norm_num, show (17 : ℕ) < 18 by norm_num, if_false,
      if_true] at this
    rw [Bv, abs_le]; constructor <;> linarith [this.1, this.2]
  refine ⟨fun m hm => ?_, fun i hi => ?_, outs_eq σ h, ⟨vals σ 22 - 2 ^ 131, by linear_combination -e1⟩,
    ⟨L5 (vals σ) 23 - 2 ^ 131, by linear_combination -e2⟩, not_dvd_B _ hB hBb,
    ⟨vals σ 38, ht, by linear_combination ex⟩⟩
  · have := hbd (16 + m)
    simp only [pB, show ¬16 + m < 16 by omega, show 16 + m < 18 by omega, if_false, if_true] at this
    have h2 : (vals σ (16 + m) : ℤ) < 2 ^ 130 := by linarith [this.2]
    simp only [vals, ival] at h2; exact_mod_cast h2
  · have := hbd (18 + i)
    simp only [pB, show ¬18 + i < 16 by omega, show ¬18 + i < 18 by omega,
      show 18 + i < 22 by omega, if_false, if_true] at this
    have h2 : (vals σ (18 + i) : ℤ) < 2 ^ 64 := by linarith [this.2]
    simp only [vals, ival] at h2; exact_mod_cast h2

end Xark.Templates.FakeGlvCheckR1
