/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.FakeGlvCheckK1
import Formal.CertCall
import Formal.CurvePrimes

set_option linter.style.header false
set_option linter.style.longLine false
set_option exponentiation.threshold 600

/-!
# `xark_secp256k1::fake_glv_check_k1`, proven over its exported rows

The scalar side of the fake-GLV verifier (Eagen–El Housni–Masson–Piellard, ePrint
2025/933). Plugs: `r = 0`, `s = 1`, `e = 2`, `x_R = 3` (4 × 64-bit limbs each), the hinted
`cₘ` (`16..19`, `kₘ = cₘ − 2⁶⁴`), `C` (`20..23`), and the quotients `q₁` (`24..29`), `q₂`
(`30..35`). The rows:

* `to_bits::<65>` of each `cₘ` (its outputs: the digits), `to_bits::<64>` of each limb of
  `C` (its outputs: `C`'s 256 bits) and of `q₁`, `q₂`;
* `(k₂² + k₃²)·w = 1`;
* two carry chains (`zero_chain`): for `A = k₀ + λk₁`, `B = k₂ + λk₃` the columns of
  `A·s + B·r + 2³²²·n − q₁·n` and of `C·s + B·e + 2³²²·n − q₂·n` in base `2⁶⁴`, with the
  products `kₘ·(λ-column)` and `C_i·s_j` as hinted product variables, each carry
  range-checked (`to_bits::<134>`, biased by `2¹³³`);
* `x_R = r + t·n` over 128-bit halves, `t`, `u` boolean.

`soundness`: on `r`, `s`, `e`, `x_R` limbs below `2⁶⁴`, every satisfying assignment has
`cₘ < 2⁶⁵` and `C < 2²⁵⁶` with the outputs their bits, `A·s + B·r ≡ 0` and
`C·s + B·e ≡ 0 (mod n)` (as integers), `B ≢ 0 (mod n)` (`glv_kernel`: `(k₂, k₃) ≠ 0` with
`|kₘ| ≤ 2⁶⁴`, and secp256k1's GLV kernel `{(a, b) : a + λb ≡ 0}` has no such vector), and
`x_R = r + t·n` with `t ∈ {0, 1}`. `Xark.FakeGlv.verify_sound` is the group side: in a
group of odd order `n`, the circuit's `2·(C·G + A·Q + B·R) = O` with these congruences
forces `R = u₁G + u₂Q`.
-/

namespace Xark.Templates.FakeGlvCheckK1

open Xark.Template Xark.R1cs Xark.Templates.EcK1Check
export Xark.Templates.Add32 (IsBit)

/-! ### The model -/

/-- secp256k1's group order `n`, and `λ`, limb-wise. -/
def nl (j : ℕ) : ℤ :=
  [13822214165235122497, 13451932020343611451, 18446744073709551614, 18446744073709551615].getD j 0
def ll (j : ℕ) : ℤ :=
  [16069571880186789234, 1310022930574435960, 11900229862571533402, 6008836872998760672].getD j 0

/-- Integer linear data over the template's variables: a constant and `(coeff, var)` terms. -/
abbrev ZL := ℤ × List (ℤ × TVar)

/-- Its linear combination, in the frontend's normal form. -/
def ZL.lc (d : ZL) : LC := norm ⟨(d.1 : F), d.2.map fun t => ((t.1 : F), t.2)⟩

def pv (i : ℕ) : LC := LC.var (.plug i)
def wv (i : ℕ) : LC := LC.var (.wit i)
/-- Plug `i`, and `kₘ = cₘ − 2⁶⁴`. -/
def pZ (i : ℕ) : ZL := (0, [(1, .plug i)])
def kZ (m : ℕ) : ZL := (-(2 ^ 64), [(1, .plug (16 + m))])

/-- Column `m` of `λ·v` (`v` at plugs `base..base + 3`). -/
def lamZL (base m : ℕ) : ZL :=
  (0, ((List.range 4).filter fun j => j ≤ m ∧ m - j < 4).map fun j => (ll j, .plug (base + m - j)))

/-- The products of `lam_cols(k_lo, k_hi, v)`: per column `m < 7`, `k_hi·λ-column`, then
for `m < 4` `k_lo·v_m`. -/
def lamPairs (lo hi base : ℕ) : List (ZL × ZL) :=
  (List.range 7).flatMap fun m =>
    (kZ hi, lamZL base m) :: if m < 4 then [(kZ lo, pZ (base + m))] else []
/-- Their variables in column `m`, from `w`. -/
def lamWits (w m : ℕ) : List ℕ :=
  if m < 4 then [w + 2 * m, w + 2 * m + 1] else if m < 7 then [w + 4 + m] else []

/-- The products of `mul_cols(g, s)`: `g_i·s_j`, `i` outer. -/
def mulPairs (gb sb : ℕ) : List (ZL × ZL) :=
  (List.range 4).flatMap fun i => (List.range 4).map fun j => (pZ (gb + i), pZ (sb + j))
def mulWits (w m : ℕ) : List ℕ :=
  ((List.range 4).flatMap fun i => (List.range 4).filterMap fun j =>
    if i + j = m then some (w + 4 * i + j) else none)

def prodRows (w : ℕ) (ps : List (ZL × ZL)) : List Row :=
  ps.mapIdx fun i p => ⟨p.1.lc, p.2.lc, wv (w + i)⟩

/-- The two product blocks: `B·r`, `A·s` from `1268`; `C·s`, `B·e` from `2354`. -/
def ps₁ : List (ZL × ZL) := lamPairs 2 3 0 ++ lamPairs 0 1 4
def ps₂ : List (ZL × ZL) := mulPairs 20 4 ++ lamPairs 2 3 8

/-- Column `m` of `z + 2³²²·n − q·n`, `z`'s products the variables `ws m`, `q` at plugs
`qb..qb + 5`. -/
def colZL (ws : ℕ → List ℕ) (qb m : ℕ) : ZL :=
  (if 5 ≤ m ∧ m < 9 then 4 * nl (m - 5) else 0,
    (ws m).map (fun w => (1, .wit w)) ++
      ((List.range 4).filter fun j => j ≤ m ∧ m - j < 6).map fun j => (-nl j, .plug (qb + m - j)))

/-- Step `m < 8`: `cols[m] + c_{m−1} − 2⁶⁴·c_m` with `c = h − 2¹³³`, `h` the plugs from `hb`. -/
def stepZL (ws : ℕ → List ℕ) (qb hb m : ℕ) : ZL :=
  ((colZL ws qb m).1 + 2 ^ 197 - (if m = 0 then 0 else 2 ^ 133),
    (colZL ws qb m).2 ++ (if m = 0 then [] else [(1, .plug (hb + m - 1))]) ++
      [(-(2 ^ 64), .plug (hb + m))])
/-- The last column: `cols[8] + c₇ = 0`. -/
def lastZL (ws : ℕ → List ℕ) (qb hb : ℕ) : ZL :=
  ((colZL ws qb 8).1 - 2 ^ 133, (colZL ws qb 8).2 ++ [(1, .plug (hb + 7))])

def eqRow (d : ZL) : Row := ⟨d.lc, ⟨1, []⟩, ⟨0, []⟩⟩

def chainRows (ws : ℕ → List ℕ) (qb hb w : ℕ) : List Row :=
  ((List.range 8).flatMap fun m =>
    MulCertK1.bitRows (pv (hb + m)) (w + 133 * m) 133 ++ [eqRow (stepZL ws qb hb m)]) ++
    [eqRow (lastZL ws qb hb)]

/-- Chain 1: `A·s + B·r`, products from `1268` (`B·r` first), carry bits from `1290`. -/
def ws₁ (m : ℕ) : List ℕ := lamWits 1279 m ++ lamWits 1268 m
/-- Chain 2: `C·s + B·e`, products from `2354` (`C·s` first), carry bits from `2381`. -/
def ws₂ (m : ℕ) : List ℕ := mulWits 2354 m ++ lamWits 2370 m

def nlo : ℤ := nl 0 + 2 ^ 64 * nl 1
def nhi : ℤ := nl 2 + 2 ^ 64 * nl 3

/-- The bit decompositions: `cₘ` (65 bits), `C`'s limbs, then `q₁ᵢ`, `q₂ᵢ` (64 bits). -/
def bitBlock : List Row :=
  ((List.range 4).flatMap fun m => MulCertK1.bitRows (pv (16 + m)) (64 * m) 64) ++
    ((List.range 4).flatMap fun i => MulCertK1.bitRows (pv (20 + i)) (256 + 63 * i) 63) ++
    (List.range 6).flatMap fun i =>
      MulCertK1.bitRows (pv (24 + i)) (508 + 126 * i) 63 ++
        MulCertK1.bitRows (pv (30 + i)) (508 + 126 * i + 63) 63

/-- `x_R = r + t·n` by halves, `t`, `u` the plugs `52`, `53`. -/
def lowZL : ZL :=
  (0, [(1, .plug 0), (2 ^ 64, .plug 1), (-1, .plug 12), (-(2 ^ 64), .plug 13), (nlo, .plug 52),
    (-(2 ^ 128), .plug 53)])
def highZL : ZL :=
  (0, [(-1, .plug 2), (-(2 ^ 64), .plug 3), (1, .plug 14), (2 ^ 64, .plug 15), (-nhi, .plug 52),
    (-1, .plug 53)])

/-- `(k₂² + k₃²)·w = 1`, and the bits `t`, `u` with `x_R = r + t·n`. -/
def kRows : List Row :=
  [⟨(kZ 2).lc, (kZ 2).lc, wv 1264⟩, ⟨(kZ 3).lc, (kZ 3).lc, wv 1265⟩,
    ⟨⟨0, [(1, .wit 1264), (1, .wit 1265)]⟩, wv 1266, ⟨1, []⟩⟩]
/-- `x·(1 − x) = 0` for plug `i`. -/
def boolRow (i : ℕ) : Row := ⟨pv i, ⟨1, [(-1, .plug i)]⟩, ⟨0, []⟩⟩
def tRows : List Row := [boolRow 52, boolRow 53, eqRow lowZL, eqRow highZL]

def modelRows : List Row :=
  bitBlock ++ kRows ++ prodRows 1268 ps₁ ++ chainRows ws₁ 24 36 1290 ++ prodRows 2354 ps₂ ++
    chainRows ws₂ 30 44 2381 ++ tRows

def modelOutputs : List LC :=
  ((List.range 4).flatMap fun m =>
    MulCertK1.lowOf (pv (16 + m)) (64 * m) 64 :: (List.range 64).map fun i => wv (64 * m + i)) ++
    (List.range 4).flatMap fun i =>
      MulCertK1.lowOf (pv (20 + i)) (256 + 63 * i) 63 ::
        (List.range 63).map fun b => wv (256 + 63 * i + b)

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = modelRows := by decide +kernel
set_option maxRecDepth 100000 in
theorem outputs_eq : template.outputs = modelOutputs := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 54).map fun j => LC.var (.plug j) := by
  decide +kernel


/-! ### Quadratic forms over the plugs

Each chain row, with every product variable replaced by its row's product, is a polynomial of
degree two in the plugs. `QF` writes one as monomials; `qnorm` sorts and merges them, so the
kernel compares two forms by `decide`, and `qval` reads one at the plugs' integer values. -/

/-- A monomial: a coefficient and the plugs it multiplies. -/
abbrev Mono := ℤ × List ℕ
abbrev QF := List Mono

def qval (τ : ℕ → ℤ) (q : QF) : ℤ := (q.map fun m => m.1 * (m.2.map τ).prod).sum

theorem qval_nil (τ : ℕ → ℤ) : qval τ [] = 0 := rfl
theorem qval_cons (τ : ℕ → ℤ) (m : Mono) (q : QF) :
    qval τ (m :: q) = m.1 * (m.2.map τ).prod + qval τ q := by simp [qval]
theorem qval_append (τ : ℕ → ℤ) (a b : QF) : qval τ (a ++ b) = qval τ a + qval τ b := by
  simp [qval]

/-- An order key for these monomials (at most two plugs, each below 99). -/
def key (l : List ℕ) : ℕ := l.foldl (fun a i => 100 * a + i + 1) 0

def qins (c : ℤ) (l : List ℕ) : QF → QF
  | [] => if c = 0 then [] else [(c, l)]
  | (d, u) :: qs =>
    if l = u then (if d + c = 0 then qs else (d + c, u) :: qs)
    else if key l < key u then (if c = 0 then (d, u) :: qs else (c, l) :: (d, u) :: qs)
    else (d, u) :: qins c l qs

def qnorm (q : QF) : QF := q.foldl (fun acc m => qins m.1 m.2 acc) []

theorem qval_qins (τ : ℕ → ℤ) (c : ℤ) (l : List ℕ) (q : QF) :
    qval τ (qins c l q) = c * (l.map τ).prod + qval τ q := by
  induction q with
  | nil => unfold qins; split_ifs with h <;> simp [qval, h]
  | cons m q ih =>
    obtain ⟨d, u⟩ := m
    unfold qins
    by_cases h1 : l = u
    · subst h1
      rw [if_pos rfl]
      split_ifs with h2
      · rw [qval_cons]; linear_combination (-(l.map τ).prod) * h2
      · rw [qval_cons, qval_cons]; ring
    · rw [if_neg h1]
      split_ifs with h3 h4
      · simp [qval_cons, h4]
      · simp only [qval_cons]
      · rw [qval_cons, qval_cons, ih]; ring

theorem qval_qnorm (τ : ℕ → ℤ) (q : QF) : qval τ (qnorm q) = qval τ q := by
  suffices ∀ acc : QF, qval τ (q.foldl (fun acc m => qins m.1 m.2 acc) acc) =
      qval τ acc + qval τ q by simpa [qnorm, qval_nil] using this []
  induction q with
  | nil => intro acc; simp [qval_nil]
  | cons m q ih => intro acc; rw [List.foldl_cons, ih, qval_qins, qval_cons]; ring

/-- Two forms with the same normal form have the same value. -/
theorem qval_eq {a b : QF} (h : qnorm a = qnorm b) (τ : ℕ → ℤ) : qval τ a = qval τ b := by
  rw [← qval_qnorm τ a, h, qval_qnorm]

def qscale (k : ℤ) (q : QF) : QF := q.map fun m => (k * m.1, m.2)

theorem qval_qscale (τ : ℕ → ℤ) (k : ℤ) (q : QF) : qval τ (qscale k q) = k * qval τ q := by
  induction q with
  | nil => simp [qscale, qval]
  | cons m q ih =>
    simp only [qscale, List.map_cons] at ih ⊢
    rw [qval_cons, qval_cons, ih]; ring

/-- A monomial's plugs in order (two at most). -/
def msort (l : List ℕ) : List ℕ := if l.getD 1 0 < l.getD 0 0 then l.reverse else l

theorem prod_msort (τ : ℕ → ℤ) (l : List ℕ) : ((msort l).map τ).prod = (l.map τ).prod := by
  unfold msort; split_ifs <;> simp [List.map_reverse, List.prod_reverse]

def qmul (a b : QF) : QF := a.flatMap fun x => b.map fun y => (x.1 * y.1, msort (x.2 ++ y.2))

theorem qval_map_mul (τ : ℕ → ℤ) (x : Mono) (b : QF) :
    qval τ (b.map fun y => (x.1 * y.1, msort (x.2 ++ y.2))) = x.1 * (x.2.map τ).prod * qval τ b := by
  induction b with
  | nil => simp [qval]
  | cons y b ih =>
    rw [List.map_cons, qval_cons, qval_cons, ih, prod_msort, List.map_append, List.prod_append]
    ring

theorem qval_qmul (τ : ℕ → ℤ) (a b : QF) : qval τ (qmul a b) = qval τ a * qval τ b := by
  induction a with
  | nil => simp [qmul, qval]
  | cons x a ih =>
    simp only [qmul, List.flatMap_cons] at ih ⊢
    rw [qval_append, ih, qval_map_mul, qval_cons]; ring

theorem qval_flatMap_zero (τ : ℕ → ℤ) (l : List ℕ) (f : ℕ → QF) (h : ∀ m ∈ l, qval τ (f m) = 0) :
    qval τ (l.flatMap f) = 0 := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [List.flatMap_cons, qval_append, h m (by simp), ih fun m hm => h m (by simp [hm])]; ring

/-- `|qval|` is at most the form with absolute coefficients at the plugs' bounds. -/
def qabs (B : ℕ → ℤ) (q : QF) : ℤ := (q.map fun m => |m.1| * (m.2.map B).prod).sum

theorem prod_bd (τ B : ℕ → ℤ) (h : ∀ i, 0 ≤ τ i ∧ τ i ≤ B i) (l : List ℕ) :
    0 ≤ (l.map τ).prod ∧ (l.map τ).prod ≤ (l.map B).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    obtain ⟨h0, h1⟩ := h i
    exact ⟨mul_nonneg h0 ih.1, mul_le_mul h1 ih.2 ih.1 (h0.trans h1)⟩

theorem abs_qval_le (τ B : ℕ → ℤ) (h : ∀ i, 0 ≤ τ i ∧ τ i ≤ B i) (q : QF) :
    |qval τ q| ≤ qabs B q := by
  induction q with
  | nil => simp [qval, qabs]
  | cons m q ih =>
    rw [qval_cons]
    have hp := prod_bd τ B h m.2
    have : |m.1 * (m.2.map τ).prod| ≤ |m.1| * (m.2.map B).prod := by
      rw [abs_mul, abs_of_nonneg hp.1]; exact mul_le_mul_of_nonneg_left hp.2 (abs_nonneg _)
    simp only [qabs, List.map_cons, List.sum_cons] at ih ⊢
    exact (abs_add_le _ _).trans (add_le_add this ih)

/-! ### Reading the rows as integer identities -/

/-- The product a variable holds: `ps₁` from `1268`, `ps₂` from `2354`. -/
def prodOf (w : ℕ) : Option (ZL × ZL) :=
  if 2354 ≤ w then ps₂[w - 2354]? else if 1268 ≤ w then ps₁[w - 1268]? else none

def pidx : TVar → ℕ
  | .plug i => i
  | .wit _ => 0

/-- A form over plugs only, as a `QF`. -/
def lin (d : ZL) : QF := (d.1, []) :: d.2.flatMap fun t => [(t.1, [pidx t.2])]

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
  | .plug i => decide (i < 54)
  | .wit _ => false

/-- Every variable a plug or a product variable of plugs. -/
def Closed (d : ZL) : Bool := d.2.all fun t =>
  match t.2 with
  | .plug i => decide (i < 54)
  | .wit w =>
    match prodOf w with
    | some p => PlugOnly p.1 && PlugOnly p.2
    | none => false

theorem getD_ins (σ : TVar → F) (i : ℕ) (hi : i < 54) :
    (template.ins σ).getD i 0 = σ (.plug i) := by
  rw [Template.ins, inputs_eq, List.getD_eq_getElem _ _ (by simpa using hi)]; simp

/-- Input `i`'s canonical value. -/
def ival (ins : List F) (i : ℕ) : ℤ := ((ins.getD i 0).val : ℤ)
abbrev vals (σ : TVar → F) : ℕ → ℤ := ival (template.ins σ)

theorem cast_vals (σ : TVar → F) (i : ℕ) (hi : i < 54) : ((vals σ i : ℤ) : F) = σ (.plug i) := by
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
  rw [ZL.lc, eval_norm, qval_cons]
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

theorem mem_modelRows {x : Row} (h : x ∈ bitBlock ∨ x ∈ prodRows 1268 ps₁ ∨ x ∈ chainRows ws₁ 24 36 1290 ∨
    x ∈ prodRows 2354 ps₂ ∨ x ∈ chainRows ws₂ 30 44 2381 ∨ x ∈ kRows ∨ x ∈ tRows) :
    x ∈ modelRows := by
  simp only [modelRows, List.mem_append]; tauto

/-- The product rows. -/
abbrev PSat (σ : TVar → F) : Prop := Xark.R1cs.Sat (prodRows 1268 ps₁ ++ prodRows 2354 ps₂) σ

theorem psat_of (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ) : PSat σ := fun x hx => by
  rcases List.mem_append.mp hx with h | h
  exacts [hs x (mem_modelRows (Or.inr (Or.inl h))),
    hs x (mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inl h)))))]

theorem prod_row (σ : TVar → F) (hs : PSat σ) (w : ℕ) (p : ZL × ZL)
    (hp : prodOf w = some p) : σ (.wit w) = p.1.lc.eval σ * p.2.lc.eval σ := by
  have key : ∀ (base : ℕ) (ps : List (ZL × ZL)) (i : ℕ),
      (∀ x ∈ prodRows base ps, x ∈ prodRows 1268 ps₁ ++ prodRows 2354 ps₂) → ps[i]? = some p →
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
  · have := key 2354 ps₂ (w - 2354) (fun _ hx => List.mem_append_right _ hx) hp
    rwa [show 2354 + (w - 2354) = w by omega] at this
  · have := key 1268 ps₁ (w - 1268) (fun _ hx => List.mem_append_left _ hx) hp
    rwa [show 1268 + (w - 1268) = w by omega] at this

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

theorem int_zero {z : ℤ} (h : ((z : ℤ) : F) = 0) (hb : |z| < (r : ℤ)) : z = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact Int.eq_zero_of_abs_lt_dvd h hb

/-- The plugs' bounds: `r`, `s`, `e`, `x_R`, `C`, `q` limbs below `2⁶⁴`, `cₘ` below `2⁶⁵`, the
carries below `2¹³⁴`, `t`, `u` bits. -/
def pB (i : ℕ) : ℤ :=
  if i < 16 then 2 ^ 64 - 1 else if i < 20 then 2 ^ 65 - 1 else if i < 36 then 2 ^ 64 - 1
  else if i < 52 then 2 ^ 134 - 1 else if i < 54 then 1 else r

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

def lamZ : ℤ := 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
/-- secp256k1's group order. -/
def nZ : ℤ := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- A 4 × 64-bit value from `b`, and a 6-limb one. -/
def L4 (v : ℕ → ℤ) (b : ℕ) : ℤ := v b + 2 ^ 64 * v (b + 1) + 2 ^ 128 * v (b + 2) + 2 ^ 192 * v (b + 3)
def L6 (v : ℕ → ℤ) (b : ℕ) : ℤ := L4 v b + 2 ^ 256 * v (b + 4) + 2 ^ 320 * v (b + 5)
/-- `kₘ = cₘ − 2⁶⁴`, `A = k₀ + λk₁`, `B = k₂ + λk₃`. -/
def kv (v : ℕ → ℤ) (m : ℕ) : ℤ := v (16 + m) - 2 ^ 64
def Av (v : ℕ → ℤ) : ℤ := kv v 0 + lamZ * kv v 1
def Bv (v : ℕ → ℤ) : ℤ := kv v 2 + lamZ * kv v 3

def limbQ (b : ℕ) : QF := [(1, [b]), (2 ^ 64, [b + 1]), (2 ^ 128, [b + 2]), (2 ^ 192, [b + 3])]
def limb6Q (b : ℕ) : QF := limbQ b ++ [(2 ^ 256, [b + 4]), (2 ^ 320, [b + 5])]
def kQ (lo hi : ℕ) : QF := lin (kZ lo) ++ qscale lamZ (lin (kZ hi))

/-- The chains' relations `A·s + B·r + 2³²²·n − q₁·n` and `C·s + B·e + 2³²²·n − q₂·n`. -/
def target₁ : QF :=
  qmul (kQ 0 1) (limbQ 4) ++ qmul (kQ 2 3) (limbQ 0) ++ [(2 ^ 322 * nZ, [])] ++ qscale (-nZ) (limb6Q 24)
def target₂ : QF :=
  qmul (limbQ 20) (limbQ 4) ++ qmul (kQ 2 3) (limbQ 8) ++ [(2 ^ 322 * nZ, [])] ++ qscale (-nZ) (limb6Q 30)

/-- A chain's rows, weighted by `2^(64m)`. -/
def csum (ws : ℕ → List ℕ) (qb hb : ℕ) : QF :=
  (List.range 8).flatMap (fun m => qscale (2 ^ (64 * m)) (qsub (stepZL ws qb hb m))) ++
    qscale (2 ^ 512) (qsub (lastZL ws qb hb))

theorem qval_limbQ (v : ℕ → ℤ) (b : ℕ) : qval v (limbQ b) = L4 v b := by
  simp [limbQ, L4, qval]; ring
theorem qval_limb6Q (v : ℕ → ℤ) (b : ℕ) : qval v (limb6Q b) = L6 v b := by
  rw [limb6Q, qval_append, qval_limbQ, L6]; simp [qval]; ring
theorem qval_kQ (v : ℕ → ℤ) (lo hi : ℕ) : qval v (kQ lo hi) = kv v lo + lamZ * kv v hi := by
  rw [kQ, qval_append, qval_qscale]; simp [lin, kZ, pidx, qval, kv]; ring

theorem qval_target₁ (v : ℕ → ℤ) :
    qval v target₁ = Av v * L4 v 4 + Bv v * L4 v 0 + 2 ^ 322 * nZ - nZ * L6 v 24 := by
  simp only [target₁, qval_append, qval_qmul, qval_kQ, qval_limbQ, qval_qscale, qval_limb6Q,
    qval_cons, qval_nil, List.map_nil, List.prod_nil, Av, Bv]; ring
theorem qval_target₂ (v : ℕ → ℤ) :
    qval v target₂ = L4 v 20 * L4 v 4 + Bv v * L4 v 8 + 2 ^ 322 * nZ - nZ * L6 v 30 := by
  simp only [target₂, qval_append, qval_qmul, qval_kQ, qval_limbQ, qval_qscale, qval_limb6Q,
    qval_cons, qval_nil, List.map_nil, List.prod_nil, Bv]; ring

set_option maxRecDepth 100000 in
theorem csum₁ : qnorm (csum ws₁ 24 36) = qnorm target₁ := by decide +kernel
set_option maxRecDepth 100000 in
theorem csum₂ : qnorm (csum ws₂ 30 44) = qnorm target₂ := by decide +kernel

/-- `x_R − (r + t·n)` from the two half rows. -/
def xQ : QF := limbQ 0 ++ [(nZ, [52])] ++ qscale (-1) (limbQ 12)
theorem xsum : qnorm (qsub lowZL ++ qscale (-(2 ^ 128)) (qsub highZL)) = qnorm xQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem closed : (∀ m < 8, Closed (stepZL ws₁ 24 36 m) = true ∧ Closed (stepZL ws₂ 30 44 m) = true ∧
    qabs pB (qsub (stepZL ws₁ 24 36 m)) < r ∧ qabs pB (qsub (stepZL ws₂ 30 44 m)) < r) ∧
    Closed (lastZL ws₁ 24 36) = true ∧ Closed (lastZL ws₂ 30 44) = true ∧
    qabs pB (qsub (lastZL ws₁ 24 36)) < r ∧ qabs pB (qsub (lastZL ws₂ 30 44)) < r ∧
    Closed lowZL = true ∧ Closed highZL = true ∧ qabs pB (qsub lowZL) < r ∧
    qabs pB (qsub highZL) < r := by
  decide +kernel


/-! ### Soundness -/

open Xark.Templates.Add32 (isBit_of_mul_self isBit_val word_lt testBit_word bit_eq_testBit)

/-- The rows of `to_bits::<m + 1>` inside the call output the bits of its input. -/
theorem bits_out (x : LC) (o m : ℕ) (hm : m + 1 ≤ 253) (σ : TVar → F)
    (h : Xark.R1cs.Sat (MulCertK1.bitRows x o m) σ) :
    (MulCertK1.lowOf x o m).eval σ :: (List.range m).map (fun i => σ (.wit (o + i))) =
      (List.range (m + 1)).map (bitOf (x.eval σ)) := by
  obtain ⟨hb, hl⟩ := (MulCertK1.sat_bitRows x o m σ).mp h
  have hw : ∀ i < m, IsBit (σ (.wit (o + i))) := fun i hi => isBit_of_mul_self (hb i hi)
  have hlow : IsBit ((MulCertK1.lowOf x o m).eval σ) := ToBits.isBit_of_mul_sub_one hl
  let v : ℕ → ℕ := fun i =>
    if i = 0 then ((MulCertK1.lowOf x o m).eval σ).val else (σ (.wit (o + (i - 1)))).val
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
    rw [MulCertK1.eval_lowOf]
    push_cast
    ring
  have hx : (x.eval σ).val = ∑ i ∈ Finset.range (m + 1), 2 ^ i * v i := by
    rw [← hcast, ZMod.val_natCast_of_lt (lt_trans hW (ToBits.two_pow_lt_r' hm))]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [bitOf, hx]
    exact bit_eq_testBit hlow (by simpa [v] using testBit_word v (m + 1) hv 0 (by omega))
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [bitOf, hx]
    exact bit_eq_testBit (hw i hi) (by simpa [v] using testBit_word v (m + 1) hv (i + 1) (by omega))

/-- The input assumption: the limbs of `r`, `s`, `e`, `x_R` (plugs `0..15`) are below `2⁶⁴`. In
`ecdsa_verify_packed` their producers enforce it (`formal/coverage-allowlist.txt`). -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins.take 16, v.val < 2 ^ 64

/-- The outputs: the 65 bits of each `cₘ` (its digits), then the 64 bits of each limb of `C`. -/
def digits (ins : List F) : List F :=
  (List.range 4).flatMap (fun m => (List.range 65).map (bitOf (ins.getD (16 + m) 0))) ++
    (List.range 4).flatMap fun i => (List.range 64).map (bitOf (ins.getD (20 + i) 0))

/-- `cₘ < 2⁶⁵`, `C`'s limbs below `2⁶⁴`, the outputs their bits, `A·s + B·r ≡ 0` and
`C·s + B·e ≡ 0 (mod n)`, `B ≢ 0 (mod n)`, and `x_R = r + t·n` with `t ∈ {0, 1}` (all as
integers: `ival ins i` is input `i`'s canonical value). -/
def Spec (ins outs : List F) : Prop :=
  (∀ m < 4, (ins.getD (16 + m) 0).val < 2 ^ 65) ∧ (∀ i < 4, (ins.getD (20 + i) 0).val < 2 ^ 64) ∧
    outs = digits ins ∧ nZ ∣ Av (ival ins) * L4 (ival ins) 4 + Bv (ival ins) * L4 (ival ins) 0 ∧
    nZ ∣ L4 (ival ins) 20 * L4 (ival ins) 4 + Bv (ival ins) * L4 (ival ins) 8 ∧ ¬nZ ∣ Bv (ival ins) ∧
    ∃ t : ℤ, (t = 0 ∨ t = 1) ∧ L4 (ival ins) 12 = L4 (ival ins) 0 + t * nZ

/-- **No short GLV kernel vector.** `a + λb ≡ 0 (mod n)` with `|a|, |b| ≤ 2⁶⁴` forces
`a = b = 0`: the kernel is spanned by `(a₁, b₁)`, `(a₂, b₂)` (128-bit, `a₁b₂ − a₂b₁ = n`), and
the cross products `a·bᵢ − b·aᵢ` are multiples of `n` below `n` in size. -/
theorem glv_kernel (a b : ℤ) (ha : |a| ≤ 2 ^ 64) (hb : |b| ≤ 2 ^ 64) (h : nZ ∣ a + lamZ * b) :
    a = 0 ∧ b = 0 := by
  have k1 : nZ ∣ 64502973549206556628585045361533709077 +
      lamZ * (-303414439467246543595250775667605759171) :=
    ⟨-98834128363575826231712400374302886273, by norm_num [nZ, lamZ]⟩
  have k2 : nZ ∣ 367917413016453100223835821029139468248 +
      lamZ * 64502973549206556628585045361533709077 :=
    ⟨21011179226632705335158493575954588082, by norm_num [nZ, lamZ]⟩
  rw [abs_le] at ha hb
  have c1 : a * (-303414439467246543595250775667605759171) -
      b * 64502973549206556628585045361533709077 = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (m := nZ) ?_ ?_
    · have := (h.mul_left (-303414439467246543595250775667605759171)).sub (k1.mul_left b)
      rw [show a * (-303414439467246543595250775667605759171) - b * 64502973549206556628585045361533709077 =
        -303414439467246543595250775667605759171 * (a + lamZ * b) - b * (64502973549206556628585045361533709077 +
          lamZ * (-303414439467246543595250775667605759171)) by ring]
      exact this
    · rw [abs_lt]; unfold nZ; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have c2 : a * 64502973549206556628585045361533709077 -
      b * 367917413016453100223835821029139468248 = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (m := nZ) ?_ ?_
    · have := (h.mul_left 64502973549206556628585045361533709077).sub (k2.mul_left b)
      rw [show a * 64502973549206556628585045361533709077 - b * 367917413016453100223835821029139468248 =
        64502973549206556628585045361533709077 * (a + lamZ * b) - b * (367917413016453100223835821029139468248 +
          lamZ * 64502973549206556628585045361533709077) by ring]
      exact this
    · rw [abs_lt]; unfold nZ; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hbn : b * nZ = 0 := by
    unfold nZ
    linear_combination (-64502973549206556628585045361533709077) * c1 +
      (-303414439467246543595250775667605759171) * c2
  have hb0 : b = 0 := (mul_eq_zero.mp hbn).resolve_right (by unfold nZ; norm_num)
  subst hb0
  exact ⟨by linarith, rfl⟩

theorem vals_nonneg (σ : TVar → F) (i : ℕ) : 0 ≤ vals σ i := by unfold vals ival; exact Int.natCast_nonneg _

theorem bit_plug (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ) (i o m : ℕ) (hm : m + 1 ≤ 253)
    (hi : i < 54) (hsub : ∀ x ∈ MulCertK1.bitRows (pv i) o m, x ∈ modelRows) :
    vals σ i < 2 ^ (m + 1) := by
  have := MulCertK1.bits_sound (pv i) o m hm σ fun x hx => hs x (hsub x hx)
  rw [vals, ival, getD_ins σ i hi]
  simp only [pv, eval_var] at this
  exact_mod_cast this

theorem bool_plug (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ) (i : ℕ) (hi : i < 54)
    (hm : boolRow i ∈ modelRows) : vals σ i = 0 ∨ vals σ i = 1 := by
  have := hs _ hm
  simp only [Row.Sat, boolRow, pv, eval_var] at this
  simp only [LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
  have hx : σ (.plug i) * σ (.plug i) = σ (.plug i) := by linear_combination -this
  rcases isBit_of_mul_self hx with h | h <;> rw [vals, ival, getD_ins σ i hi, h] <;> simp

theorem mem_bitBlock_c (m : ℕ) (hm : m < 4) :
    ∀ x ∈ MulCertK1.bitRows (pv (16 + m)) (64 * m) 64, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, hx⟩))))
theorem mem_bitBlock_g (m : ℕ) (hm : m < 4) :
    ∀ x ∈ MulCertK1.bitRows (pv (20 + m)) (256 + 63 * m) 63, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, hx⟩))))
theorem mem_bitBlock_q1 (m : ℕ) (hm : m < 6) :
    ∀ x ∈ MulCertK1.bitRows (pv (24 + m)) (508 + 126 * m) 63, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, List.mem_append_left _ hx⟩)))
theorem mem_bitBlock_q2 (m : ℕ) (hm : m < 6) :
    ∀ x ∈ MulCertK1.bitRows (pv (30 + m)) (508 + 126 * m + 63) 63, x ∈ modelRows := fun _ hx =>
  mem_modelRows (Or.inl (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, List.mem_append_right _ hx⟩)))
theorem mem_chain_bits (ws : ℕ → List ℕ) (qb hb w : ℕ) (m : ℕ) (hm : m < 8) :
    ∀ x ∈ MulCertK1.bitRows (pv (hb + m)) (w + 133 * m) 133, x ∈ chainRows ws qb hb w := fun _ hx =>
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, List.mem_append_left _ hx⟩)

/-- Every plug within `pB`. -/
theorem vals_bd (σ : TVar → F) (ha : Assumptions (template.ins σ))
    (hs : Xark.R1cs.Sat modelRows σ) : ∀ i, 0 ≤ vals σ i ∧ vals σ i ≤ pB i := by
  intro i
  refine ⟨vals_nonneg σ i, ?_⟩
  have hlen : (template.ins σ).length = 54 := by rw [Template.ins, inputs_eq]; simp
  unfold pB
  split_ifs with h1 h2 h3 h4 h5
  · have := ha _ (getD_mem_take h1 (by omega))
    simp only [vals, ival]; zify at this; linarith
  · obtain ⟨m, rfl⟩ : ∃ m, i = 16 + m := ⟨i - 16, by omega⟩
    have := bit_plug σ hs _ _ 64 (by norm_num) (by omega) (mem_bitBlock_c m (by omega))
    norm_num at this; linarith
  · by_cases h24 : i < 24
    · obtain ⟨m, rfl⟩ : ∃ m, i = 20 + m := ⟨i - 20, by omega⟩
      have := bit_plug σ hs _ _ 63 (by norm_num) (by omega) (mem_bitBlock_g m (by omega))
      norm_num at this; linarith
    · by_cases h30 : i < 30
      · obtain ⟨m, rfl⟩ : ∃ m, i = 24 + m := ⟨i - 24, by omega⟩
        have := bit_plug σ hs _ _ 63 (by norm_num) (by omega) (mem_bitBlock_q1 m (by omega))
        norm_num at this; linarith
      · obtain ⟨m, rfl⟩ : ∃ m, i = 30 + m := ⟨i - 30, by omega⟩
        have := bit_plug σ hs _ _ 63 (by norm_num) (by omega) (mem_bitBlock_q2 m (by omega))
        norm_num at this; linarith
  · by_cases h44 : i < 44
    · obtain ⟨m, rfl⟩ : ∃ m, i = 36 + m := ⟨i - 36, by omega⟩
      have := bit_plug σ hs _ _ 133 (by norm_num) (by omega) fun _ hx =>
        mem_modelRows (Or.inr (Or.inr (Or.inl (mem_chain_bits ws₁ 24 36 1290 m (by omega) _ hx))))
      norm_num at this; linarith
    · obtain ⟨m, rfl⟩ : ∃ m, i = 44 + m := ⟨i - 44, by omega⟩
      have := bit_plug σ hs _ _ 133 (by norm_num) (by omega) fun _ hx =>
        mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (mem_chain_bits ws₂ 30 44 2381 m (by omega) _ hx))))))
      norm_num at this; linarith
  · have hb : vals σ i = 0 ∨ vals σ i = 1 := by
      by_cases h52 : i = 52
      · subst h52; exact bool_plug σ hs 52 (by norm_num)
          (mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (.head _))))))))
      · obtain rfl : i = 53 := by omega
        exact bool_plug σ hs 53 (by norm_num)
          (mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (.tail _ (.head _)))))))))
    omega
  · have := ZMod.val_lt ((template.ins σ).getD i 0)
    simp only [vals, ival]; exact_mod_cast this.le

/-- A chain's rows make its weighted sum zero. -/
theorem chain_zero (σ : TVar → F) (hs : Xark.R1cs.Sat modelRows σ)
    (hbd : ∀ i, 0 ≤ vals σ i ∧ vals σ i ≤ pB i) (ws : ℕ → List ℕ) (qb hb w : ℕ)
    (hsub : ∀ x ∈ chainRows ws qb hb w, x ∈ modelRows)
    (hc : ∀ m < 8, Closed (stepZL ws qb hb m) = true ∧ qabs pB (qsub (stepZL ws qb hb m)) < r)
    (hl : Closed (lastZL ws qb hb) = true) (hlb : qabs pB (qsub (lastZL ws qb hb)) < r) :
    qval (vals σ) (csum ws qb hb) = 0 := by
  rw [csum, qval_append, qval_qscale, qval_flatMap_zero,
    zero_of_row σ hs hbd _ hl hlb (hsub _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))]
  · ring
  · intro m hm
    have hm := List.mem_range.mp hm
    rw [qval_qscale, zero_of_row σ hs hbd _ (hc m hm).1 (hc m hm).2 (hsub _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, List.mem_append_right _
        (List.mem_singleton.mpr rfl)⟩))), mul_zero]

theorem qval_lin_kZ (v : ℕ → ℤ) (m : ℕ) : qval v (lin (kZ m)) = kv v m := by
  simp [lin, kZ, pidx, qval, kv]; ring

theorem mem_tRows (x : Row) (h : x ∈ tRows) : x ∈ modelRows :=
  mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- The outputs are the digits. -/
theorem outs_eq (σ : TVar → F) (h : Xark.R1cs.Sat modelRows σ) :
    template.outs σ = digits (template.ins σ) := by
  rw [Template.outs, outputs_eq, modelOutputs, digits, List.map_append, List.map_flatMap,
    List.map_flatMap, List.flatMap_def, List.flatMap_def, List.flatMap_def, List.flatMap_def]
  have blk : ∀ (b o k : ℕ), b < 54 → k + 1 ≤ 253 →
      (∀ x ∈ MulCertK1.bitRows (pv b) o k, x ∈ modelRows) →
      (MulCertK1.lowOf (pv b) o k :: (List.range k).map fun i => wv (o + i)).map (·.eval σ) =
        (List.range (k + 1)).map (bitOf ((template.ins σ).getD b 0)) := by
    intro b o k hb hk hsub
    have := bits_out (pv b) o k hk σ fun x hx => h x (hsub x hx)
    simp only [pv, eval_var] at this
    rw [getD_ins σ _ hb, ← this, List.map_cons, List.map_map]
    simp [pv, wv, Function.comp_def]
  refine congrArg₂ (· ++ ·) (congrArg List.flatten (List.map_congr_left fun m hm => ?_))
    (congrArg List.flatten (List.map_congr_left fun m hm => ?_))
  · exact blk _ _ 64 (by have := List.mem_range.mp hm; omega) (by norm_num)
      (mem_bitBlock_c m (List.mem_range.mp hm))
  · exact blk _ _ 63 (by have := List.mem_range.mp hm; omega) (by norm_num)
      (mem_bitBlock_g m (List.mem_range.mp hm))

/-- **Soundness.** -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [Template.Sat, rows_eq] at h
  have hbd := vals_bd σ ha h
  obtain ⟨hc, l1, l2, lb1, lb2, clo, chi, blo, bhi⟩ := closed
  -- The two chains.
  have e1 := qval_eq csum₁ (vals σ)
  rw [chain_zero σ h hbd ws₁ 24 36 1290 (fun x hx => mem_modelRows (Or.inr (Or.inr (Or.inl hx))))
    (fun m hm => ⟨(hc m hm).1, (hc m hm).2.2.1⟩) l1 lb1, qval_target₁] at e1
  have e2 := qval_eq csum₂ (vals σ)
  rw [chain_zero σ h hbd ws₂ 30 44 2381
    (fun x hx => mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))
    (fun m hm => ⟨(hc m hm).2.1, (hc m hm).2.2.2⟩) l2 lb2, qval_target₂] at e2
  -- x_R = r + t·n.
  have ex := qval_eq xsum (vals σ)
  rw [qval_append, qval_qscale,
    zero_of_row σ h hbd _ clo blo (mem_tRows _ (.tail _ (.tail _ (.head _)))),
    zero_of_row σ h hbd _ chi bhi (mem_tRows _ (.tail _ (.tail _ (.tail _ (.head _)))))] at ex
  simp only [xQ, qval_append, qval_qscale, qval_limbQ, qval_cons, qval_nil, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil] at ex
  have ht := bool_plug σ h 52 (by norm_num) (mem_tRows _ (.head _))
  -- (k₂, k₃) ≠ 0.
  have hk : ¬(kv (vals σ) 2 = 0 ∧ kv (vals σ) 3 = 0) := by
    rintro ⟨h2, h3⟩
    have r1 := h _ (mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (.head _))))))))
    have r2 := h _ (mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (.tail _ (.head _)))))))))
    have r3 := h _ (mem_modelRows (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (.tail _ (.tail _ (.head _))))))))))
    simp only [Row.Sat, wv, eval_var] at r1 r2 r3
    rw [eval_lin σ _ (by decide), qval_lin_kZ, h2] at r1
    rw [eval_lin σ _ (by decide), qval_lin_kZ, h3] at r2
    simp only [LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at r3
    rw [← r1, ← r2] at r3
    simp at r3
  have kb : ∀ m, m < 4 → |kv (vals σ) m| ≤ 2 ^ 64 := fun m hm => by
    have := hbd (16 + m)
    simp only [pB, show ¬16 + m < 16 by omega, show 16 + m < 20 by omega, if_false, if_true] at this
    rw [kv, abs_le]; constructor <;> linarith [this.1, this.2]
  refine ⟨fun m hm => ?_, fun i hi => ?_, ?_, ⟨L6 (vals σ) 24 - 2 ^ 322, by linear_combination -e1⟩,
    ⟨L6 (vals σ) 30 - 2 ^ 322, by linear_combination -e2⟩, fun hd => hk ?_,
    ⟨vals σ 52, ht, by linear_combination ex⟩⟩
  · have := hbd (16 + m)
    simp only [pB, show ¬16 + m < 16 by omega, show 16 + m < 20 by omega, if_false, if_true] at this
    have h2 : (vals σ (16 + m) : ℤ) < 2 ^ 65 := by linarith [this.2]
    simp only [vals, ival] at h2; exact_mod_cast h2
  · have := hbd (20 + i)
    simp only [pB, show ¬20 + i < 16 by omega, show ¬20 + i < 20 by omega,
      show 20 + i < 36 by omega, if_false, if_true] at this
    have h2 : (vals σ (20 + i) : ℤ) < 2 ^ 64 := by linarith [this.2]
    simp only [vals, ival] at h2; exact_mod_cast h2
  · exact outs_eq σ h
  · exact glv_kernel _ _ (kb 2 (by norm_num)) (kb 3 (by norm_num)) hd

end Xark.Templates.FakeGlvCheckK1

namespace Xark.FakeGlv

/-- **The group side of fake GLV.** In a group that `n` kills (`n` an odd prime, as secp256k1's
order), the circuit's `2·(C·G + A·Q + B·R) = 0` with `A ≡ −B·u₂`, `C ≡ −B·u₁ (mod n)` and
`B ≢ 0` (`FakeGlvCheckK1.soundness`) forces `R = u₁G + u₂Q`: `2B` is invertible mod `n`. -/
theorem verify_sound {G : Type*} [AddCommGroup G] (n : ℕ) (hp : n.Prime) (h2 : n ≠ 2)
    (hn : ∀ x : G, (n : ℤ) • x = 0) (g q R : G) (A B C u1 u2 : ℤ)
    (hA : (n : ℤ) ∣ A + B * u2) (hC : (n : ℤ) ∣ C + B * u1) (hB : ¬(n : ℤ) ∣ B)
    (h : (2 : ℤ) • (C • g + A • q + B • R) = 0) : R = u1 • g + u2 • q := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨c, hc⟩ := hC
  have e : (2 : ℤ) • (C • g + A • q + B • R) =
      (2 * B) • (R - (u1 • g + u2 • q)) + (2 * c) • ((n : ℤ) • g) + (2 * a) • ((n : ℤ) • q) := by
    rw [show C = n * c - B * u1 by linarith, show A = n * a - B * u2 by linarith]
    simp only [smul_add, smul_sub, sub_smul, smul_smul]
    module
  rw [e, hn g, hn q, smul_zero, smul_zero, add_zero, add_zero] at h
  have hpz := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (n : ℤ) (2 * B) := (Prime.coprime_iff_not_dvd hpz).mpr fun hd => by
    rcases hpz.dvd_or_dvd hd with h2' | h2'
    · have h' : (n : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2'
      have := hp.two_le
      omega
    · exact hB h2'
  obtain ⟨u, v, huv⟩ := hcop
  have : R - (u1 • g + u2 • q) = 0 := by
    rw [← one_smul ℤ (R - (u1 • g + u2 • q)), ← huv, add_smul, mul_smul, mul_smul, hn, h,
      smul_zero, smul_zero, add_zero]
  exact sub_eq_zero.mp this

end Xark.FakeGlv
