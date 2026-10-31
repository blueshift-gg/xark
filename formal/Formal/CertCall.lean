/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.CertBits

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A certificate called inside a larger template

The generic part of the point-op proofs (`Formal/EcK1Check.lean`, `Formal/EcR1Check.lean`)
and the fake-GLV checks: substituting a callee's plugs by the caller's linear forms
(`sub`, `view`) in the frontend's normal form (`norm`), and operand limbs as integer linear
forms of the plugs (`OpD`) with their range over bounded plugs (`opZ_mem`).
-/

namespace Xark.Templates.EcK1Check

open Xark.Template Xark.R1cs

/-! ### Substitution and the frontend's normal form -/

/-- Each variable `v` replaced by the combination `g v`. -/
def sub (g : TVar → LC) (l : LC) : LC :=
  ⟨l.const + (l.terms.map fun t => t.1 * (g t.2).const).sum,
    l.terms.flatMap fun t => (g t.2).terms.map fun u => (t.1 * u.1, u.2)⟩

theorem eval_sub (g : TVar → LC) (l : LC) (σ : TVar → F) :
    (sub g l).eval σ = l.eval fun v => (g v).eval σ := by
  obtain ⟨c, ts⟩ := l
  simp only [sub, LC.eval]
  induction ts generalizing c with
  | nil => simp
  | cons t ts ih =>
    have := ih 0
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
      List.sum_append, zero_add] at this ⊢
    have hm : ((g t.2).terms.map fun u => (t.1 * u.1, u.2)).map (fun t => t.1 * σ t.2) =
        (g t.2).terms.map fun u => t.1 * (u.1 * σ u.2) := by
      simp only [List.map_map]; congr 1; funext u; simp [Function.comp, mul_assoc]
    rw [hm, List.sum_map_mul_left]
    linear_combination this

/-- The frontend's variable order: plugs, then variables, each by index. -/
def before : TVar → TVar → Bool
  | .plug a, .plug b => a < b
  | .plug _, .wit _ => true
  | .wit _, .plug _ => false
  | .wit a, .wit b => a < b

/-- Add `c·v` to sorted, merged terms. -/
def ins (c : F) (v : TVar) : List (F × TVar) → List (F × TVar)
  | [] => if c = 0 then [] else [(c, v)]
  | (d, u) :: ts =>
    if v = u then (if d + c = 0 then ts else (d + c, u) :: ts)
    else if before v u then (if c = 0 then (d, u) :: ts else (c, v) :: (d, u) :: ts)
    else (d, u) :: ins c v ts

def normT (ts : List (F × TVar)) : List (F × TVar) := ts.foldl (fun acc t => ins t.1 t.2 acc) []

/-- A combination in normal form. -/
def norm (l : LC) : LC := ⟨l.const, normT l.terms⟩

theorem sum_ins (c : F) (v : TVar) (ts : List (F × TVar)) (σ : TVar → F) :
    ((ins c v ts).map fun t => t.1 * σ t.2).sum = c * σ v + (ts.map fun t => t.1 * σ t.2).sum := by
  induction ts with
  | nil => unfold ins; split_ifs with h <;> simp [h]
  | cons t ts ih =>
    obtain ⟨d, u⟩ := t
    unfold ins
    by_cases h1 : v = u
    · subst h1
      rw [if_pos rfl]
      split_ifs with h2
      · simp only [List.map_cons, List.sum_cons]; linear_combination (-σ v) * h2
      · simp only [List.map_cons, List.sum_cons]; ring
    · rw [if_neg h1]
      split_ifs with h3 h4
      · simp [h4]
      · simp only [List.map_cons, List.sum_cons]
      · simp only [List.map_cons, List.sum_cons, ih]; ring

theorem eval_norm (l : LC) (σ : TVar → F) : (norm l).eval σ = l.eval σ := by
  obtain ⟨c, ts⟩ := l
  simp only [norm, normT, LC.eval]
  congr 1
  suffices ∀ acc : List (F × TVar), ((ts.foldl (fun acc t => ins t.1 t.2 acc) acc).map
      fun t => t.1 * σ t.2).sum = (acc.map fun t => t.1 * σ t.2).sum +
        (ts.map fun t => t.1 * σ t.2).sum by simpa using this []
  induction ts with
  | nil => simp
  | cons t ts ih => intro acc; rw [List.foldl_cons, ih, sum_ins]; simp; ring

theorem eval_var (v : TVar) (σ : TVar → F) : (LC.var v : LC).eval σ = σ v := by
  simp [LC.var, LC.eval]

/-- `sub` then `norm`. -/
def nsub (g : TVar → LC) (l : LC) : LC := norm (sub g l)

theorem eval_nsub (g : TVar → LC) (l : LC) (σ : TVar → F) :
    (nsub g l).eval σ = l.eval fun v => (g v).eval σ := by rw [nsub, eval_norm, eval_sub]

def rowSub (g : TVar → LC) (r : Row) : Row := ⟨nsub g r.a, nsub g r.b, nsub g r.c⟩

theorem sat_rowSub (g : TVar → LC) (rs : List Row) (σ : TVar → F) :
    Xark.R1cs.Sat (rs.map (rowSub g)) σ ↔ Xark.R1cs.Sat rs fun v => (g v).eval σ := by
  simp [Xark.R1cs.Sat, Row.Sat, rowSub, eval_nsub]

/-! ### A certificate inside a larger template -/

/-- A certificate's variables seen from a call: plug `j` is the operand `f j`, variable
`i` is the caller's `o + i`. -/
def view (f : ℕ → LC) (o : ℕ) : TVar → LC
  | .plug j => f j
  | .wit i => LC.var (.wit (o + i))

/-- An operand limb `c + Σ kᵢ·plugᵢ` with integer coefficients. -/
def op (c : ℤ) (ts : List (ℤ × ℕ)) : LC := ⟨(c : F), ts.map fun t => ((t.1 : F), .plug t.2)⟩

/-- Its integer value at the plugs' canonical values. -/
def opZ (c : ℤ) (ts : List (ℤ × ℕ)) (σ : TVar → F) : ℤ :=
  c + (ts.map fun t => t.1 * ((σ (.plug t.2)).val : ℤ)).sum

theorem eval_op (c : ℤ) (ts : List (ℤ × ℕ)) (σ : TVar → F) :
    (op c ts).eval σ = ((opZ c ts σ : ℤ) : F) := by
  simp only [op, opZ, LC.eval, List.map_map, Int.cast_add, Int.cast_list_sum, List.map_map]
  congr 2
  apply List.map_congr_left
  intro t _
  simp

/-- An operand limb as its constant and integer terms. -/
abbrev OpD := ℤ × List (ℤ × ℕ)

def OpD.lc (d : OpD) : LC := op d.1 d.2
def OpD.z (d : OpD) (σ : TVar → F) : ℤ := opZ d.1 d.2 σ
/-- Its least and greatest value over plug values `i` in `[0, bd i]`. -/
def OpD.lo (bd : ℕ → ℤ) (d : OpD) : ℤ := d.1 + (d.2.map fun t => min t.1 0 * bd t.2).sum
def OpD.hi (bd : ℕ → ℤ) (d : OpD) : ℤ := d.1 + (d.2.map fun t => max t.1 0 * bd t.2).sum

theorem opZ_mem (bd : ℕ → ℤ) (c : ℤ) (ts : List (ℤ × ℕ)) (σ : TVar → F)
    (hv : ∀ t ∈ ts, ((σ (.plug t.2)).val : ℤ) ≤ bd t.2) :
    OpD.lo bd (c, ts) ≤ OpD.z (c, ts) σ ∧ OpD.z (c, ts) σ ≤ OpD.hi bd (c, ts) := by
  simp only [OpD.lo, OpD.hi, OpD.z, opZ]
  induction ts generalizing c with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨k, i⟩ := t
    have h0 : (0 : ℤ) ≤ ((σ (.plug i)).val : ℤ) := Int.natCast_nonneg _
    have h1 : ((σ (.plug i)).val : ℤ) ≤ bd i := hv (k, i) (by simp)
    have := ih 0 fun t ht => hv t (by simp [ht])
    simp only [List.map_cons, List.sum_cons, zero_add] at this ⊢
    rcases le_total 0 k with hk | hk
    · rw [min_eq_right hk, max_eq_left hk]
      constructor <;> nlinarith
    · rw [min_eq_left hk, max_eq_right hk]
      constructor <;> nlinarith

/-- A certificate's variables seen from its caller's assignment. -/
def vw (d : ℕ → OpD) (o : ℕ) (σ : TVar → F) : TVar → F :=
  fun v => (view (fun m => (d m).lc) o v).eval σ

theorem vw_plug (d : ℕ → OpD) (o : ℕ) (σ : TVar → F) (m : ℕ) (hb : 0 ≤ (d m).z σ ∧ (d m).z σ < 2 ^ 68) :
    (((vw d o σ (.plug m)).val : ℕ) : ℤ) = (d m).z σ := by
  simp only [vw, view, OpD.lc, eval_op]
  exact MulCertK1.val_intCast hb.1 (lt_trans hb.2 (by norm_num))

/-- An entry among the first `n` (how `Assumptions` reads input `i`). -/
theorem getD_mem_take {l : List F} {n i : ℕ} (hi : i < n) (hl : i < l.length) :
    l.getD i 0 ∈ l.take n := by
  rw [List.getD_eq_getElem _ _ hl]
  exact List.mem_iff_getElem.2 ⟨i, by simp [hi, hl], by simp⟩

end Xark.Templates.EcK1Check
