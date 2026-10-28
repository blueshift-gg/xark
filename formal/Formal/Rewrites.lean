/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

set_option linter.style.header false

/-!
# Constraint-reducing rewrites preserve the circuit

The gadget theorems in this library are stated over the constraints a gadget
emits. The stable frontend (`crates/frontend`) emits *fewer* rows than the MIR
frontend for the same program; every saving is one of three rewrites, applied as
the row would be emitted:

* **Product reuse (CSE)** — `crates/frontend/src/builder.rs::emit_mul_var`. When
  `A · B = x` is already a row, a second `A · B` returns `x` instead of emitting
  `A · B = y` for a fresh `y`. (SHA-256: `Maj`'s `b ∧ c` is the previous round's
  `a ∧ b`; a 3-limb square's cross terms `xᵢ·xⱼ` appear twice.)
* **Inline sums** — `builder.rs::materialize`. The MIR frontend names a
  multiplication operand `L` of more than 8 terms with a fresh `t` and a row
  `L · 1 = t`; the stable frontend uses `L` in place.
* **Constant folding** — `host.rs` (`Intr::Pow`). `c ^ n` of a constant `c` is a
  constant, not the rows `c · c = t₁, …` (Poseidon's constant capacity lane).

(Reducing constants modulo `p` is not a rewrite at all: the rows are over
`ZMod p`, where `c` and `c mod p` are the same element.)

All three are instances of one fact, `elim_sound`: if the rows force a variable
`v` to equal a linear form `e` not involving `v`, then substituting `e` for `v`
yields rows whose solutions are **exactly** the original solutions with `v`
forgotten — no assignment is gained (soundness: nothing new to forge) and none
lost (completeness). So every property of a circuit's other wires — in particular
each gadget soundness theorem here, and the public-input relation the proof
system checks — is unchanged by the rewrite.
-/

namespace Xark.R1cs

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {F : Type*} [CommRing F] {V : Type*} [DecidableEq V]

/-- A linear combination `const + Σ cᵢ · xᵢ` (the `LinearCombination` of
`crates/ir/src/linear_combination.rs`). -/
structure LC (F V : Type*) where
  const : F
  terms : List (F × V)

namespace LC

/-- Value under an assignment. -/
def eval (l : LC F V) (σ : V → F) : F :=
  l.const + (l.terms.map fun t => t.1 * σ t.2).sum

/-- The single variable `x`. -/
def var (x : V) : LC F V := ⟨0, [(1, x)]⟩

/-- The constant `c`. -/
def cst (c : F) : LC F V := ⟨c, []⟩

/-- Total coefficient of `v`. -/
def coeff (l : LC F V) (v : V) : F :=
  ((l.terms.filter fun t => t.2 = v).map Prod.fst).sum

/-- Substitute `e` for `v`: drop `v`'s terms and add `coeff v · e`. -/
def subst (l : LC F V) (v : V) (e : LC F V) : LC F V :=
  ⟨l.const + l.coeff v * e.const,
    l.terms.filter (fun t => t.2 ≠ v) ++ e.terms.map fun t => (l.coeff v * t.1, t.2)⟩

/-- `l` does not depend on `v`. -/
def Indep (l : LC F V) (v : V) : Prop :=
  ∀ σ x, l.eval (Function.update σ v x) = l.eval σ

@[simp] theorem eval_var (x : V) (σ : V → F) : (var x : LC F V).eval σ = σ x := by
  simp [eval, var]

@[simp] theorem eval_cst (c : F) (σ : V → F) : (cst c : LC F V).eval σ = c := by
  simp [eval, cst]

theorem cst_indep (c : F) (v : V) : (cst c : LC F V).Indep v := by
  intro σ x; simp

theorem var_indep {x v : V} (h : x ≠ v) : (var x : LC F V).Indep v := by
  intro σ y; simp [Function.update_of_ne h]

/-- Splitting a term list into the `v` terms and the rest. -/
private theorem sum_split (ts : List (F × V)) (v : V) (σ : V → F) :
    (ts.map fun t => t.1 * σ t.2).sum =
      ((ts.filter fun t => t.2 ≠ v).map fun t => t.1 * σ t.2).sum +
        ((ts.filter fun t => t.2 = v).map Prod.fst).sum * σ v := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    by_cases h : t.2 = v
    · simp [h, ih, List.filter_cons, add_mul]; ring
    · simp [h, ih, List.filter_cons]; ring

/-- The `v`-free part of the sum ignores `σ v`. -/
private theorem sum_filter_update (ts : List (F × V)) (v : V) (σ : V → F) (x : F) :
    ((ts.filter fun t => t.2 ≠ v).map fun t => t.1 * Function.update σ v x t.2).sum =
      ((ts.filter fun t => t.2 ≠ v).map fun t => t.1 * σ t.2).sum := by
  congr 1
  apply List.map_congr_left
  intro t ht
  have : t.2 ≠ v := by simpa using (List.mem_filter.mp ht).2
  rw [Function.update_of_ne this]

private theorem sum_scaled (ts : List (F × V)) (k : F) (σ : V → F) :
    ((ts.map fun t => (k * t.1, t.2)).map fun t => t.1 * σ t.2).sum =
      k * (ts.map fun t => t.1 * σ t.2).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **Substitution is evaluation at the updated assignment.** -/
theorem eval_subst (l : LC F V) (v : V) (e : LC F V) (σ : V → F) :
    (l.subst v e).eval σ = l.eval (Function.update σ v (e.eval σ)) := by
  simp only [eval, subst, List.map_append, List.sum_append, sum_scaled]
  rw [sum_split l.terms v (Function.update σ v _), sum_filter_update]
  simp [coeff]; ring

/-- A substituted form no longer depends on `v` (when `e` doesn't). -/
theorem subst_indep (l : LC F V) {v : V} {e : LC F V} (he : e.Indep v) :
    (l.subst v e).Indep v := by
  intro σ x
  rw [eval_subst, eval_subst, he, Function.update_idem]

end LC

/-- A row `a · b = c`. -/
structure Row (F V : Type*) where
  a : LC F V
  b : LC F V
  c : LC F V

namespace Row

def Sat (r : Row F V) (σ : V → F) : Prop := r.a.eval σ * r.b.eval σ = r.c.eval σ

def subst (r : Row F V) (v : V) (e : LC F V) : Row F V :=
  ⟨r.a.subst v e, r.b.subst v e, r.c.subst v e⟩

theorem sat_subst (r : Row F V) (v : V) (e : LC F V) (σ : V → F) :
    (r.subst v e).Sat σ ↔ r.Sat (Function.update σ v (e.eval σ)) := by
  simp [Sat, subst, LC.eval_subst]

/-- `A · B = x`. -/
def mul (A B : LC F V) (x : V) : Row F V := ⟨A, B, LC.var x⟩

end Row

/-- A constraint system: all rows hold. -/
def Sat (S : List (Row F V)) (σ : V → F) : Prop := ∀ r ∈ S, r.Sat σ

def subst (S : List (Row F V)) (v : V) (e : LC F V) : List (Row F V) :=
  S.map fun r => r.subst v e

theorem sat_subst (S : List (Row F V)) (v : V) (e : LC F V) (σ : V → F) :
    Sat (subst S v e) σ ↔ Sat S (Function.update σ v (e.eval σ)) := by
  simp [Sat, subst, Row.sat_subst]

/-- **Variable elimination is exact.** If every solution of `S` has `v = e` (with
`e` not depending on `v`), then the solutions of `S[v := e]` are exactly the
solutions of `S` with `v` forgotten: `τ` solves the rewritten rows iff some value
of `v` extends it to a solution of the original rows. -/
theorem elim_sound (S : List (Row F V)) (v : V) (e : LC F V) (he : e.Indep v)
    (hforce : ∀ σ, Sat S σ → σ v = e.eval σ) (τ : V → F) :
    Sat (subst S v e) τ ↔ ∃ x, Sat S (Function.update τ v x) := by
  rw [sat_subst]
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨x, hx⟩
    have hv := hforce _ hx
    rw [Function.update_self, he] at hv
    rwa [← hv]

/-- Dropping a row that the rest already implies changes nothing. -/
theorem sat_drop (S : List (Row F V)) (r : Row F V) (h : ∀ σ, Sat S σ → r.Sat σ)
    (σ : V → F) : Sat (r :: S) σ ↔ Sat S σ := by
  constructor
  · intro hs r' hr'; exact hs r' (List.mem_cons_of_mem _ hr')
  · intro hs r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact h σ hs
    · exact hs r' hr'

/-! ### The three rewrites -/

/-- **Product reuse (CSE).** With `A · B = x` among the rows, emitting a second
`A · B = y` (fresh `y`) and then using `y` — the MIR lowering — has the same
solutions, `y` forgotten, as using `x` directly — the stable lowering, which is
the rows with `y := x`, the duplicate `A · B = x` dropped. -/
theorem cse_sound (S : List (Row F V)) (A B : LC F V) (x y : V) (hxy : x ≠ y)
    (hmem : Row.mul A B x ∈ S) (τ : V → F) :
    Sat (subst S y (LC.var x)) τ ↔
      ∃ t, Sat (Row.mul A B y :: S) (Function.update τ y t) := by
  have hrw : subst (Row.mul A B y :: S) y (LC.var x) =
      (Row.mul A B y).subst y (LC.var x) :: subst S y (LC.var x) := rfl
  rw [← elim_sound _ y (LC.var x) (LC.var_indep hxy), hrw, sat_drop]
  · intro σ hσ
    have hx := hσ _ (List.mem_map_of_mem hmem)
    rw [Row.sat_subst] at hx ⊢
    simpa [Row.Sat, Row.mul, Function.update_of_ne hxy] using hx
  · intro σ hσ
    have h1 := hσ _ (List.mem_cons_self ..)
    have h2 := hσ _ (List.mem_cons_of_mem _ hmem)
    simp only [Row.Sat, Row.mul, LC.eval_var] at h1 h2
    rw [LC.eval_var, ← h1, h2]

/-- **Inline sums.** Naming an operand `L` as `t` with the row `L · 1 = t` — the MIR
lowering — has the same solutions, `t` forgotten, as using `L` in place — the
stable lowering, `S[t := L]` (the defining row becomes `L · 1 = L` and goes). -/
theorem inline_sound (S : List (Row F V)) (L : LC F V) (t : V) (hL : L.Indep t)
    (τ : V → F) :
    Sat (subst S t L) τ ↔ ∃ x, Sat (⟨L, LC.cst 1, LC.var t⟩ :: S) (Function.update τ t x) := by
  have hrw : subst (⟨L, LC.cst 1, LC.var t⟩ :: S) t L =
      Row.subst ⟨L, LC.cst 1, LC.var t⟩ t L :: subst S t L := rfl
  rw [← elim_sound _ t L hL, hrw, sat_drop]
  · intro σ _
    rw [Row.sat_subst]
    simp [Row.Sat, hL σ]
  · intro σ hσ
    have h := hσ _ (List.mem_cons_self ..)
    simp only [Row.Sat, LC.eval_cst, mul_one, LC.eval_var] at h
    exact h.symm

/-- **Folding a linear product.** A row `A · B = t` whose product is (as a function)
the linear form `e` — one operand constant, or the defining row `L · 1 = t` of a
named sum — can be dropped with `e` used in place of `t`. (Covers `mul` of an
operand that is constant *in the field*: reducing coefficients mod `p` can turn
`p·x + c` into the literal constant `c`, which the frontend then folds.) -/
theorem fold_sound (S : List (Row F V)) (A B e : LC F V) (t : V) (he : e.Indep t)
    (hlin : ∀ σ, A.eval σ * B.eval σ = e.eval σ) (τ : V → F) :
    Sat (subst S t e) τ ↔ ∃ x, Sat (⟨A, B, LC.var t⟩ :: S) (Function.update τ t x) := by
  have hrw : subst (⟨A, B, LC.var t⟩ :: S) t e =
      Row.subst ⟨A, B, LC.var t⟩ t e :: subst S t e := rfl
  rw [← elim_sound _ t e he, hrw, sat_drop]
  · intro σ _
    rw [Row.sat_subst]
    simp [Row.Sat, hlin, he σ]
  · intro σ hσ
    have h := hσ _ (List.mem_cons_self ..)
    simp only [Row.Sat, LC.eval_var] at h
    rw [← h, hlin]

/-- **Constant folding.** A product row `a · b = t` of two constants — the MIR
lowering of `c ^ n` emits a chain of them — has the same solutions, `t` forgotten,
as the constant `a · b` in place of `t`. -/
theorem const_mul_sound (S : List (Row F V)) (a b : F) (t : V) (τ : V → F) :
    Sat (subst S t (LC.cst (a * b))) τ ↔
      ∃ x, Sat (Row.mul (LC.cst a) (LC.cst b) t :: S) (Function.update τ t x) := by
  have hrw : subst (Row.mul (LC.cst a) (LC.cst b) t :: S) t (LC.cst (a * b)) =
      Row.subst (Row.mul (LC.cst a) (LC.cst b) t) t (LC.cst (a * b)) ::
        subst S t (LC.cst (a * b)) := rfl
  rw [← elim_sound _ t _ (LC.cst_indep _ _), hrw, sat_drop]
  · intro σ _
    rw [Row.sat_subst]
    simp [Row.Sat, Row.mul]
  · intro σ hσ
    have h := hσ _ (List.mem_cons_self ..)
    simp only [Row.Sat, Row.mul, LC.eval_cst, LC.eval_var] at h
    rw [LC.eval_cst, h]

/-! ## Branch guards

A witness branch runs both arms. A `require` (`assert!`, `require_eq`, the
equalities of an integer division) inside an arm is emitted as the row
`G · D = 0`, where `G` is the arm's guard — the `{0,1}` conjunction of the
enclosing arms' conditions (`crates/frontend/src/host.rs::require_gated`) — and
the arm's values reach the rest of the circuit only through the select
`e + c · (t − e)` on the branch condition (`interp.rs::merge`). Then the row is
the requirement exactly where the arm is taken, and nothing where it isn't
(`gated_sat`); guards of nested arms are products (`guard_mul`); an untaken
arm's hints are pinned to `0` (`pin_dead`); and an untaken arm's values never
matter (`select_taken`). -/

/-- A guarded row `G · D = 0` holds iff `D = 0` wherever `G = 1`. -/
theorem gated_sat (G D : LC F V) (σ : V → F) (hG : G.eval σ = 0 ∨ G.eval σ = 1) :
    (⟨G, D, LC.cst 0⟩ : Row F V).Sat σ ↔ (G.eval σ = 1 → D.eval σ = 0) := by
  have h0 : (LC.cst 0 : LC F V).eval σ = 0 := by simp [LC.eval, LC.cst]
  simp only [Row.Sat, h0]
  rcases hG with h | h
  · refine ⟨fun _ h1 => ?_, fun _ => by rw [h, zero_mul]⟩
    rw [← one_mul (D.eval σ), ← h1, h, zero_mul]
  · rw [h, one_mul]
    exact ⟨fun hd _ => hd, fun hd => hd rfl⟩

/-- A nested arm's guard: the product of `{0,1}` values is `1` iff both are. -/
theorem guard_mul (g c : F) (hg : g = 0 ∨ g = 1) (hc : c = 0 ∨ c = 1) :
    (g * c = 0 ∨ g * c = 1) ∧ (g * c = 1 ↔ g = 1 ∧ c = 1) := by
  rcases hg with rfl | rfl <;> rcases hc with rfl | rfl <;> simp

/-- An arm's hints read `g · x` and are pinned by `(1 − g) · h = 0`
(`builder.rs::gate_input`, `pin_dead`): where the arm is taken the hint sees `x`
and the pin is vacuous; where it isn't, the hint sees `0` and `h` is forced to `0`
— so every variable stays determined by the inputs. -/
theorem pin_dead (g x h : F) (hg : g = 0 ∨ g = 1) :
    (g = 1 → g * x = x ∧ ((1 - g) * h = 0 ↔ True)) ∧
      (g = 0 → g * x = 0 ∧ ((1 - g) * h = 0 ↔ h = 0)) := by
  -- (`0 = 1` only in the trivial ring, where every element is `0`.)
  have triv : (0 : F) = 1 → ∀ a : F, a = 0 := fun e a => by
    rw [← mul_one a, ← e, mul_zero]
  rcases hg with rfl | rfl
  · refine ⟨fun e => ?_, fun _ => ⟨zero_mul x, ?_⟩⟩
    · exact ⟨by rw [triv e (0 * x), triv e x], fun _ => trivial,
        fun _ => triv e ((1 - 0) * h)⟩
    · rw [sub_zero, one_mul]
  · refine ⟨fun _ => ⟨one_mul x, fun _ => trivial, fun _ => by rw [sub_self, zero_mul]⟩,
      fun e => ?_⟩
    exact ⟨triv e.symm (1 * x), fun _ => triv e.symm h, fun _ => triv e.symm _⟩

/-- The merge's select returns the taken arm's value, whatever the other's. -/
theorem select_taken (t e : F) : e + 1 * (t - e) = t := by ring

theorem select_untaken (t e : F) : e + 0 * (t - e) = e := by ring

end Xark.R1cs
