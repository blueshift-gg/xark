/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Template

set_option linter.style.header false
set_option linter.dupNamespace false

/-!
# The solver's assignment, as a computable reference for soundness

`Template.solve` runs a template's hints in order from plug values, as the solver
(`crates/ir/src/solver.rs`) does. `Formal/AesSbox.lean`'s soundness uses it as a
reference assignment: its product rows pin every product to a function of the plugs, so
any satisfying assignment agrees with `solve` on them, and `decide +kernel` evaluates
`solve` on each of the 256 inputs. When every hint writes one variable above the earlier
writes and reads only plugs and earlier variables (`ordered`, checked by `decide`), each
hint's equation holds at `solve` (`Template.solve_hint`) and the plugs are kept
(`Template.solve_plug`).

`obligation thm` is what a soundness theorem `∀ σ, H₁ σ → … → Hₙ σ → C σ` holds
vacuously without: `∃ σ, H₁ σ ∧ … ∧ Hₙ σ`. Each harness's `satisfiable`
(`Formal/Templates/Witness/*.lean`, written by `cargo xtask lean-export --witnesses`)
proves it with an `assign` of plug values a production call passed and the witness
the solver computed from them, which `decide +kernel` checks row by row; the values
come from Rust, so the kernel checks them and trusts nothing that computed them.
-/

namespace Xark.Template

open Xark.R1cs

/-- What the solver (`crates/ir/src/solver.rs`) assigns for one hint. -/
def Hint.run (σ : TVar → F) : Hint → TVar → F
  | .product o a b => Function.update σ (.wit o) (a.eval σ * b.eval σ)
  | .linear o a => Function.update σ (.wit o) (a.eval σ)
  | .xor o a b => Function.update σ (.wit o) (a.eval σ + b.eval σ - 2 * a.eval σ * b.eval σ)
  | .or o a b => Function.update σ (.wit o) (a.eval σ + b.eval σ - a.eval σ * b.eval σ)
  | .inverse o x | .inverseOrZero o x => Function.update σ (.wit o) (x.eval σ)⁻¹
  | .bit o x i => Function.update σ (.wit o) (bitOf (x.eval σ) i)
  | .bits os x =>
    os.zipIdx.foldl (fun τ (o, i) => Function.update τ (.wit o) (bitOf (x.eval σ) i)) σ
  | .divRem q m n d =>
    Function.update (Function.update σ (.wit q) ((n.eval σ).val / (d.eval σ).val : ℕ))
      (.wit m) ((n.eval σ).val % (d.eval σ).val : ℕ)

/-- Plug values `x`, before any hint has run. -/
def init (x : ℕ → F) : TVar → F
  | .plug i => x i
  | .wit _ => 0

/-- The solver's assignment for plug values `x`: its hints run in order. -/
def Template.solve (t : Template) (x : ℕ → F) : TVar → F := t.hints.foldl Hint.run (init x)

theorem eval_congr {l : LC} {σ τ : TVar → F} (h : ∀ t ∈ l.terms, σ t.2 = τ t.2) :
    l.eval σ = l.eval τ := by
  unfold Xark.R1cs.LC.eval
  rw [List.map_congr_left fun t ht => by rw [h t ht]]

/-- The variable a single-output hint writes. -/
def Hint.out? : Hint → Option ℕ
  | .product o _ _ | .linear o _ | .xor o _ _ | .or o _ _ | .inverse o _
  | .inverseOrZero o _ | .bit o _ _ => some o
  | .bits _ _ | .divRem _ _ _ _ => none

/-- The variables a hint's linear combinations read. -/
def Hint.reads : Hint → List TVar
  | .product _ a b | .xor _ a b | .or _ a b => a.terms.map (·.2) ++ b.terms.map (·.2)
  | .linear _ a | .inverse _ a | .inverseOrZero _ a | .bit _ a _ | .bits _ a =>
    a.terms.map (·.2)
  | .divRem _ _ a b => a.terms.map (·.2) ++ b.terms.map (·.2)

/-- The value a single-output hint writes, under `σ`. -/
def Hint.value (σ : TVar → F) : Hint → F
  | .product _ a b => a.eval σ * b.eval σ
  | .linear _ a => a.eval σ
  | .xor _ a b => a.eval σ + b.eval σ - 2 * a.eval σ * b.eval σ
  | .or _ a b => a.eval σ + b.eval σ - a.eval σ * b.eval σ
  | .inverse _ a | .inverseOrZero _ a => (a.eval σ)⁻¹
  | .bit _ a i => bitOf (a.eval σ) i
  | .bits _ _ | .divRem _ _ _ _ => 0

/-- `v` is a plug or a variable below `m`. -/
def below (m : ℕ) : TVar → Bool
  | .plug _ => true
  | .wit k => decide (k < m)

/-- Every hint is single-output, writes a variable at or above `m` and above every
earlier write, and reads only plugs and variables below what it writes. -/
def ordered : ℕ → List Hint → Bool
  | _, [] => true
  | m, h :: hs =>
    match h.out? with
    | none => false
    | some o => decide (m ≤ o) && h.reads.all (below o) && ordered (o + 1) hs

theorem eval_congr_reads (l : LC) {σ τ : TVar → F} (h : ∀ v ∈ l.terms.map (·.2), σ v = τ v) :
    l.eval σ = l.eval τ := by
  obtain ⟨c, ts⟩ := l
  simp only [LC.eval]
  congr 2
  refine List.map_congr_left fun t ht => ?_
  rw [h t.2 (List.mem_map.mpr ⟨t, ht, rfl⟩)]

theorem value_congr (h : Hint) {σ τ : TVar → F} (hr : ∀ v ∈ h.reads, σ v = τ v) :
    h.value σ = h.value τ := by
  cases h <;> simp only [Hint.reads, List.mem_append] at hr <;> simp only [Hint.value] <;>
    first
    | rfl
    | rw [eval_congr_reads _ fun v hv => hr v hv]
    | rw [eval_congr_reads _ fun v hv => hr v (Or.inl hv),
        eval_congr_reads _ fun v hv => hr v (Or.inr hv)]

theorem run_eq (h : Hint) {o : ℕ} (ho : h.out? = some o) (σ : TVar → F) :
    h.run σ = Function.update σ (.wit o) (h.value σ) := by
  cases h <;> simp only [Hint.out?, Option.some.injEq, reduceCtorEq] at ho <;> subst ho <;> rfl

/-- Running ordered hints from `m` leaves every plug and every variable below `m`. -/
theorem foldl_below : ∀ (hs : List Hint) (m : ℕ) (τ : TVar → F), ordered m hs = true →
    ∀ v, below m v = true → hs.foldl Hint.run τ v = τ v
  | [], _, _, _, _, _ => rfl
  | h :: hs, m, τ, hord, v, hv => by
    simp only [ordered] at hord
    split at hord
    · exact absurd hord (by simp)
    · rename_i o ho
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hord
      obtain ⟨⟨hm, -⟩, hord⟩ := hord
      rw [List.foldl_cons, foldl_below hs (o + 1) _ hord v ?_, run_eq h ho]
      · rw [Function.update_of_ne]
        rintro rfl
        simp [below] at hv
        omega
      · cases v <;> simp_all [below]
        omega

/-- **The solver's assignment satisfies each hint.** -/
theorem solve_hint : ∀ (hs : List Hint) (m : ℕ) (τ : TVar → F), ordered m hs = true →
    ∀ h ∈ hs, ∃ o, h.out? = some o ∧
      hs.foldl Hint.run τ (.wit o) = h.value (hs.foldl Hint.run τ)
  | [], _, _, _, _, hh => absurd hh (List.not_mem_nil)
  | h :: hs, m, τ, hord, h', hh => by
    have hord' := hord
    simp only [ordered] at hord
    split at hord
    · exact absurd hord (by simp)
    · rename_i o ho
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hord
      obtain ⟨⟨-, hr⟩, hord⟩ := hord
      rcases List.mem_cons.mp hh with rfl | hh
      · refine ⟨o, ho, ?_⟩
        have hb : ∀ v, below (o + 1) v = true →
            (h' :: hs).foldl Hint.run τ v = h'.run τ v := fun v hv => by
          rw [List.foldl_cons]; exact foldl_below hs (o + 1) _ hord v hv
        rw [hb _ (by simp [below]), run_eq h' ho, Function.update_self]
        refine value_congr h' fun v hv => ?_
        rw [hb v ?_, run_eq h' ho, Function.update_of_ne]
        · rintro rfl; have := hr _ hv; simp [below] at this
        · have := hr _ hv
          cases v <;> simp_all [below]
          omega
      · rw [List.foldl_cons]
        exact solve_hint hs (o + 1) _ hord h' hh

namespace Template

/-- The solver's assignment keeps the plug values. -/
theorem solve_plug (t : Template) (x : ℕ → F) (h : ordered 0 t.hints = true) (i : ℕ) :
    t.solve x (.plug i) = x i := by
  rw [solve, foldl_below _ 0 _ h _ rfl]; rfl

/-- Each hint's equation holds at the solver's assignment. -/
theorem solve_hint (t : Template) (x : ℕ → F) (h : ordered 0 t.hints = true) :
    ∀ hi ∈ t.hints, ∃ o, hi.out? = some o ∧ t.solve x (.wit o) = hi.value (t.solve x) :=
  Xark.Template.solve_hint _ 0 _ h

end Template

/-! ### A witness of a soundness theorem's hypotheses -/

/-- The assignment with plug values `p` and witness values `w`, in chunks of `n`. A
lookup in one flat list takes `j` kernel steps, each cached for the whole proof: a
3567-witness template took more than 12 GB. In chunks of 64 it takes about
`j / 64 + 64` and stays under 4 GB. `n` is an argument, not the first chunk's length,
so that it is a numeral the kernel divides by natively: `List.length` of a literal is
not, and `Nat.div` by it unfolds well-founded recursion. -/
def assign (p : List F) (n : ℕ) (w : List (List F)) : TVar → F
  | .plug i => p.getD i 0
  | .wit j => (w.getD (j / n) []).getD (j % n) 0

/-- `∀ v ∈ l, p v` over field elements, decided by walking `l`. Without it `decide`
finds Mathlib's `Fintype.decidableForallFintype` first (`ZMod r` is finite), which
enumerates all `r` elements: `decide +kernel` on an `Assumptions` never ends. Scoped:
it changes instance selection only where `Xark.Template` is open. -/
scoped instance (priority := high) decidableBAllF (l : List F) (p : F → Prop) [DecidablePred p] :
    Decidable (∀ v ∈ l, p v) :=
  List.decidableBAll p l

scoped instance (t : Template) (σ : TVar → F) : Decidable (t.Sat σ) :=
  inferInstanceAs (Decidable (∀ r ∈ t.rows, r.a.eval σ * r.b.eval σ = r.c.eval σ))

open Lean Meta Elab Term in
/-- `∃ σ, H₁ σ ∧ … ∧ Hₙ σ` for `thm : ∀ σ, H₁ σ → … → Hₙ σ → C σ`, with the
definitions of `Xark.Templates` other than the templates unfolded (`Assumptions`,
`IsBit`), so that `decide` evaluates it at a concrete `σ`. -/
def obligation (thm : Name) : MetaM Expr := do
  forallTelescope (← getConstInfo thm).type fun xs _ => do
    let some σ := xs[0]? | throwError "{thm} has no assignment"
    unless ← isDefEq (← inferType σ) (← mkArrow (mkConst ``TVar) (mkConst ``F)) do
      throwError "{thm}'s first binder isn't an assignment `TVar → F`"
    let hs ← xs[1:].toArray.mapM inferType
    for h in hs do
      unless ← isProp h do throwError "{thm} has a binder after `σ` that isn't a hypothesis"
    let body ← deltaExpand (mkAndN hs.toList) fun n =>
      (`Xark.Templates).isPrefixOf n && n.getString! != "template"
    mkAppM ``Exists #[← mkLambdaFVars #[σ] body]

open Lean Elab Term in
/-- `obligation% soundness`: the proposition `obligation` builds. -/
elab "obligation% " thm:ident : term => do
  obligation (← realizeGlobalConstNoOverloadWithInfo thm)

end Xark.Template
