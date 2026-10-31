/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib
import Formal.Rewrites
import Formal.GrumpkinGroup
import Formal.Minimize.Check

set_option linter.style.header false

/-!
# The certified minimizer: what the checker's acceptance means

`Formal/Minimize/Check.lean`'s `check` accepts a certificate of one minimizer run.
Read over `ZMod r` as `Xark.R1cs` rows (`Formal/Rewrites.lean`), acceptance means:

* `check_sound`: every solution `τ` of the minimized rows extends to a solution of the
  original rows, `recompute P τ`, which changes only the eliminated variables, giving each
  its defining form (`elim_sound`'s substitution, replayed from the last step back);
* `check_complete`: every solution `σ` of the original rows solves the minimized rows,
  and `recompute P σ = σ`: the eliminated variables are functions of the survivors;
* `check_internal`: every eliminated variable is listed `Internal` (never a public or
  private input), and `check_inputs`: the output keeps every other variable with its
  visibility.

The proof: each step's equation `v k = e k` holds at `recompute P τ`, and (forward, step
by step from the defining rows) at every original solution. Where they hold, an original
row and the row it ended as, `O + Σ m · (e j - v j)`, agree, which reduces every claim
to the checker's per-row checks.
-/

namespace Xark.Minimize

open Xark.R1cs

variable {p : ℕ}

/-- A checker form over `ZMod p`. -/
def Lc.toLC (p : ℕ) (l : Lc) : LC (ZMod p) ℕ := ⟨l.k, l.t.map fun a => ((a.1 : ZMod p), a.2)⟩

/-- A checker row over `ZMod p`. -/
def Row.toRow (p : ℕ) (r : Row) : R1cs.Row (ZMod p) ℕ := ⟨r.a.toLC p, r.b.toLC p, r.c.toLC p⟩

/-- The original rows: the steps' defining rows and the rest. -/
def orig (p : ℕ) (P : Problem) : List (R1cs.Row (ZMod p) ℕ) :=
  P.steps.toList.map (·.src.row.toRow p) ++ P.recs.toList.map (·.1.row.toRow p)

/-- The minimized row a fate names. -/
def Fate.out : Fate → Option Row
  | .kept M => some M
  | .dropped => none

/-- The minimized rows: the kept rows' `M`s, in order. -/
def keyed (p : ℕ) (P : Problem) : List (R1cs.Row (ZMod p) ℕ) :=
  P.recs.toList.filterMap fun r => r.2.out.map (·.toRow p)

/-- Give each eliminated variable its defining form, from the last step back. -/
def recompute (p : ℕ) (P : Problem) (τ : ℕ → ZMod p) : ℕ → ZMod p :=
  P.steps.toList.foldr (fun s σ => Function.update σ s.v ((s.e.toLC p).eval σ)) τ

/-! ### Forms -/

/-- The value of terms. -/
def tsum (p : ℕ) (t : List (ℕ × ℕ)) (σ : ℕ → ZMod p) : ZMod p :=
  (t.map fun a => (a.1 : ZMod p) * σ a.2).sum

@[simp] theorem tsum_nil (σ : ℕ → ZMod p) : tsum p [] σ = 0 := rfl

@[simp] theorem tsum_cons (a : ℕ × ℕ) (t) (σ : ℕ → ZMod p) :
    tsum p (a :: t) σ = a.1 * σ a.2 + tsum p t σ := by simp [tsum]

@[simp] theorem tsum_append (t u) (σ : ℕ → ZMod p) :
    tsum p (t ++ u) σ = tsum p t σ + tsum p u σ := by simp [tsum]

/-- `neg` is negation. -/
theorem neg_natCast [NeZero p] (m : ℕ) : ((neg p m : ℕ) : ZMod p) = -(m : ZMod p) := by
  have hlt : m % p ≤ p := (Nat.mod_lt _ (NeZero.pos p)).le
  rw [neg, Nat.cast_sub hlt, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

theorem tsum_map_neg [NeZero p] (t : List (ℕ × ℕ)) (σ : ℕ → ZMod p) :
    tsum p (t.map fun a => (neg p a.1, a.2)) σ = -tsum p t σ := by
  induction t with
  | nil => simp
  | cons a t ih => simp [ih, neg_natCast]; ring

theorem tsum_map_mul (m : ℕ) (t : List (ℕ × ℕ)) (σ : ℕ → ZMod p) :
    tsum p (t.map fun a => (m * a.1, a.2)) σ = m * tsum p t σ := by
  induction t with
  | nil => simp
  | cons a t ih => simp [ih]; ring

theorem eval_toLC (l : Lc) (σ : ℕ → ZMod p) : (l.toLC p).eval σ = l.k + tsum p l.t σ := by
  simp [Lc.toLC, LC.eval, tsum, Function.comp_def]

theorem tsum_combine (acc t : List (ℕ × ℕ)) (σ : ℕ → ZMod p) :
    tsum p (combine p acc t) σ = tsum p acc σ + tsum p t σ := by
  induction t generalizing acc with
  | nil => cases acc <;> simp [combine]
  | cons a t ih =>
    rcases acc with _ | ⟨⟨c, x⟩, acc⟩
    · simp [combine, ih]
    · obtain ⟨d, y⟩ := a
      by_cases h : x = y
      · subst h; simp [combine, ih, ZMod.natCast_mod]; ring
      · simp [combine, h, ih]; ring

theorem tsum_norm (t : List (ℕ × ℕ)) (σ : ℕ → ZMod p) : tsum p (norm p t) σ = tsum p t σ := by
  rw [norm, tsum_combine, tsum_nil, zero_add]
  exact ((List.mergeSort_perm t _).map _).sum_eq

theorem tsum_eq_zero (t : List (ℕ × ℕ)) (σ : ℕ → ZMod p) (h : t.all fun a => a.1 % p == 0) :
    tsum p t σ = 0 := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have : (a.1 : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero h.1
    simp [this, ih h.2]

theorem eval_of_isConst {l : Lc} (h : isConst p l) (σ : ℕ → ZMod p) :
    (l.toLC p).eval σ = l.k := by
  rw [eval_toLC, ← tsum_norm, tsum_eq_zero _ _ h, add_zero]

theorem eval_of_isZero {l : Lc} (h : isZero p l) (σ : ℕ → ZMod p) : (l.toLC p).eval σ = 0 := by
  simp only [isZero, Bool.and_eq_true, beq_iff_eq] at h
  rw [eval_of_isConst h.2, ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero h.1

theorem eval_sub [NeZero p] (x y : Lc) (σ : ℕ → ZMod p) :
    ((sub p x y).toLC p).eval σ = (x.toLC p).eval σ - (y.toLC p).eval σ := by
  simp only [eval_toLC, sub, tsum_append, tsum_map_neg, Nat.cast_add, neg_natCast]; ring

theorem eval_scale (m : ℕ) (l : Lc) (σ : ℕ → ZMod p) :
    ((scale m l).toLC p).eval σ = m * (l.toLC p).eval σ := by
  simp only [eval_toLC, scale, tsum_map_mul, Nat.cast_mul]; ring

theorem sat_iff_of_rel [NeZero p] {R : Row} {d : Lc} (h : rel p R = some d) (σ : ℕ → ZMod p) :
    (R.toRow p).Sat σ ↔ (d.toLC p).eval σ = 0 := by
  simp only [R1cs.Row.Sat, Row.toRow]
  unfold rel at h
  split_ifs at h with ha hb <;> cases h
  · rw [eval_sub, eval_scale, eval_of_isConst ha, sub_eq_zero]
  · rw [eval_sub, eval_scale, eval_of_isConst hb, sub_eq_zero, mul_comm]

theorem tsum_congr (t : List (ℕ × ℕ)) {σ σ' : ℕ → ZMod p} (h : ∀ a ∈ t, σ a.2 = σ' a.2) :
    tsum p t σ = tsum p t σ' := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    simp only [tsum_cons]
    rw [h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- A form ignores a variable it doesn't name. -/
theorem eval_congr (l : Lc) {σ σ' : ℕ → ZMod p} (h : ∀ a ∈ l.t, σ a.2 = σ' a.2) :
    (l.toLC p).eval σ = (l.toLC p).eval σ' := by
  rw [eval_toLC, eval_toLC, tsum_congr _ h]

/-! ### The steps' equations -/

/-- The equations of the steps before `bound` hold at `σ`. -/
def Holds (p : ℕ) (P : Problem) (bound : ℕ) (σ : ℕ → ZMod p) : Prop :=
  ∀ j < bound, ∀ s, P.steps[j]? = some s → σ s.v = (s.e.toLC p).eval σ

/-- Where the equations hold, adding multiples of them changes no value. -/
theorem eval_apply [NeZero p] {P : Problem} {bound : ℕ} {σ : ℕ → ZMod p}
    (hσ : Holds p P bound σ) : ∀ (ms : List (ℕ × ℕ)) (l l' : Lc),
    apply p P.steps bound l ms = some l' → (l'.toLC p).eval σ = (l.toLC p).eval σ
  | [], l, l', h => by cases h; rfl
  | (j, m) :: ms, l, l', h => by
    unfold apply at h
    split_ifs at h with hj
    split at h
    · next s hs =>
      rw [eval_apply hσ ms _ _ h, eval_toLC, eval_toLC]
      have := hσ j hj s hs
      rw [eval_toLC] at this
      simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, tsum_cons, tsum_append,
        tsum_map_mul, neg_natCast, this]
      ring
    · cases h

theorem sat_certRow [NeZero p] {P : Problem} {bound : ℕ} {σ : ℕ → ZMod p}
    (hσ : Holds p P bound σ) {o : Orig} {R : Row} (h : certRow p P.steps bound o = some R) :
    (R.toRow p).Sat σ ↔ (o.row.toRow p).Sat σ := by
  simp only [certRow, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h
  simp only [R1cs.Row.Sat, Row.toRow, eval_apply hσ _ _ _ ha, eval_apply hσ _ _ _ hb,
    eval_apply hσ _ _ _ hc]

/-! ### Reading the checks -/

theorem mem_of_find {α : Type} {key : α → ℕ} {xs : Array α} {x : ℕ} {a : α}
    (h : find key xs x = some a) : a ∈ xs := by
  simp only [find, Option.bind_eq_some_iff] at h
  obtain ⟨i, -, hi⟩ := h
  exact Array.mem_of_getElem? hi

theorem entry_spec {vars : Array Var} {x : ℕ} {e : Var} (h : entry vars x = some e) :
    e ∈ vars ∧ e.id = x := by
  unfold entry at h
  split at h
  · next a ha =>
    split_ifs at h with hx
    cases h
    exact ⟨mem_of_find ha, by simpa using hx⟩
  · cases h

/-! ### Replaying the steps backwards -/

/-- The replay order is well founded: no step's form names its own or an earlier
step's variable, and no two steps share a variable. -/
def Good : List Step → Prop
  | [] => True
  | s :: L => (∀ t ∈ s :: L, ∀ a ∈ t.e.t, a.2 ≠ s.v) ∧ (∀ t ∈ L, t.v ≠ s.v) ∧ Good L

/-- Replaying a well-founded list gives every step its equation. -/
theorem foldr_holds (τ : ℕ → ZMod p) : ∀ L : List Step, Good L → ∀ t ∈ L,
    L.foldr (fun s σ => Function.update σ s.v ((s.e.toLC p).eval σ)) τ t.v =
      (t.e.toLC p).eval (L.foldr (fun s σ => Function.update σ s.v ((s.e.toLC p).eval σ)) τ)
  | [], _, t, ht => by cases ht
  | s :: L, ⟨he, hv, hg⟩, t, ht => by
    simp only [List.foldr_cons]
    set σ := L.foldr (fun s σ => Function.update σ s.v ((s.e.toLC p).eval σ)) τ
    rw [eval_congr t.e (σ' := σ) fun a ha => Function.update_of_ne (he t ht a ha) _ _]
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [Function.update_self]
    · rw [Function.update_of_ne (hv t ht)]
      exact foldr_holds τ L hg t ht

theorem good_of_getElem : ∀ L : List Step,
    (∀ i j (hi : i < L.length) (hj : j < L.length), i ≤ j → ∀ a ∈ L[j].e.t, a.2 ≠ L[i].v) →
    (∀ i j (hi : i < L.length) (hj : j < L.length), i < j → L[j].v ≠ L[i].v) → Good L
  | [], _, _ => trivial
  | s :: L, he, hv => by
    refine ⟨fun t ht a ha => ?_, fun t ht => ?_, good_of_getElem L ?_ ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
      exact he 0 j (by simp) hj (Nat.zero_le _) a ha
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
      exact hv 0 (j + 1) (by simp) (by simp; omega) (by omega)
    · intro i j hi hj hij
      exact he (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
    · intro i j hi hj hij
      exact hv (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)

theorem foldr_self {σ : ℕ → ZMod p} : ∀ L : List Step,
    (∀ t ∈ L, σ t.v = (t.e.toLC p).eval σ) →
    L.foldr (fun s σ => Function.update σ s.v ((s.e.toLC p).eval σ)) σ = σ
  | [], _ => rfl
  | s :: L, h => by
    simp only [List.foldr_cons]
    rw [foldr_self L fun t ht => h t (List.mem_cons_of_mem _ ht)]
    exact Function.update_eq_self_iff.mpr (h s (List.mem_cons_self ..)).symm

theorem holds_mono {P : Problem} {k n : ℕ} {σ : ℕ → ZMod p} (hkn : k ≤ n) (h : Holds p P n σ) :
    Holds p P k σ := fun j hj => h j (by omega)

theorem recompute_of_ne (P : Problem) (τ : ℕ → ZMod p) (x : ℕ) (hx : ∀ s ∈ P.steps, s.v ≠ x) :
    recompute p P τ x = τ x := by
  unfold recompute
  have : ∀ s ∈ P.steps.toList, s.v ≠ x := fun s hs => hx s (by simpa using hs)
  generalize P.steps.toList = L at this ⊢
  induction L with
  | nil => rfl
  | cons s L ih =>
    simp only [List.foldr_cons]
    rw [Function.update_of_ne (this s (List.mem_cons_self ..)).symm]
    exact ih fun t ht => this t (List.mem_cons_of_mem _ ht)

/-- A step's checked equation: its row, ended as `R` with relation `d`, gives
`d = c · (v - e)` with `c ≠ 0`. -/
theorem eval_rel_step [Fact p.Prime] {s : Step} {d : Lc}
    (hc : coeffOf p s.v d ≠ 0)
    (hz : isZero p ⟨d.k + coeffOf p s.v d * s.e.k,
      (neg p (coeffOf p s.v d), s.v) :: d.t ++ (scale (coeffOf p s.v d) s.e).t⟩ = true)
    (σ : ℕ → ZMod p) :
    (d.toLC p).eval σ = ((coeffOf p s.v d : ℕ) : ZMod p) * (σ s.v - (s.e.toLC p).eval σ) ∧
      ((coeffOf p s.v d : ℕ) : ZMod p) ≠ 0 := by
  have hz := eval_of_isZero (σ := σ) hz
  rw [eval_toLC] at hz
  simp only [scale, Nat.cast_add, Nat.cast_mul, tsum_cons, tsum_append, tsum_map_mul,
    neg_natCast] at hz
  refine ⟨?_, ?_⟩
  · rw [eval_toLC, eval_toLC]; linear_combination hz
  · rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hc (Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ (Fact.out : p.Prime).pos))

theorem mem_steps {P : Problem} {s : Step} (hs : s ∈ P.steps) : ∃ k : ℕ, P.steps[k]? = some s := by
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hs
  exact ⟨k, Array.getElem?_eq_getElem hk⟩

section Checked

variable {P : Problem} (h : checkOver p P = true)
include h

theorem parts : (∀ k < P.steps.size, (match P.steps[k]? with
      | some s => stepOk p P k s
      | none => false) = true) ∧ varsOk P = true ∧ ∀ r ∈ P.recs, recOk p P r = true := by
  simp only [checkOver, headerOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Array.all_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem steps_ok : ∀ k s, P.steps[k]? = some s → stepOk p P k s = true := by
  intro k s hs
  have hk : k < P.steps.size := by
    by_contra hk; rw [Array.getElem?_eq_none (by omega)] at hs; cases hs
  simpa [hs] using (parts h).1 k hk

/-- What the checker knows of step `k`. -/
theorem step_spec {k : ℕ} {s : Step} (hs : P.steps[k]? = some s) :
    idx P.vars s.v = some k ∧ (∃ e ∈ P.vars, e.id = s.v ∧ e.vis = 2) ∧
      (∀ a ∈ s.e.t, ∀ i, idx P.vars a.2 = some i → k < i) ∧
      ∃ R d, certRow p P.steps k s.src = some R ∧ rel p R = some d ∧ coeffOf p s.v d ≠ 0 ∧
        isZero p ⟨d.k + coeffOf p s.v d * s.e.k,
          (neg p (coeffOf p s.v d), s.v) :: d.t ++ (scale (coeffOf p s.v d) s.e).t⟩ = true := by
  have := steps_ok h k s hs
  simp only [stepOk, Bool.and_eq_true, List.all_eq_true] at this
  obtain ⟨⟨hv, he⟩, hr⟩ := this
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold idx
    split at hv
    · next e hen => simp only [Bool.and_eq_true, beq_iff_eq] at hv; simp [hen, hv.2]
    · cases hv
  · split at hv
    · next e hen =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      exact ⟨e, (entry_spec hen).1, (entry_spec hen).2, hv.1⟩
    · cases hv
  · intro a ha i hi
    have := he a ha
    rw [hi] at this
    simpa using this
  · split at hr
    · next R hR =>
      split at hr
      · next d hd =>
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
        exact ⟨R, d, hR, hd, hr.1, hr.2⟩
      · cases hr
    · cases hr

/-- Distinct steps eliminate distinct variables. -/
theorem step_v_ne {j k : ℕ} {s t : Step} (hs : P.steps[j]? = some s) (ht : P.steps[k]? = some t)
    (hjk : j ≠ k) : s.v ≠ t.v := by
  intro he
  have h1 := (step_spec h hs).1
  rw [he, (step_spec h ht).1] at h1
  exact hjk (Option.some.inj h1).symm

/-- A step's form doesn't name the variable of that step or of any earlier one. -/
theorem step_e_ne {j k : ℕ} {s t : Step} (hs : P.steps[j]? = some s) (ht : P.steps[k]? = some t)
    (hjk : j ≤ k) : ∀ a ∈ t.e.t, a.2 ≠ s.v := by
  intro a ha he
  have := (step_spec h ht).2.2.1 a ha j (by rw [he]; exact (step_spec h hs).1)
  omega

/-- A form naming only unlisted or uneliminated variables names no step's variable. -/
theorem ne_of_idx {x : ℕ} (hx : idx P.vars x = none) : ∀ s ∈ P.steps, s.v ≠ x := by
  intro s hs he
  obtain ⟨k, hk⟩ := mem_steps hs
  have := (step_spec h hk).1
  rw [he, hx] at this
  cases this

theorem good : Good P.steps.toList := by
  apply good_of_getElem
  · intro i j hi hj hij
    simp only [Array.length_toList] at hi hj
    simp only [Array.getElem_toList]
    exact step_e_ne h (Array.getElem?_eq_getElem hi) (Array.getElem?_eq_getElem hj) hij
  · intro i j hi hj hij
    simp only [Array.length_toList] at hi hj
    simp only [Array.getElem_toList]
    exact step_v_ne h (Array.getElem?_eq_getElem hj) (Array.getElem?_eq_getElem hi) (by omega)

/-- At `recompute P τ` every step's equation holds. -/
theorem holds_recompute (τ : ℕ → ZMod p) : Holds p P P.steps.size (recompute p P τ) :=
  fun _ _ s hs => foldr_holds τ _ (good h) s (by simpa using Array.mem_of_getElem? hs)

/-- At a solution of the original rows, every step's equation holds: step `k`'s row, its
earlier steps substituted, says `c · (v k - e k) = 0`. -/
theorem holds_of_sat [Fact p.Prime] {σ : ℕ → ZMod p} (hσ : Sat (orig p P) σ) :
    ∀ k ≤ P.steps.size, Holds p P k σ := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj t ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih (by omega) j hj t ht
    obtain ⟨-, -, -, R, d, hR, hd, hc, hz⟩ := step_spec h ht
    have hsat : (R.toRow p).Sat σ := by
      rw [sat_certRow (ih (by omega)) hR]
      exact hσ _ (List.mem_append_left _
        (List.mem_map.mpr ⟨t, by simpa using Array.mem_of_getElem? ht, rfl⟩))
    rw [sat_iff_of_rel hd] at hsat
    obtain ⟨he, hc⟩ := eval_rel_step hc hz σ
    rw [hsat, eq_comm, mul_eq_zero] at he
    exact sub_eq_zero.mp (he.resolve_left hc)

/-- A row that defines no step and the row it ended as. -/
theorem rec_spec [NeZero p] {r : Orig × Fate} (hr : r ∈ P.recs) :
    ∃ R, certRow p P.steps P.steps.size r.1 = some R ∧
      ∀ σ : ℕ → ZMod p, match r.2 with
        | .kept M => (∀ l ∈ [M.a, M.b, M.c], ∀ a ∈ l.t, ∀ s ∈ P.steps, s.v ≠ a.2) ∧
            ((R.toRow p).Sat σ ↔ (M.toRow p).Sat σ)
        | .dropped => (R.toRow p).Sat σ := by
  have := (parts h).2.2 r hr
  unfold recOk at this
  split at this
  · next R M hR hM =>
    refine ⟨R, hR, fun σ => ?_⟩
    rw [hM]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
    refine ⟨fun l hl a ha => ne_of_idx h ?_, ?_⟩
    · have := this.1
      simp only [outOk, List.all_eq_true, beq_iff_eq] at this
      exact this l hl a ha
    · rcases this.2 with rfl | ⟨⟨ha, hb⟩, hc⟩
      · rfl
      · have e := fun x y (hz : isZero p (sub p x y) = true) =>
          sub_eq_zero.mp ((eval_sub x y σ).symm.trans (eval_of_isZero hz σ))
        simp only [R1cs.Row.Sat, Row.toRow, e _ _ ha, e _ _ hb, e _ _ hc]
  · next R hR hd =>
    refine ⟨R, hR, fun σ => ?_⟩
    rw [hd]
    split at this
    · next d hrel => exact (sat_iff_of_rel hrel σ).mpr (eval_of_isZero this σ)
    · cases this
  · cases this

theorem sound_over [Fact p.Prime] (τ : ℕ → ZMod p) (hM : Sat (keyed p P) τ) :
    Sat (orig p P) (recompute p P τ) := by
  set σ := recompute p P τ
  have hH : Holds p P P.steps.size σ := holds_recompute h τ
  intro row hrow
  rcases List.mem_append.mp hrow with hrow | hrow
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨k, hk⟩ := mem_steps (by simpa using ht)
    have hks : k < P.steps.size := by
      by_contra hn; rw [Array.getElem?_eq_none (by omega)] at hk; cases hk
    obtain ⟨-, -, -, R, d, hR, hd, hc, hz⟩ := step_spec h hk
    rw [← sat_certRow (holds_mono hks.le hH) hR, sat_iff_of_rel hd,
      (eval_rel_step hc hz σ).1, hH k hks t hk, sub_self, mul_zero]
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨R, hR, hspec⟩ := rec_spec h (by simpa using hr)
    rw [← sat_certRow hH hR]
    have := hspec σ
    split at this
    · next M hM' =>
      rw [this.2]
      have hτ := hM (M.toRow p) (List.mem_filterMap.mpr ⟨r, hr, by simp [hM', Fate.out]⟩)
      have e := fun l (hl : l ∈ [M.a, M.b, M.c]) => eval_congr (p := p) l (σ := σ) (σ' := τ)
        fun a ha => recompute_of_ne P τ a.2 (this.1 l hl a ha)
      simp only [R1cs.Row.Sat, Row.toRow, e M.a (by simp), e M.b (by simp), e M.c (by simp)]
      exact hτ
    · exact this

theorem complete_over [Fact p.Prime] (σ : ℕ → ZMod p) (hσ : Sat (orig p P) σ) :
    Sat (keyed p P) σ ∧ recompute p P σ = σ := by
  have hH := holds_of_sat h hσ _ le_rfl
  refine ⟨fun row hrow => ?_, ?_⟩
  · obtain ⟨r, hr, hout⟩ := List.mem_filterMap.mp hrow
    obtain ⟨R, hR, hspec⟩ := rec_spec h (by simpa using hr)
    have := hspec σ
    split at this
    · next M hM =>
      rw [hM] at hout
      simp only [Fate.out, Option.map_some, Option.some.injEq] at hout
      rw [← hout, ← this.2, sat_certRow hH hR]
      exact hσ _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    · next hd => rw [hd] at hout; cases hout
  · apply foldr_self
    intro t ht
    obtain ⟨k, hk⟩ := mem_steps (by simpa using ht)
    have hks : k < P.steps.size := by
      by_contra hn; rw [Array.getElem?_eq_none (by omega)] at hk; cases hk
    exact hH k hks t hk

end Checked

theorem checkOver_of_check {P : Problem} (h : check P = true) : checkOver r P = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.2

/-- **Soundness.** If the checker accepts, every solution of the minimized rows extends to
a solution of the original rows: `recompute` gives each eliminated variable its defining
form and leaves every other variable alone. -/
theorem check_sound {P : Problem} (h : check P = true) (τ : ℕ → ZMod r)
    (hM : Sat (keyed r P) τ) :
    Sat (orig r P) (recompute r P τ) ∧ ∀ x, (∀ s ∈ P.steps, s.v ≠ x) → recompute r P τ x = τ x :=
  ⟨sound_over (checkOver_of_check h) τ hM, recompute_of_ne P τ⟩

/-- **Completeness.** If the checker accepts, every solution of the original rows solves
the minimized rows, and its eliminated variables are the ones `recompute` gives it. -/
theorem check_complete {P : Problem} (h : check P = true) (σ : ℕ → ZMod r)
    (hσ : Sat (orig r P) σ) : Sat (keyed r P) σ ∧ recompute r P σ = σ :=
  complete_over (checkOver_of_check h) σ hσ

/-- If the checker accepts, every eliminated variable is listed `Internal`: no public or
private input is eliminated. -/
theorem check_internal {P : Problem} (h : check P = true) :
    ∀ s ∈ P.steps, ∃ e ∈ P.vars, e.id = s.v ∧ e.vis = 2 := by
  intro s hs
  obtain ⟨k, hk⟩ := mem_steps hs
  exact (step_spec (checkOver_of_check h) hk).2.1

/-- If the checker accepts, the output lists every input variable that isn't internal,
with its visibility. -/
theorem check_inputs {P : Problem} (h : check P = true) :
    ∀ e ∈ P.vars, e.vis ≠ 2 → (e.id, e.vis) ∈ P.outVars := by
  intro e he hv
  have := (parts (checkOver_of_check h)).2.1
  simp only [varsOk, Bool.and_eq_true, Array.all_eq_true', Bool.or_eq_true, beq_iff_eq] at this
  rcases this.1 e he with h2 | hf
  · exact absurd h2 hv
  · exact mem_of_find hf

end Xark.Minimize
