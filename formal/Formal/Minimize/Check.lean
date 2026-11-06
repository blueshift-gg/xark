/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/

/-!
# The certified minimizer's checker

`crates/ir/src/minimize.rs` eliminates linearly defined `Internal` variables. Run with a
trace, it also writes a certificate of each run, and this checker, compiled to
`lake exe minimize_check` (`MinimizeCheck.lean`), accepts or refuses it.
`Formal/Minimize/Sound.lean` proves what acceptance means: the minimized rows have
exactly the original rows' solutions, the eliminated variables recomputed from the
survivors (`check_sound`, `check_complete`), and only `Internal` variables are
eliminated (`check_internal`).

The certificate, for original rows `O` and minimized rows `M`:

* the steps: step `k` eliminates the variable `v k := e k`, a linear form of the
  survivors and of variables eliminated at later steps, using its defining row;
* for each original row, per form (`a`, `b`, `c`), the multipliers `(j, m)` of the
  substitutions the minimizer made in it. The row it ended as is then
  `O + Σ m · (e j - v j)`, which is the original row wherever the steps' equations hold;
* for each row that defines no step, its fate: kept as the next row of `M`, or dropped.

The checker computes each ended row and checks it: a kept row must equal (as a
function) its row of `M`, which names no eliminated variable; a dropped row must be
linear and identically true; step `k`'s row, substituting only earlier steps, must be
linear with relation `c · (v k - e k)` for a nonzero `c`. Only this file's definitions
run in the checker, so it imports nothing beyond core Lean.

Coefficients are naturals read modulo `p` (the certificate's modulus, which must be
BN254's `r`).
-/

namespace Xark.Minimize

/-- A linear form `k + Σ c · x`: the constant and the `(coefficient, variable)` terms
(the order of `Xark.R1cs.LC.terms`). -/
structure Lc where
  k : Nat
  t : List (Nat × Nat)
deriving Inhabited, DecidableEq

/-- The row `a · b = c`. -/
structure Row where
  a : Lc
  b : Lc
  c : Lc
deriving Inhabited, DecidableEq

/-- A variable of the minimizer's input: its id, its visibility (`0` public, `1`
private, `2` internal, as `xark_ir::Visibility`) and the step that eliminates it. -/
structure Var where
  id : Nat
  vis : Nat
  elim : Option Nat
deriving Inhabited

/-- An original row and, per form, the multipliers `(step, m)` of the substitutions the
minimizer made in it. -/
structure Orig where
  row : Row
  ma : List (Nat × Nat)
  mb : List (Nat × Nat)
  mc : List (Nat × Nat)
deriving Inhabited

/-- A step: `v := e`, defined by the original row `src`. -/
structure Step where
  v : Nat
  e : Lc
  src : Orig
deriving Inhabited

/-- What became of an original row that defines no step. -/
inductive Fate where
  /-- Kept as the minimized row `M`. -/
  | kept (M : Row)
  /-- Dropped as identically true. -/
  | dropped
deriving Inhabited

/-- One minimizer run: the modulus, the input's variables in ascending id, the output's
`(id, visibility)` variables in ascending id, the steps (with their defining rows), and
the other original rows in order, each with what it became. The minimized rows are the
kept rows' `M`s, in order. -/
structure Problem where
  p : Nat
  vars : Array Var
  outVars : Array (Nat × Nat)
  steps : Array Step
  recs : Array (Orig × Fate)
deriving Inhabited

/-- BN254's scalar field order, `Xark.r` (`Formal/Gadgets.lean`). -/
def bn254 : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- `-m` modulo `p`. -/
def neg (p m : Nat) : Nat := p - m % p

/-- Binary search for the key `x` in `xs`, sorted by `key` ascending. Callers recheck
the answer, so this need not be proven. -/
def find {α : Type} (key : α → Nat) (xs : Array α) (x : Nat) : Option α :=
  (go 0 xs.size 64).bind fun i => xs[i]?
where
  go (lo hi : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match xs[mid]? with
        | some e => if key e == x then some mid
            else if key e < x then go (mid + 1) hi fuel else go lo mid fuel
        | none => none
      else none

/-- The input variable `x`, if listed. -/
def entry (vars : Array Var) (x : Nat) : Option Var :=
  match find Var.id vars x with
  | some e => if e.id == x then some e else none
  | none => none

/-- The step that eliminates `x`, if any. -/
def idx (vars : Array Var) (x : Nat) : Option Nat := (entry vars x).bind (·.elim)

/-- Merge adjacent terms of the same variable (`acc` is reversed). -/
def combine (p : Nat) : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | acc, [] => acc
  | [], a :: r => combine p [a] r
  | (c, x) :: acc, (d, y) :: r =>
    if x == y then combine p (((c + d) % p, x) :: acc) r
    else combine p ((d, y) :: (c, x) :: acc) r

/-- The terms with each variable once: sorted by variable, then merged. -/
def norm (p : Nat) (t : List (Nat × Nat)) : List (Nat × Nat) :=
  combine p [] (t.mergeSort fun a b => a.2 ≤ b.2)

/-- `l` is constant: every variable's total coefficient is `0`. -/
def isConst (p : Nat) (l : Lc) : Bool := (norm p l.t).all fun a => a.1 % p == 0

/-- `l` is the zero function. -/
def isZero (p : Nat) (l : Lc) : Bool := l.k % p == 0 && isConst p l

/-- `x - y`. -/
def sub (p : Nat) (x y : Lc) : Lc :=
  ⟨x.k + neg p y.k, x.t ++ y.t.map fun a => (neg p a.1, a.2)⟩

/-- `m · l`. -/
def scale (m : Nat) (l : Lc) : Lc := ⟨m * l.k, l.t.map fun a => (m * a.1, a.2)⟩

/-- The linear relation a row imposes when an operand is constant (`relation` in
`minimize.rs`): `a · b - c` with the constant operand's value. -/
def rel (p : Nat) (r : Row) : Option Lc :=
  if isConst p r.a then some (sub p (scale r.a.k r.b) r.c)
  else if isConst p r.b then some (sub p (scale r.b.k r.a) r.c)
  else none

/-- The total coefficient of `v` in `l`. -/
def coeffOf (p v : Nat) (l : Lc) : Nat :=
  (l.t.foldl (fun s a => if a.2 == v then s + a.1 else s) 0) % p

/-- `l + Σ m · (e j - v j)` over the multipliers, each step before `bound`. -/
def apply (p : Nat) (steps : Array Step) (bound : Nat) (l : Lc) :
    List (Nat × Nat) → Option Lc
  | [] => some l
  | (j, m) :: ms =>
    if j < bound then
      match steps[j]? with
      | some s => apply p steps bound
          ⟨(l.k + m * s.e.k) % p, (neg p m, s.v) :: s.e.t.map (fun a => (m * a.1, a.2)) ++ l.t⟩
          ms
      | none => none
    else none

/-- The row an original row ended as, substituting only steps before `bound`. -/
def certRow (p : Nat) (steps : Array Step) (bound : Nat) (o : Orig) : Option Row := do
  let a ← apply p steps bound o.row.a o.ma
  let b ← apply p steps bound o.row.b o.mb
  let c ← apply p steps bound o.row.c o.mc
  pure ⟨a, b, c⟩

/-- Step `k` is well formed: its variable is listed `Internal` and eliminated at `k`, its
form uses only survivors and later steps, and its row, substituting only earlier steps,
ended linear with relation `c · (v - e)`, `c ≠ 0`. -/
def stepOk (p : Nat) (P : Problem) (k : Nat) (s : Step) : Bool :=
  (match entry P.vars s.v with
    | some e => e.vis == 2 && e.elim == some k
    | none => false) &&
  s.e.t.all (fun a => match idx P.vars a.2 with
    | none => true
    | some i => k < i) &&
  match certRow p P.steps k s.src with
  | some R => match rel p R with
    | some d =>
      let c := coeffOf p s.v d
      c != 0 && isZero p ⟨d.k + c * s.e.k, (neg p c, s.v) :: d.t ++ (scale c s.e).t⟩
    | none => false
  | none => false

/-- The minimized row `M` uses no eliminated variable. -/
def outOk (P : Problem) (M : Row) : Bool :=
  [M.a, M.b, M.c].all fun l => l.t.all fun a => idx P.vars a.2 == none

/-- An original row became what its fate says: the minimized row `M` (equal as a
function, and naming no eliminated variable), or an identically true linear row. -/
def recOk (p : Nat) (P : Problem) (r : Orig × Fate) : Bool :=
  match certRow p P.steps P.steps.size r.1, r.2 with
  | some R, .kept M => outOk P M && (R == M ||
      isZero p (sub p R.a M.a) && isZero p (sub p R.b M.b) && isZero p (sub p R.c M.c))
  | some R, .dropped => match rel p R with
    | some d => isZero p d
    | none => false
  | none, _ => false

/-- The output keeps every input variable that isn't internal, with its visibility, and
lists only input variables that weren't eliminated. -/
def varsOk (P : Problem) : Bool :=
  P.vars.all (fun e => e.vis == 2 || find Prod.fst P.outVars e.id == some (e.id, e.vis)) &&
  P.outVars.all fun o => match entry P.vars o.1 with
    | some e => e.vis == o.2 && e.elim == none
    | none => false

/-- Everything but the rows that define no step (`MinimizeCheck.lean` checks those one at
a time, as it reads them). -/
def headerOk (p : Nat) (P : Problem) : Bool :=
  (List.range P.steps.size).all (fun k => match P.steps[k]? with
    | some s => stepOk p P k s
    | none => false) &&
  varsOk P

/-- **The checker**, over the prime `p`. -/
def checkOver (p : Nat) (P : Problem) : Bool := headerOk p P && P.recs.all (recOk p P)

/-- **The checker.** -/
def check (P : Problem) : Bool := P.p == bn254 && checkOver bn254 P

end Xark.Minimize
