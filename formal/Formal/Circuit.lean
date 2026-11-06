/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Template
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Lift

set_option linter.style.header false
-- `Xark.Circuit.Circuit`: the type is named after its namespace, as `Template` is.
set_option linter.dupNamespace false

/-!
# A whole circuit as its gadget calls

`cargo xtask lean-export --circuit <example>` writes `Formal/Circuits/<Example>.lean`: the
example's rows as a list of segments, each either the glue rows outside every `#[gadget]`
call or a call of a proven template with the combinations its plugs carry and the first
variable it allocated. `rows` spells the segments out over the circuit's own variables
(`ℕ`); `cargo xtask lean-export --check` runs `CircuitHash.lean`, which prints the hash of
`rows` for each circuit, and fails unless it is the hash of the rows the compiler emitted.
So a theorem about `Sat C σ` is a theorem about the production circuit.

`sat_call` hands each call's template its satisfying assignment, so every template's
`soundness` applies to its call; the circuit files prove their `Assumptions` from the other
calls' `Spec`s.
-/

namespace Xark.R1cs.LC

variable {F : Type*} [CommRing F] {V W : Type*}

/-- `l` with each variable `v` replaced by the combination `f v`. -/
def bind (l : LC F V) (f : V → LC F W) : LC F W :=
  ⟨l.const + (l.terms.map fun t => t.1 * (f t.2).const).sum,
    l.terms.flatMap fun t => (f t.2).terms.map fun u => (t.1 * u.1, u.2)⟩

theorem eval_bind (l : LC F V) (f : V → LC F W) (σ : W → F) :
    (l.bind f).eval σ = l.eval fun v => (f v).eval σ := by
  obtain ⟨c, ts⟩ := l
  simp only [bind, eval]
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_map, Function.comp_def] at ih ⊢
    have h1 : ((f t.2).terms.map fun u => t.1 * u.1 * σ u.2).sum =
        t.1 * ((f t.2).terms.map fun u => u.1 * σ u.2).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun u _ => by ring
    linear_combination ih + h1

end Xark.R1cs.LC

namespace Xark.Circuit

open Xark.R1cs Xark.Template

/-- A combination over the circuit's variables. -/
abbrev GLC := Xark.R1cs.LC F ℕ
/-- A row over the circuit's variables. -/
abbrev GRow := Xark.R1cs.Row F ℕ

/-- The exported data carries integer coefficients (the ones the frontend holds, any sign):
an integer literal elaborates at once, a field numeral goes through `Nat.AtLeastTwo` per
literal, which made a circuit of 600 calls take half an hour. -/
abbrev ZLC := Xark.R1cs.LC ℤ ℕ
abbrev ZRow := Xark.R1cs.Row ℤ ℕ

/-- The integer coefficients read in the field. -/
def ZLC.toF (l : ZLC) : GLC := ⟨(l.const : F), l.terms.map fun t => ((t.1 : F), t.2)⟩
def ZRow.toF (r : ZRow) : GRow := ⟨ZLC.toF r.a, ZLC.toF r.b, ZLC.toF r.c⟩

/-- One call of a proven template inside the circuit: the combinations its plugs carry (the
harness calls the gadget on fresh variables, so `plug i` is input `i`) and the first
variable it allocated (`wit j` is variable `base + j`). -/
structure Call where
  t : Template
  plugs : List ZLC
  base : ℕ

namespace Call

/-- Each template variable as a combination over the circuit's. -/
def env (c : Call) : TVar → GLC
  | .plug i => ZLC.toF (c.plugs.getD i (LC.cst 0))
  | .wit j => LC.var (c.base + j)

/-- The call's rows: the template's over the circuit's variables. -/
def rows (c : Call) : List GRow :=
  c.t.rows.map fun r => ⟨r.a.bind c.env, r.b.bind c.env, r.c.bind c.env⟩

/-- The template's assignment under the circuit's: each template variable's combination,
evaluated. -/
def lift (c : Call) (σ : ℕ → F) : TVar → F := fun v => (c.env v).eval σ

theorem sat_rows {c : Call} {σ : ℕ → F} (h : Xark.R1cs.Sat c.rows σ) : c.t.Sat (c.lift σ) := by
  intro r hr
  have := h _ (List.mem_map_of_mem hr)
  simp only [Row.Sat, LC.eval_bind] at this
  exact this

theorem ins (c : Call) (σ : ℕ → F) :
    c.t.ins (c.lift σ) = c.t.inputs.map fun l => (l.bind c.env).eval σ := by
  simp only [Template.ins, LC.eval_bind]
  rfl

theorem outs (c : Call) (σ : ℕ → F) :
    c.t.outs (c.lift σ) = c.t.outputs.map fun l => (l.bind c.env).eval σ := by
  simp only [Template.outs, LC.eval_bind]
  rfl

end Call

/-- A run of the circuit's rows: glue outside every call, one call of a template, or a
call the frontend folded (constant plugs let it drop rows): its rows as emitted, which no
template proof covers yet (`Template.foldAt` is the step that would tie them to one). -/
inductive Seg where
  | glue (rows : List ZRow)
  | call (c : Call)
  | folded (gadget : String) (rows : List ZRow)

/-- The segment's rows. -/
def Seg.rows : Seg → List GRow
  | .glue rows => rows.map ZRow.toF
  | .call c => c.rows
  | .folded _ rows => rows.map ZRow.toF

/-- A circuit: its rows in order, as segments. -/
abbrev Circuit := List Seg

/-- Every row of the circuit. -/
def rows (C : Circuit) : List GRow := C.flatMap Seg.rows

/-- Every row holds under `σ`. -/
def Sat (C : Circuit) (σ : ℕ → F) : Prop := Xark.R1cs.Sat (rows C) σ

theorem sat_seg {C : Circuit} {s : Seg} (hs : s ∈ C) {σ : ℕ → F} (h : Sat C σ) :
    Xark.R1cs.Sat s.rows σ := fun r hr =>
  h r (List.mem_flatMap.mpr ⟨s, hs, hr⟩)

/-- A satisfying assignment of the circuit satisfies each call's template. -/
theorem sat_call {C : Circuit} {c : Call} (hc : Seg.call c ∈ C) {σ : ℕ → F} (h : Sat C σ) :
    c.t.Sat (c.lift σ) :=
  Call.sat_rows (sat_seg hc h)

/-! ## The hash `lean-export --check` compares

Rows rendered in one normal form (coefficients as canonical representatives, terms by
variable, merged, zeros dropped) and hashed with FNV-1a 64; the exporter renders the
compiler's rows the same way. A drift gate, not a commitment: whoever controls the
exporter controls both sides. -/

/-- `t` before a term list sorted by variable, merged into its head if the variable is
the same. -/
def consTerm (t : F × ℕ) : List (F × ℕ) → List (F × ℕ)
  | u :: l => if t.2 = u.2 then (t.1 + u.1, u.2) :: l else t :: u :: l
  | [] => [t]

/-- Terms sorted by variable, merged, zero coefficients dropped. A merge sort: some rows
have thousands of terms. -/
def norm (l : GLC) : GLC :=
  ⟨l.const, ((l.terms.mergeSort fun a b => a.2 ≤ b.2).foldr consTerm []).filter
    fun t => t.1 ≠ 0⟩

def renderLC (l : GLC) : String :=
  let l := norm l
  let terms := l.terms.map fun t => s!"({t.1.val}, {t.2})"
  s!"⟨{l.const.val}, [{", ".intercalate terms}]⟩"

def renderRow (r : GRow) : String := s!"⟨{renderLC r.a}, {renderLC r.b}, {renderLC r.c}⟩"

/-- FNV-1a 64 of `s`'s UTF-8 bytes. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

/-- FNV-1a 64 of the rows, rendered one per line, as sixteen hex digits. -/
def hashRows (rows : List GRow) : String :=
  let h := fnv1a64 ("\n".intercalate (rows.map renderRow))
  let hex := Nat.toDigits 16 h.toNat
  s!"fnv1a64:{String.ofList (List.replicate (16 - hex.length) '0' ++ hex)}"

/-- The circuit's hash. -/
def hash (C : Circuit) : String := hashRows (rows C)

/-- Each segment's hash and row count, the segments hashed side by side (one `Task` each):
`check` compares them with the compiler's. -/
def segHashes (C : Circuit) : List (String × Nat) :=
  (C.map fun s => Task.spawn fun _ => let r := s.rows; (hashRows r, r.length)).map Task.get

/-- `CircuitHash.lean`'s check of one circuit against the exporter's hashes: throws, naming
the first segment whose rows differ, unless the composition's rows are the compiler's.
It compares the segments' hashes, in order: equal, they pin every row, so the whole
circuit's hash (`expected`, over the same rows) is printed, not recomputed. -/
def check (name : String) (c : Circuit) (expected : String) (expectedSegs : List String) :
    IO Unit := do
  let segs := segHashes c
  let got := segs.map (·.1)
  if got != expectedSegs then
    let bad := (List.range (max got.length expectedSegs.length)).find? fun i =>
      got.getD i "" != expectedSegs.getD i ""
    let i := bad.getD 0
    throw (IO.userError s!"{name}: the Lean composition's rows differ from the compiler's \
      ({expected}); first differing segment: s{i} (Lean {got.getD i "none"}, \
      compiler {expectedSegs.getD i "none"})")
  let rows := (segs.map (·.2)).foldl (· + ·) 0
  IO.println s!"{name}: {expected} ({rows} rows, {c.length} segments)"

end Xark.Circuit
