/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Gadgets
import Formal.Rewrites

set_option linter.style.header false
set_option linter.style.longLine false
-- `Xark.Template.Template`: the structure is named after its namespace.
set_option linter.dupNamespace false

/-!
# Exported gadget templates

A `#[gadget]` function's calls are recorded by the frontend
(`crates/frontend/src/gadgets.rs`) and `cargo xtask lean-export <gadget>` writes one
call's exact R1CS to `Formal/Templates/<Gadget>.lean` as a `Template`: the rows
`a · b = c` over BN254's scalar field (the `Xark.R1cs` rows of `Formal/Rewrites.lean`,
so its rewrite lemmas apply), the hints the prover runs, and each variable's role. A
proof about a gadget is a theorem about that `Template` value, and
`cargo xtask lean-export --check` fails when the code stops emitting it.
-/

namespace Xark.Template

/-- A template's variable: `plug i`, the `i`-th variable its inputs read, or `wit j`,
the `j`-th variable the call allocated. -/
inductive TVar where
  | plug (i : ℕ)
  | wit (j : ℕ)
  deriving DecidableEq, Repr

/-- BN254's scalar field, `ark_bn254::Fr`. -/
abbrev F := ZMod r

deriving instance DecidableEq for Xark.R1cs.LC
deriving instance DecidableEq for Xark.R1cs.Row

abbrev LC := Xark.R1cs.LC F TVar
abbrev Row := Xark.R1cs.Row F TVar

/-- A witness op (`xark_ir::primitive::WitnessGen`): how the prover computes the
`wit` variables it names. -/
inductive Hint where
  | product (out : ℕ) (left right : LC)
  | linear (out : ℕ) (lc : LC)
  | xor (out : ℕ) (a b : LC)
  | or (out : ℕ) (a b : LC)
  | inverse (out : ℕ) (input : LC)
  | inverseOrZero (out : ℕ) (input : LC)
  | bit (out : ℕ) (input : LC) (index : ℕ)
  | bits (outs : List ℕ) (input : LC)
  | divRem (q r : ℕ) (num den : LC)
  deriving DecidableEq

/-- One `#[gadget]` call as the frontend emitted it. -/
structure Template where
  /-- `sha256` of the exported data; what `lean-export --check` compares. -/
  hash : String
  /-- `module::function`. -/
  name : String
  plugs : ℕ
  wits : ℕ
  /-- The parameters' field elements, in order. -/
  inputs : List LC
  /-- The result's field elements. -/
  outputs : List LC
  hints : List Hint
  rows : List Row

/-- Bit `i` of `x`'s canonical representative, as a field element. -/
def bitOf (x : F) (i : ℕ) : F := if x.val.testBit i then 1 else 0

namespace Template

/-- Every row holds under `σ`. -/
def Sat (t : Template) (σ : TVar → F) : Prop := Xark.R1cs.Sat t.rows σ

/-- The inputs' values under `σ`. -/
def ins (t : Template) (σ : TVar → F) : List F := t.inputs.map (·.eval σ)

/-- The outputs' values under `σ`. -/
def outs (t : Template) (σ : TVar → F) : List F := t.outputs.map (·.eval σ)

/-! ### Plugs carrying linear combinations

A production call can pass any linear combination for an input: a constant, a sum
of earlier wires. Its rows are then the template's with each plug `p` replaced by
that combination `e` (`Rewrites.lean`'s `LC.subst`), which `cargo xtask lean-export
--coverage` checks up to renaming and reduction mod `r`. `inst` substitutes the
plugs one after another, so it is those rows when no combination reads a plug
substituted after it: always for constants (`consts`), which is the case proven per
gadget here. The template's soundness carries over to `inst`'s rows whenever the
substituted inputs meet its assumptions. -/

open Xark.R1cs

/-- `σ` with each plug `p` of `k` set to its combination's value. -/
def env (k : List (ℕ × LC)) (σ : TVar → F) : TVar → F :=
  k.foldr (fun p τ => Function.update τ (.plug p.1) (p.2.eval τ)) σ

/-- The combinations `k` substituted for their plugs in `l`. -/
def instLC (k : List (ℕ × LC)) (l : LC) : LC :=
  k.foldl (fun l p => l.subst (.plug p.1) p.2) l

theorem env_cons (p : ℕ × LC) (k : List (ℕ × LC)) (σ : TVar → F) :
    env (p :: k) σ = Function.update (env k σ) (.plug p.1) (p.2.eval (env k σ)) := rfl

theorem eval_instLC (k : List (ℕ × LC)) (l : LC) (σ : TVar → F) :
    (instLC k l).eval σ = l.eval (env k σ) := by
  induction k generalizing l with
  | nil => rfl
  | cons p k ih =>
    rw [instLC, List.foldl_cons, ← instLC, ih, LC.eval_subst, env_cons]

/-- A hint with the combinations `k` substituted. -/
def _root_.Xark.Template.Hint.inst (k : List (ℕ × LC)) : Hint → Hint
  | .product o a b => .product o (instLC k a) (instLC k b)
  | .linear o a => .linear o (instLC k a)
  | .xor o a b => .xor o (instLC k a) (instLC k b)
  | .or o a b => .or o (instLC k a) (instLC k b)
  | .inverse o x => .inverse o (instLC k x)
  | .inverseOrZero o x => .inverseOrZero o (instLC k x)
  | .bit o x i => .bit o (instLC k x) i
  | .bits os x => .bits os (instLC k x)
  | .divRem q m n d => .divRem q m (instLC k n) (instLC k d)

/-- The template with the combinations `k` substituted for their plugs. -/
def inst (t : Template) (k : List (ℕ × LC)) : Template :=
  { t with
    inputs := t.inputs.map (instLC k)
    outputs := t.outputs.map (instLC k)
    hints := t.hints.map (Hint.inst k)
    rows := t.rows.map fun r => ⟨instLC k r.a, instLC k r.b, instLC k r.c⟩ }

theorem sat_inst (t : Template) (k : List (ℕ × LC)) (σ : TVar → F) :
    (t.inst k).Sat σ ↔ t.Sat (env k σ) := by
  simp [Sat, inst, Xark.R1cs.Sat, Row.Sat, eval_instLC]

theorem ins_inst (t : Template) (k : List (ℕ × LC)) (σ : TVar → F) :
    (t.inst k).ins σ = t.ins (env k σ) := by
  simp [ins, inst, eval_instLC]

theorem outs_inst (t : Template) (k : List (ℕ × LC)) (σ : TVar → F) :
    (t.inst k).outs σ = t.outs (env k σ) := by
  simp [outs, inst, eval_instLC]

/-- **Soundness carries over** to the template with plugs carrying `k`, on inputs
meeting the assumptions. -/
theorem soundness_inst {A : List F → Prop} {S : List F → List F → Prop} (t : Template)
    (sound : ∀ σ, A (t.ins σ) → t.Sat σ → S (t.ins σ) (t.outs σ)) (k : List (ℕ × LC))
    (σ : TVar → F) (ha : A ((t.inst k).ins σ)) (h : (t.inst k).Sat σ) :
    S ((t.inst k).ins σ) ((t.inst k).outs σ) := by
  rw [ins_inst] at ha ⊢
  rw [outs_inst]
  exact sound _ ha ((sat_inst t k σ).mp h)

/-- Constant plugs `c`: the combinations `LC.cst`. -/
def consts (c : List (ℕ × F)) : List (ℕ × LC) := c.map fun p => (p.1, LC.cst p.2)

/-! ### Folding a witness

The frontend folds a call whose inputs are partly constant further than `inst`: a
hint whose inputs are all constant (`hint_bit` of a constant) is replaced by its
value, and one that is affine in the call's other wires (XOR with a constant
operand: `k + (1 − 2k)·x`) by that form, and the rows this closes are dropped.
`cargo xtask lean-export --coverage` replays that on the proven template: after
`inst`, it folds one witness `o` at a time into the combination `e` its hint
computes and drops each row the substitution leaves holding at every assignment
(closed and true, or an identity like `2k · x = 2k·x`); the call is covered when
what is left hashes to the call's template. `foldAt` is one such step. -/

/-- `t` with witness `o` folded into `e`: inputs and outputs read `e` for `o`, and
`keep` and `hs` are the rows and hints left. -/
def foldAt (t : Template) (o : ℕ) (e : LC) (keep : List Row) (hs : List Hint) : Template :=
  { t with
    inputs := t.inputs.map (·.subst (.wit o) e)
    outputs := t.outputs.map (·.subst (.wit o) e)
    hints := hs
    rows := keep }

/-- Each row of `t` with `e` for `o` is kept, or holds at every assignment. -/
def Folds (t : Template) (o : ℕ) (e : LC) (keep : List Row) : Prop :=
  ∀ r ∈ t.rows, r.subst (.wit o) e ∈ keep ∨ ∀ σ, (r.subst (.wit o) e).Sat σ

theorem ins_foldAt (t : Template) (o : ℕ) (e : LC) (keep : List Row) (hs : List Hint)
    (σ : TVar → F) :
    (t.foldAt o e keep hs).ins σ = t.ins (Function.update σ (.wit o) (e.eval σ)) := by
  simp [ins, foldAt, LC.eval_subst]

theorem outs_foldAt (t : Template) (o : ℕ) (e : LC) (keep : List Row) (hs : List Hint)
    (σ : TVar → F) :
    (t.foldAt o e keep hs).outs σ = t.outs (Function.update σ (.wit o) (e.eval σ)) := by
  simp [outs, foldAt, LC.eval_subst]

/-- **A fold adds no solution.** An assignment of the folded rows, with `o` set to
`e`'s value, satisfies the original ones. (No condition on `e`: the hint it came
from doesn't matter.) -/
theorem sat_of_foldAt (t : Template) (o : ℕ) (e : LC) (keep : List Row) (hs : List Hint)
    (hf : t.Folds o e keep) (σ : TVar → F) (h : (t.foldAt o e keep hs).Sat σ) :
    t.Sat (Function.update σ (.wit o) (e.eval σ)) := by
  intro r hr
  rw [← Row.sat_subst]
  rcases hf r hr with hk | hv
  · exact h _ hk
  · exact hv σ

/-- **Soundness carries over** to a fold: what the folded rows accept, the
original rows accept with `o := e`, and the inputs and outputs are the same
values there. -/
theorem soundness_foldAt {A : List F → Prop} {S : List F → List F → Prop} (t : Template)
    (sound : ∀ σ, A (t.ins σ) → t.Sat σ → S (t.ins σ) (t.outs σ)) (o : ℕ) (e : LC)
    (keep : List Row) (hs : List Hint) (hf : t.Folds o e keep) (σ : TVar → F)
    (ha : A ((t.foldAt o e keep hs).ins σ)) (h : (t.foldAt o e keep hs).Sat σ) :
    S ((t.foldAt o e keep hs).ins σ) ((t.foldAt o e keep hs).outs σ) := by
  rw [ins_foldAt] at ha ⊢
  rw [outs_foldAt]
  exact sound _ ha (sat_of_foldAt t o e keep hs hf σ h)

end Template

end Xark.Template
