/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.CondSwap
import Formal.GrumpkinGroup

set_option linter.style.header false

/-!
# `xark_merkle::cond_swap`, proven over its exported rows

`Formal/Templates/CondSwap.lean` is the R1CS the frontend emits for one call of
`xark_merkle::cond_swap(s, a, b)` (`cargo xtask lean-export cond_swap`), halo2's
one-product conditional swap: the booleanity row `s · s = s` and the product
`s · (b − a) = w`, with outputs `a' = a + w` and `b' = b − w` and one product hint for `w`.

* **Soundness** (`soundness`, no input assumption): every assignment satisfying the rows
  has `s ∈ {0, 1}` and outputs `(a, b)` when `s = 0`, `(b, a)` when `s = 1`. The
  booleanity is the template's own row, so no caller has to enforce it.

`xark_merkle::merkle_root` calls `cond_swap(index_bits[i], node, siblings[i])` at each of
its `DEPTH` levels (a const generic, so the path length is fixed by the circuit's type)
and hashes the pair with `xark_poseidon::hash2`. `root_binds` composes the levels: if the
levels' swaps are satisfied and wired as `merkle_root` wires them, every index bit is a
bit and the computed root is `merkleRoot H leaf path`, the Merkle root of the leaf along
its path. It rests on two things this file does not prove. First, an assumption about the
hash: every assignment satisfying `hash2`'s rows outputs `H (left, right)` for a function
`H`. `hash2` has no exported-template proof, so this is assumed, not proven over its rows.
Second, each level of `merkle_root` emits this template's rows with `node` and the
sibling in the input positions; the export checks the harness call only, and matching
every production call is ticket 08's coverage check (a constant index bit, for one,
would fold the rows). That the root binds the leaf in the cryptographic sense is then
`H`'s collision resistance.
-/

namespace Xark.Templates.CondSwap

open Xark.Template Xark.R1cs

instance : Fact (Nat.Prime r) := bn254_r_prime

/-- A field element that is a bit. -/
def IsBit (x : F) : Prop := x = 0 ∨ x = 1

/-- The spec, on inputs `[s, a, b]`: `s` is a bit and the outputs are `s ? (b, a) : (a, b)`. -/
def Spec (ins outs : List F) : Prop :=
  ∃ s a b, ins = [s, a, b] ∧ ((s = 0 ∧ outs = [a, b]) ∨ (s = 1 ∧ outs = [b, a]))

/-! ### The exported template, read structurally -/

/-- `s · (b − a)`'s right side. -/
def diff : LC := ⟨0, [(-1, .plug 1), (1, .plug 2)]⟩

theorem inputs_eq : template.inputs = [.var (.plug 0), .var (.plug 1), .var (.plug 2)] := by
  decide +kernel

theorem outputs_eq :
    template.outputs = [⟨0, [(1, .plug 1), (1, .wit 1)]⟩, ⟨0, [(1, .plug 2), (-1, .wit 1)]⟩] := by
  decide +kernel

theorem rows_eq : template.rows =
    [⟨.var (.plug 0), .var (.plug 0), .var (.plug 0)⟩, ⟨.var (.plug 0), diff, .var (.wit 1)⟩] := by
  decide +kernel

theorem eval_diff (σ : TVar → F) : diff.eval σ = σ (.plug 2) - σ (.plug 1) := by
  simp [diff, LC.eval]; ring

theorem ins_eq (σ : TVar → F) : template.ins σ = [σ (.plug 0), σ (.plug 1), σ (.plug 2)] := by
  simp [Template.ins, inputs_eq]

theorem outs_eq (σ : TVar → F) :
    template.outs σ = [σ (.plug 1) + σ (.wit 1), σ (.plug 2) - σ (.wit 1)] := by
  simp [Template.outs, outputs_eq, LC.eval]; ring

/-- The rows hold iff `s · s = s` and `w = s · (b − a)`. -/
theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    σ (.plug 0) * σ (.plug 0) = σ (.plug 0) ∧
      σ (.plug 0) * (σ (.plug 2) - σ (.plug 1)) = σ (.wit 1) := by
  simp [Template.Sat, rows_eq, Xark.R1cs.Sat, Row.Sat, eval_diff]

theorem isBit_of_mul_self {x : F} (h : x * x = x) : IsBit x := by
  have : x * (x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

/-! ### Soundness -/

/-- **Soundness.** Any assignment satisfying the exported rows has a bit selector and
outputs `(a, b)` when it is `0` and `(b, a)` when it is `1`; no assumption on the inputs. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  obtain ⟨hb, hw⟩ := (sat_iff σ).mp h
  refine ⟨_, _, _, ins_eq σ, ?_⟩
  rw [outs_eq, ← hw]
  rcases isBit_of_mul_self hb with h0 | h1
  · exact Or.inl ⟨h0, by rw [h0]; simp⟩
  · exact Or.inr ⟨h1, by rw [h1]; simp⟩

/-! ### The Merkle root -/

/-- The Merkle root of `node` along `path`, one `(bit, sibling)` per level, leaf level
first: bit `0` hashes `(node, sibling)`, bit `1` hashes `(sibling, node)`. -/
def merkleRoot (H : F → F → F) : F → List (F × F) → F
  | node, [] => node
  | node, (b, s) :: path => merkleRoot H (if b = 0 then H node s else H s node) path

/-- The node `merkle_root` hashes from one level's swap assignment, under the assumption
that `hash2`'s rows compute `H`. -/
def next (H : F → F → F) (σ : TVar → F) : F :=
  H ((template.outs σ).getD 0 0) ((template.outs σ).getD 1 0)

/-- `σs` are the swaps of `merkle_root`'s levels along `path` from `node`: level `i`'s
rows hold and its inputs are `(bitᵢ, running node, siblingᵢ)`, with one swap per level. -/
def Wired (H : F → F → F) : F → List (TVar → F) → List (F × F) → Prop
  | _, [], [] => True
  | node, σ :: σs, (b, s) :: path =>
    template.Sat σ ∧ template.ins σ = [b, node, s] ∧ Wired H (next H σ) σs path
  | _, _, _ => False

/-- The node the levels compute, `next` folded over them. -/
def circuitRoot (H : F → F → F) : F → List (TVar → F) → F
  | node, [] => node
  | _, σ :: σs => circuitRoot H (next H σ) σs

/-- **Root binding.** If `merkle_root`'s levels are satisfied and wired along `path` from
`leaf`, every index bit is a bit and the root they compute is `merkleRoot H leaf path`. -/
theorem root_binds (H : F → F → F) :
    ∀ (leaf : F) (σs : List (TVar → F)) (path : List (F × F)), Wired H leaf σs path →
      (∀ p ∈ path, IsBit p.1) ∧ circuitRoot H leaf σs = merkleRoot H leaf path
  | _, [], [], _ => ⟨by simp, rfl⟩
  | _, [], _ :: _, h | _, _ :: _, [], h => h.elim
  | node, σ :: σs, (b, s) :: path, ⟨hsat, hins, hw⟩ => by
    obtain ⟨s', a, b', hins', hspec⟩ := soundness σ hsat
    rw [hins] at hins'
    simp only [List.cons.injEq, and_true] at hins'
    obtain ⟨rfl, rfl, rfl⟩ := hins'
    have hnext : next H σ = if b = 0 then H node s else H s node := by
      rcases hspec with ⟨h0, ho⟩ | ⟨h1, ho⟩
      · simp [next, ho, h0]
      · simp [next, ho, h1]
    obtain ⟨hbits, hroot⟩ := root_binds H _ σs path hw
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rcases hspec with ⟨h0, _⟩ | ⟨h1, _⟩
        · exact Or.inl h0
        · exact Or.inr h1
      · exact hbits p hp
    · rw [circuitRoot, hroot, merkleRoot, hnext]

end Xark.Templates.CondSwap
