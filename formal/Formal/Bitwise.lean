/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

-- The `style.header` linter hard-codes mathlib's Apache license string; this is
-- an MIT project, so disable that house-style check (it is not a correctness lint).
set_option linter.style.header false

/-!
# xark bitwise-gadget soundness — mechanised in Lean 4 / mathlib

Machine-checked soundness for the bitwise primitives in
`crates/xark-bits/src/lib.rs`. Each theorem mirrors the *exact*
R1CS constraint the Rust builder emits for one output bit, and proves two
things at once:

* **determinism** — the output bit is a function of the input bits (no prover
  slack / no under-constraint), and
* **functional correctness** — that function is the intended boolean op, and
  the output stays in `{0, 1}`.

Stated over any field (in particular `ark_bn254::Fr`), so they hold over *all*
field assignments — no input bound. See `Formal/Gadgets.lean` for the boolean
and range gadgets this builds on.
-/

namespace Xark

/-- **AND-bit soundness.** The AND gadget (`crates/xark-bits/src/lib.rs`) emits `aᵢ * bᵢ = outᵢ`. Given the
inputs are boolean, the output is boolean and equals the logical AND
(`out = 1 ↔ a = 1 ∧ b = 1`). -/
theorem and_sound {F : Type*} [Field F] (a b out : F)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (h : a * b = out) :
    (out = 0 ∨ out = 1) ∧ (out = 1 ↔ a = 1 ∧ b = 1) := by
  subst h
  refine ⟨?_, ?_⟩ <;>
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-- **XOR-bit soundness.** The XOR gadget (`crates/xark-bits/src/lib.rs`) emits `(2·a) · b = a + b − out`
(with `out` separately boolean-enforced). Given the inputs are boolean, this
constraint pins `out` to `a + b − 2ab`, which is boolean and is exactly XOR:
`out = 0 ↔ a = b`. -/
theorem xor_sound {F : Type*} [Field F] (a b out : F)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (h : (2 * a) * b = a + b - out) :
    (out = 0 ∨ out = 1) ∧ (out = 0 ↔ a = b) := by
  -- The constraint rearranges to pin `out` uniquely (determinism).
  have hout : out = a + b - 2 * (a * b) := by linear_combination h
  refine ⟨?_, ?_⟩ <;>
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rw [hout] <;> norm_num

/-- **NOT-bit soundness.** The NOT gadget (`crates/xark-bits/src/lib.rs`) represents the complement as the
LC `1 − a`. Given `a` is boolean, `1 − a` is boolean and is logical NOT
(`1 − a = 1 ↔ a = 0`). -/
theorem not_sound {F : Type*} [Field F] (a : F) (ha : a = 0 ∨ a = 1) :
    ((1 - a) = 0 ∨ (1 - a) = 1) ∧ ((1 - a) = 1 ↔ a = 0) := by
  rcases ha with rfl | rfl <;> refine ⟨?_, ?_⟩ <;> norm_num

end Xark
