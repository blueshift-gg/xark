/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Gadgets
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- The `style.header` linter hard-codes mathlib's Apache license string; this is
-- an MIT project, so disable that house-style check (it is not a correctness lint).
set_option linter.style.header false

/-!
# Carry arithmetic — mechanised in Lean 4 / mathlib

Two carry lemmas:

* N-ary parity `Σⱼ bⱼ = out + 2·k`. No current gadget emits this form
  (`xark_bits::xor3`, `maj3` and `chi` are single-row forms proven in
  `Formal/HashOps.lean`; `Field::xor` is one fused row); a general lemma.
* Wrapping 32-bit addition `Σ inputs = result + 2³²·carry`: the arithmetic
  behind `xark_bits::add32` (a 33-bit decomposition of the sum) and
  `xark_bits::reduce::<N>`, whose exported rows are proven in
  `Formal/Add32.lean` and `Formal/Reduce.lean`.

The content beyond `Gadgets.lean`/`Bitwise.lean` is the *carry arithmetic*:
that a small range-checked carry, plus a bounded sum that cannot wrap the
modulus `r`, forces the output to be the parity (resp. the low 32 bits) of the
inputs and pins it uniquely. We prove the pure-`ℕ` core and, for parity, the
field-level lift over `ZMod r`, reusing the no-wrap pattern of `range_unique`.
-/

namespace Xark

/-! ## N-ary XOR (parity) -/

/-- **Parity core (ℕ).** Given
`Σⱼ bⱼ = out + 2·k` with the output bit `out ∈ {0,1}` and `k` a range-checked
carry. Then `out` is exactly the parity of the input-bit sum — and is therefore
uniquely determined. -/
theorem xor_n_parity_core {n : ℕ} (β : Fin n → ℕ) (out k : ℕ)
    (hout : out ≤ 1) (h : (∑ i, β i) = out + 2 * k) :
    out = (∑ i, β i) % 2 := by
  omega

/-- **Parity, field-level.** The lift of `xor_n_parity_core` to the `ZMod r`
constraint. With the input bits and output bit boolean, the
carry equal to a natural number `kn` (its range decomposition), and the two
nat sums below the modulus (no wrap — trivially true for small `n`), the
field constraint
`Σⱼ bⱼ = out + 2·kn` forces the output bit to be the input parity. -/
theorem xor_n_parity_field {n : ℕ} (b : Fin n → ZMod r) (out : ZMod r) (kn : ℕ)
    (hb : ∀ i, b i = 0 ∨ b i = 1) (hout : out = 0 ∨ out = 1)
    (hwrap : (∑ i, toBit (b i)) < r) (hwrap2 : toBit out + 2 * kn < r)
    (h : (∑ i, b i) = out + 2 * (kn : ZMod r)) :
    toBit out = (∑ i, toBit (b i)) % 2 := by
  set S := ∑ i : Fin n, toBit (b i) with hS
  -- Both sides of the constraint are casts of their nat values.
  have castS : (S : ZMod r) = ∑ i, b i := by
    rw [hS]; push_cast
    apply Finset.sum_congr rfl; intro i _; rw [cast_toBit (hb i)]
  have castR : ((toBit out + 2 * kn : ℕ) : ZMod r) = out + 2 * (kn : ZMod r) := by
    push_cast; rw [cast_toBit hout]
  have hfield : (S : ZMod r) = ((toBit out + 2 * kn : ℕ) : ZMod r) := by
    rw [castS, castR, h]
  -- Lift to ℕ (no wrap), then it is pure parity.
  have hmod := (ZMod.natCast_eq_natCast_iff S (toBit out + 2 * kn) r).mp hfield
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt hwrap, Nat.mod_eq_of_lt hwrap2] at hmod
  have hout1 : toBit out ≤ 1 := toBit_le_one out
  omega

/-! ## Wrapping 32-bit addition -/

/-- **Wrapping-add core (ℕ).** Given
`Σ inputs = result + 2³²·carry` with the 32 result bits boolean, so
`result < 2³²`. Hence the result is the inputs' sum reduced mod `2³²` — the
wrapping add — and is uniquely determined by the inputs. (The 32 result *bits*
are then pinned by `bits_unique`.) -/
theorem add_mod_32_core (S R C : ℕ) (hR : R < 2 ^ 32) (h : S = R + 2 ^ 32 * C) :
    R = S % 2 ^ 32 := by
  have e : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  rw [e] at hR h ⊢
  omega

/-- The result is **uniquely determined**: any two wrapping-add results for
the same input sum coincide. Immediate from `add_mod_32_core` (both equal
`S % 2³²`). -/
theorem add_mod_32_unique (S R R' C C' : ℕ)
    (hR : R < 2 ^ 32) (hR' : R' < 2 ^ 32)
    (h : S = R + 2 ^ 32 * C) (h' : S = R' + 2 ^ 32 * C') :
    R = R' := by
  rw [add_mod_32_core S R C hR h, add_mod_32_core S R' C' hR' h']

end Xark
