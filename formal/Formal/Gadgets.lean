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
# xark gadget soundness — mechanised in Lean 4 / mathlib

Machine-checked soundness lemmas for the R1CS gadgets emitted by
`crates/acir-r1cs`. Each theorem mirrors the *exact* constraints the Rust
builder enforces, so a proof here is a statement about the real circuit.

* `boolean_sound` — mirrors `gadgets/boolean.rs::enforce_boolean`, which
  enforces `b * (b - 1) = 0`. We prove that this holds **iff** `b ∈ {0, 1}`,
  in any field (more generally any ring with no zero divisors). This is the
  primitive every other gadget builds on (range, bitwise, the hashes all
  pin their wires to {0,1} this way).

* `range_unique` — mirrors `gadgets/range.rs::decompose_into_bits`, which
  allocates `n` boolean wires `bᵢ` and enforces `Σᵢ 2ⁱ·bᵢ = value`. We prove
  the gadget is **functionally deterministic**: the bit-vector is *uniquely*
  determined by `value` — i.e. the R1CS has no under-constraint slack — as
  long as the width `n ≤ 253 < log₂ r`, so the field sum cannot wrap the
  BN254 scalar modulus. Under-constraint is the precise bug class these
  proofs target, and this discharges it for the range gadget over *all* field
  assignments.
-/

namespace Xark

/-- **`enforce_boolean` soundness.** The single constraint
`b * (b - 1) = 0` emitted by `gadgets/boolean.rs` holds exactly when `b` is a
boolean field element. Stated for any ring with no zero divisors (every field,
in particular `ark_bn254::Fr`). -/
theorem boolean_sound {F : Type*} [Ring F] [NoZeroDivisors F] (b : F) :
    b * (b - 1) = 0 ↔ b = 0 ∨ b = 1 := by
  rw [mul_eq_zero, sub_eq_zero]

/-- BN254 scalar field order `r` — the modulus of `ark_bn254::Fr`. -/
def r : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

instance : NeZero r := ⟨by unfold r; norm_num⟩
instance : Fact (1 < r) := ⟨by unfold r; norm_num⟩

/-- `2^253 < r`: the width cap `MAX_BITS = 253` in `gadgets/range.rs` keeps an
`n`-bit recomposition (`n ≤ 253`) strictly below the modulus, so it cannot wrap. -/
theorem two_pow_lt_r : (2 : ℕ) ^ 253 < r := by unfold r; norm_num

/-- A `{0,1}` field element of `ZMod r` as a natural-number bit (`0` or `1`). -/
def toBit (x : ZMod r) : ℕ := if x = 1 then 1 else 0

theorem toBit_le_one (x : ZMod r) : toBit x ≤ 1 := by
  unfold toBit; split <;> simp

/-- The nat-bit casts back to the field element, when the wire is boolean. -/
theorem cast_toBit {x : ZMod r} (hx : x = 0 ∨ x = 1) : ((toBit x : ℕ) : ZMod r) = x := by
  unfold toBit
  rcases hx with h | h <;> subst h <;> simp

/-- **Binary-representation uniqueness over `ℕ`.** If two bit-vectors of width
`n` have the same weighted sum `Σᵢ 2ⁱ·βᵢ`, they are equal. This is the
combinatorial core of range-gadget determinism: the recomposition is injective
on bit-vectors. Proved by induction on `n`, peeling the low bit via parity. -/
theorem bits_unique :
    ∀ {n : ℕ} (β γ : Fin n → ℕ), (∀ i, β i ≤ 1) → (∀ i, γ i ≤ 1) →
      (∑ i : Fin n, 2 ^ (i.val) * β i = ∑ i : Fin n, 2 ^ (i.val) * γ i) → β = γ := by
  intro n
  induction n with
  | zero => intro β γ _ _ _; funext i; exact i.elim0
  | succ m ih =>
    intro β γ hβ hγ hsum
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hsum
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ] at hsum
    -- Factor the shared `2` out of each tail sum.
    have e : ∀ (δ : Fin (m + 1) → ℕ),
        (∑ i : Fin m, 2 ^ (i.val) * 2 * δ i.succ)
          = 2 * (∑ i : Fin m, 2 ^ (i.val) * δ i.succ) := by
      intro δ; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [e β, e γ] at hsum
    have hβ0 : β 0 ≤ 1 := hβ 0
    have hγ0 : γ 0 ≤ 1 := hγ 0
    -- Parity peels the low bit; the boolean bound makes it exact, then the
    -- doubled tails are equal as well.
    have hlow : β 0 = γ 0 := by omega
    have htail : (∑ i : Fin m, 2 ^ (i.val) * β i.succ)
               = (∑ i : Fin m, 2 ^ (i.val) * γ i.succ) := by omega
    have htails := ih (fun i => β i.succ) (fun i => γ i.succ)
      (fun i => hβ i.succ) (fun i => hγ i.succ) htail
    funext i
    refine Fin.cases ?_ ?_ i
    · exact hlow
    · intro j; exact congrFun htails j

/-- **`decompose_into_bits` determinism / soundness.** Given the boolean
constraints on every bit (`hb`, `hb'`) and the recomposition constraint
`Σᵢ 2ⁱ·bᵢ = Σᵢ 2ⁱ·b'ᵢ` (both equal to the same `value` wire), the two
bit-vectors coincide — for any width `n ≤ 253`. The range gadget therefore
pins its witness uniquely: no prover has slack to choose a different
decomposition of the same value. The bound `n ≤ 253` is exactly the Rust
`MAX_BITS` cap, and is what prevents a field wrap-around from collapsing two
distinct bit-vectors onto one value. -/
theorem range_unique {n : ℕ} (hn : n ≤ 253)
    (b b' : Fin n → ZMod r)
    (hb : ∀ i, b i = 0 ∨ b i = 1) (hb' : ∀ i, b' i = 0 ∨ b' i = 1)
    (hsum : ∑ i : Fin n, (2 : ZMod r) ^ (i.val) * b i
          = ∑ i : Fin n, (2 : ZMod r) ^ (i.val) * b' i) :
    b = b' := by
  -- The pure-`ℕ` weighted bit sums.
  set N := ∑ i : Fin n, 2 ^ (i.val) * toBit (b i) with hN
  set M := ∑ i : Fin n, 2 ^ (i.val) * toBit (b' i) with hM
  -- `Σ 2ⁱ < 2ⁿ`.
  have hsum_pow : (∑ i : Fin n, (2 : ℕ) ^ (i.val)) < 2 ^ n := by
    have heq : (∑ i : Fin n, (2 : ℕ) ^ (i.val)) = 2 ^ n - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) n, Nat.geomSum_eq (by norm_num) n]
      simp
    rw [heq]
    exact Nat.sub_lt (pow_pos (by norm_num) n) Nat.one_pos
  -- Each nat sum is `< 2ⁿ ≤ 2²⁵³ < r`.
  have bound : ∀ (f : Fin n → ZMod r),
      (∑ i : Fin n, 2 ^ (i.val) * toBit (f i)) < 2 ^ n := by
    intro f
    have h1 : (∑ i : Fin n, 2 ^ (i.val) * toBit (f i)) ≤ ∑ i : Fin n, 2 ^ (i.val) := by
      apply Finset.sum_le_sum; intro i _
      calc 2 ^ (i.val) * toBit (f i) ≤ 2 ^ (i.val) * 1 := by gcongr; exact toBit_le_one (f i)
        _ = 2 ^ (i.val) := by rw [mul_one]
    exact lt_of_le_of_lt h1 hsum_pow
  have hbound : (2 : ℕ) ^ n ≤ r :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hn) (le_of_lt two_pow_lt_r)
  have hNr : N < r := lt_of_lt_of_le (bound b) hbound
  have hMr : M < r := lt_of_lt_of_le (bound b') hbound
  -- The field sums are the casts of the nat sums.
  have castN : (N : ZMod r) = ∑ i : Fin n, (2 : ZMod r) ^ (i.val) * b i := by
    rw [hN]; push_cast
    apply Finset.sum_congr rfl; intro i _; rw [cast_toBit (hb i)]
  have castM : (M : ZMod r) = ∑ i : Fin n, (2 : ZMod r) ^ (i.val) * b' i := by
    rw [hM]; push_cast
    apply Finset.sum_congr rfl; intro i _; rw [cast_toBit (hb' i)]
  -- Equal field values ⇒ equal nat values (both below the modulus).
  have castEq : (N : ZMod r) = (M : ZMod r) := by rw [castN, castM, hsum]
  have hmod : N ≡ M [MOD r] := (ZMod.natCast_eq_natCast_iff N M r).mp castEq
  have hNM : N = M := by
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt hNr, Nat.mod_eq_of_lt hMr] at hmod
  -- Nat-level binary uniqueness ⇒ the bits agree, hence the field wires agree.
  have hbits := bits_unique (fun i => toBit (b i)) (fun i => toBit (b' i))
    (fun i => toBit_le_one (b i)) (fun i => toBit_le_one (b' i)) hNM
  funext i
  have hi : toBit (b i) = toBit (b' i) := congrFun hbits i
  rw [← cast_toBit (hb i), ← cast_toBit (hb' i), hi]

end Xark
