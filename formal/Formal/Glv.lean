/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Ecdsa
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# GLV + fixed-base comb + 2-way joint Strauss-Shamir

`crates/acir-r1cs/src/gadgets/ecdsa.rs::scalar_mul_2p_secp256k1_comb_glv`
computes `u₁ · G + u₂ · Q` for ECDSA verification on secp256k1 via three
combined optimisations: (1) GLV decomposition for the variable-base term,
(2) a fixed-base comb table for `u₁ · G`, and (3) 2-way joint
Strauss-Shamir interleaving.

This file establishes the **algebraic soundness** of (1) and the
**endomorphism interface** for the GLV trick over any additive commutative
group `G`. The joint loop and the comb-table-correctness theorems
(`windowed_scalar_mul_sound`, `joint_strauss_shamir_correct`) live in
`Formal.AdvancedGadgets` and are fully proved there.

## Theorem index

| Name                                | Statement |
|-------------------------------------|-----------|
| `glv_sum_eq`                        | `k₁ • P + k₂ • (λ • P) = (k₁ + λ·k₂) • P` (proven) |
| `IsEndomorphism`                    | `φ : G → G` is an endomorphism with eigenvalue `λ` |
| `glv_via_endomorphism`              | combines the above: `k₁ • P + k₂ • φ(P) = (k₁ + λ·k₂) • P` (proven) |
| `glv_endomorphism_correct`          | secp256k1's `φ(P) = (β·P.x mod p, P.y) = λ·P` (concrete instance in `Formal.Secp256k1Group`) |
| `glv_decomposition_mod_n_sound`     | `k₁ + λ·k₂ ≡ k (mod n) ∧ n • P = 0 ⇒ (k₁ + λ·k₂) • P = k • P` (proven) |
| `windowed_scalar_mul_sound`         | comb table reconstructs `s • G` (in `Formal.AdvancedGadgets`) |
| `joint_strauss_shamir_correct`      | 2-way joint loop = `u₁ • G + u₂ • Q` (in `Formal.AdvancedGadgets`) |
-/

namespace Xark

/-! ## GLV decomposition — algebraic content -/

/-- **GLV decomposition identity** (group-theoretic). For any additive
commutative group `G`, any point `P : G`, scalars `k₁ k₂ : ℕ`, and
endomorphism eigenvalue `λ : ℕ`:

    `k₁ • P + k₂ • (λ • P) = (k₁ + λ · k₂) • P`.

This is the heart of GLV: an integer scalar `k = k₁ + λ · k₂` can be split
into two scalars and the multiplication evaluated as a sum of two
scalar-mults of `P` and `φ(P) = λ · P`. -/
theorem glv_sum_eq {G : Type*} [AddCommGroup G] (P : G) (k1 k2 lam : ℕ) :
    k1 • P + k2 • (lam • P) = (k1 + lam * k2) • P := by
  rw [← mul_nsmul', add_nsmul]
  ring_nf

/-- **Endomorphism predicate.** `IsEndomorphism φ λ` says that `φ : G → G`
is a map satisfying `φ(P) = λ · P` for all points `P`. For secp256k1,
`φ(P) = (β · P.x mod p, P.y)` realises this with the documented `λ`
(`secp256k1_lambda`). -/
def IsEndomorphism {G : Type*} [AddCommGroup G] (φ : G → G) (lam : ℕ) : Prop :=
  ∀ P : G, φ P = lam • P

/-- **GLV via the endomorphism.** Combines `glv_sum_eq` and
`IsEndomorphism` into the user-facing form: if `φ` is the documented
endomorphism, then `k₁ • P + k₂ • φ(P) = (k₁ + λ · k₂) • P`.

This is the algebraic identity the gadget exploits: the gadget computes
`k₁ • P + k₂ • φ(P)` via 129-bit scalar mults (one per half), saving
~128 doublings vs `(k₁ + λ · k₂) • P` directly. -/
theorem glv_via_endomorphism {G : Type*} [AddCommGroup G]
    (φ : G → G) (lam : ℕ) (h_endo : IsEndomorphism φ lam)
    (P : G) (k1 k2 : ℕ) :
    k1 • P + k2 • (φ P) = (k1 + lam * k2) • P := by
  rw [h_endo P]
  exact glv_sum_eq P k1 k2 lam

/-! ## Endomorphism correctness — algebraic kernel

`glv_endomorphism_correct` proves the algebraic kernel of GLV correctness:
in any additive commutative group `G`, if `φ : G → G` is a group
homomorphism and the eigenvalue relation `φ(P) = λ • P` holds at *one*
point `P`, then it holds at every multiple `k • P` — i.e. `φ`
restricted to the cyclic subgroup ⟨`P`⟩ is precisely scalar
multiplication by `λ`. This is the property the gadget exploits over the
secp256k1 generator's cyclic subgroup of order `n = secp256k1_n`.

Once `Formal.Secp256k1Group.Secp256k1Point` is in scope, this
theorem specialises to the concrete claim `φ(P) = λ · P` for the
secp256k1 endomorphism `φ(x, y) = (β · x mod p, y)` by:

1. exhibiting `φ` as a group endomorphism (one-step structural proof
   from the secp256k1 addition law), and
2. computing `φ(G) = λ • G` for the curve generator (a finite check). -/

/-- **`glv_endomorphism_correct` (algebraic kernel).**
Given a group homomorphism `φ : G → G` on an additive commutative group
`G`, an eigenvalue `λ : ℕ`, and a point `P : G` for which the eigenvalue
relation `φ(P) = λ • P` holds, the relation extends to every multiple of
`P` — `φ(k • P) = λ • (k • P)` for all `k : ℕ`.

Composed with `glv_via_endomorphism`, this discharges the GLV decomposition
in any cyclic subgroup containing the secp256k1 generator: prover supplies
`(k₁, k₂)` with `k₁ + λ·k₂ ≡ k (mod n)`, and the gadget computes
`k₁ • P + k₂ • φ(P) = k • P` modulo the subgroup. -/
theorem glv_endomorphism_correct {G : Type*} [AddCommGroup G]
    (φ : G → G)
    (h_hom : ∀ a b : G, φ (a + b) = φ a + φ b)
    (h_zero : φ 0 = 0)
    (P : G) (lam : ℕ) (h_eig : φ P = lam • P) :
    ∀ k : ℕ, φ (k • P) = lam • (k • P) := by
  intro k
  induction k with
  | zero =>
    simp [h_zero]
  | succ n ih =>
    -- `(n+1) • P = n • P + P`. By homomorphism + IH + eigenvalue:
    -- `φ((n+1)•P) = φ(n•P) + φ(P) = (λ•(n•P)) + (λ•P) = λ•((n+1)•P)`.
    rw [succ_nsmul, h_hom, ih, h_eig, ← smul_add, ← succ_nsmul]

/-- **Endomorphism-homomorphism corollary.** A group endomorphism that
satisfies the eigenvalue relation at a single generator gives an
`IsEndomorphism` instance over the cyclic subgroup it generates. -/
theorem isEndomorphism_of_eigenvalue_at_generator {G : Type*} [AddCommGroup G]
    (φ : G → G)
    (h_hom : ∀ a b : G, φ (a + b) = φ a + φ b)
    (h_zero : φ 0 = 0)
    (P : G) (lam : ℕ) (h_eig : φ P = lam • P) :
    ∀ k : ℕ, φ (k • P) = lam • (k • P) :=
  glv_endomorphism_correct φ h_hom h_zero P lam h_eig

/-! ## Endomorphism correctness for secp256k1

The concrete secp256k1 endomorphism is `φ(x, y) = (β · x mod p, y)` where
`β` is a specific cube root of unity mod `p`. The statement
`∀ P ∈ secp256k1, φ(P) = λ · P` is discharged in
`Formal.Secp256k1Group` (`secp256k1_phi_hom`,
`secp256k1_phi_eigenvalue_at_G`, `secp256k1_phi_acts_as_lambda`) against
the `Secp256k1Point` `AddCommGroup` instance. -/

/-- **secp256k1 GLV-relation soundness (algebraic).** The prover supplies
`(k₁, k₂)` such that `k₁ + λ · k₂ ≡ k (mod n)` over ℤ where `n` is the
secp256k1 scalar order. This integer identity is exactly what
`ecdsa.rs::glv_decompose_native` enforces (via the non-native modular
constraint chain `Formal.NonNative.mul_mod_via_Fr_limbwise_constraints`).

Given the integer identity and a group `G` with `n • P = 0` (curve group
order divides `n`), `(k₁ + λ · k₂) • P = k • P`. -/
theorem glv_decomposition_mod_n_sound {G : Type*} [AddCommGroup G] (P : G)
    (n k k1 k2 lam : ℕ)
    (h_ord : n • P = 0)
    (h_rel : k1 + lam * k2 ≡ k [MOD n]) :
    (k1 + lam * k2) • P = k • P := by
  -- Any natural-number multiple reduces mod `n` under `n • P = 0`: split
  -- `m = m / n * n + m % n`; `mul_nsmul' P (m/n) n` rewrites the
  -- `(m / n * n) • P` chunk as `(m / n) • (n • P) = (m / n) • 0 = 0`.
  have h_reduce : ∀ m : ℕ, m • P = (m % n) • P := by
    intro m
    conv_lhs =>
      rw [show m = m / n * n + m % n from (Nat.div_add_mod' m n).symm,
          add_nsmul, mul_nsmul', h_ord, nsmul_zero, zero_add]
  rw [h_reduce (k1 + lam * k2), h_reduce k]
  exact congrArg (· • P) h_rel

/-! ## Fixed-base comb table + 2-way joint Strauss-Shamir

The full algebraic correctness statements for the comb-scan fixed-base
table and the 2-way interleaved Strauss-Shamir ladder live in
`Formal.AdvancedGadgets` (`windowed_scalar_mul_sound` and
`joint_strauss_shamir_correct`), depending only on the same
`AddCommGroup` interface used in this file. -/

end Xark
