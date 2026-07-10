/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib
import Formal.Gadgets

-- The `style.header` linter hard-codes mathlib's Apache license string; this is
-- an MIT project, so disable that house-style check (it is not a correctness lint).
set_option linter.style.header false

/-!
# xark non-native modular-product soundness — mechanised in Lean 4 / mathlib

The ECDSA verifier in `crates/xark-secp256k1/src/lib.rs` evaluates the
secp256k1 base- and scalar-field arithmetic *inside* a BN254 R1CS. Both
secp256k1 moduli are 256 bits wide and do not fit in BN254 `Fr` (~254 bits),
so every non-native multiplication `c = a · b mod m` is lowered via the
**prover-aided identity** pattern: the prover supplies the quotient `q` and
remainder `c`, and the circuit checks the *integer* identity

    a · b = q · m + c

limb-by-limb (`β = 2^86`, three limbs per 256-bit value) while a separate
range gadget pins `0 ≤ c < m` by bit-decomposing `c`. This pattern is reused
verbatim by `inv_mod` (`a · a⁻¹ = 1 mod m`) and by every affine point-add /
point-double / scalar-mul step that feeds into the ECDSA verifier.

We prove the *abstract* soundness of this pattern over `ℕ`: that the integer
identity together with the range check on `c` already forces `c` to be the
unique modular product. Concretely:

* `mul_mod_sound` — the headline lemma. If `0 < m`, `c < m`, and
  `a · b = q · m + c` as natural numbers, then `c = (a · b) % m`. This is
  what the prover-aided identity actually *buys*: the limb-by-limb integer
  check plus the bit-decomposition range check fully pin the modular product;
  the prover has no remaining slack in `c`.
* `mul_mod_complete` — the matching completeness statement: a valid
  `(q, c)` always exists, namely the division-algorithm pair
  `(a*b / m, a*b % m)`. Confirms the gadget admits all honest witnesses.
* `valOfLimbs` / `valOfLimbs_zero` / `valOfLimbs_succ` — the limb-recomposition
  function `Σᵢ ls i · β^i` for an `n`-limb vector indexed by `Fin n`, plus the
  base / cons-style identities that let limbwise statements compose with
  whole-integer statements.
* `mul_mod_via_limbs` — the gluing theorem: applying `mul_mod_sound` to the
  recomposed limb values. State: given limb vectors `a, b, q, c, m : Fin n → ℕ`
  whose recomposed integer values satisfy the identity
  `valOfLimbs a · valOfLimbs b = valOfLimbs q · valOfLimbs m + valOfLimbs c`
  and `valOfLimbs c < valOfLimbs m`, then
  `valOfLimbs c = (valOfLimbs a · valOfLimbs b) % valOfLimbs m`. This is the
  exact shape the limb-by-limb constraints are designed to discharge.

Scope: this file proves the abstract step "integer identity + remainder
range ⇒ modular product" *and* the carry-no-wrap step that lifts the per-column
limb-by-limb `Fr` constraints emitted by `mul_mod` to the integer identity over
ℕ. Concretely, beyond the abstract pieces above, we also prove:

* `colSum` / `colSum_eq` — the schoolbook column-sum (Cauchy product) identity:
  the product of two limb-recomposed values equals `Σₖ colSum a b k · β^k`,
  where `colSum a b k = Σ_{i ≤ k} aᵢ · b_{k−i}`. This is the polynomial step
  underlying limbwise multiplication.
* `colSum_carry_telescope` — the carry-telescoping theorem: if for every column
  `k < 2n` the per-column constraint
  `colSum a b k + carry k = colSum_qm k + β · carry (k+1)` holds, with
  `carry 0 = 0` and `carry (2n) = 0`, then `Σₖ colSum a b k · β^k = Σₖ colSum_qm k · β^k`.
  The carry tower cancels by telescoping, so the column-by-column field equations
  (no carry wrap modeled as carries being plain ℕ) force the polynomial equality.
* `mul_mod_via_limbwise_constraints` — the gluing theorem. Given limb vectors
  `a, b, q, c, m : Fin n → ℕ` and a carry function `carry : ℕ → ℕ` satisfying the
  per-column equations together with `valOfLimbs c β < valOfLimbs m β` and
  `0 < valOfLimbs m β`, then `valOfLimbs c β = (valOfLimbs a β · valOfLimbs b β) % valOfLimbs m β`.
  This is the **full soundness chain** for the non-native `mod_mul` gadget
  (`crates/xark-bignum/src/lib.rs`): limb-by-limb
  constraints + carry-no-wrap ⇒ modular product is correct.

The "no carry wrap" hypothesis is captured by the carries being natural numbers
in the proof (rather than `Fr` field elements); the corresponding circuit-level
range check on each carry is the gadget-side obligation, the analogue of
`range_unique` in `Formal.Gadgets`.

In addition, this file proves the **Fr-level no-wrap argument** that
discharges the gap between the `ℕ`-valued statement above and the actual
`Fr = ZMod r`-valued column equations emitted by the gadget. Concretely:

* `add_val_no_wrap` / `mul_val_no_wrap` — the `ZMod r ↔ ℕ` bridge: under
  per-operand value bounds that keep the sum / product strictly below `r`, the
  `Fr`-arithmetic agrees with `ℕ`-arithmetic on `.val`.
* `colSum_le` — the column-sum budget bound: for `n`-limb vectors with each
  limb strictly bounded by `β`, every column `colSum a b k ≤ n · (β − 1)²`.
* `carry_le` — the carry-budget bound: assuming the per-column ℕ-equation, the
  `k`-th carry stays below `(k + 1) · n · (β − 1)²`.
* `mul_mod_via_Fr_limbwise_constraints` — the headline theorem for the
  secp256k1 concrete shape (`n = 3`, `β = 2 ^ 86`): from the per-column
  equations holding in `Fr` together with the limb / carry value bounds
  (the in-circuit range obligation), the integer-level conclusion of
  `mul_mod_via_limbwise_constraints` follows. The budget chain keeps every
  column expression far below the BN254 modulus `r`, so no field wrap occurs.
-/

namespace Xark

/-! ## Abstract prover-aided identity (over `ℕ`) -/

/-- **Prover-aided modular product, soundness.** If the prover supplies `(q, c)`
satisfying the *integer* identity `a · b = q · m + c` and the gadget's bit
decomposition pins `c < m` (with `m` positive — vacuous for the secp256k1
base / scalar moduli, which are large primes), then `c` is exactly the modular
product `(a · b) % m`. This is the abstract content of what the non-native
`mod_mul` gadget (`crates/xark-bignum/src/lib.rs`) enforces. -/
theorem mul_mod_sound (a b q c m : ℕ) (hc : c < m)
    (h : a * b = q * m + c) :
    c = (a * b) % m := by
  rw [h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-- **Prover-aided modular product, completeness.** For any inputs `a, b` and
any positive modulus `m`, the division-algorithm pair
`(q, c) = (a * b / m, a * b % m)` satisfies the integer identity
`a · b = q · m + c` with `c < m`. So every honest evaluation is admissible —
the gadget rejects no valid signature for lack of a witness. -/
theorem mul_mod_complete (a b m : ℕ) (hm : 0 < m) :
    ∃ q c, c < m ∧ a * b = q * m + c := by
  refine ⟨(a * b) / m, (a * b) % m, Nat.mod_lt _ hm, ?_⟩
  rw [Nat.mul_comm ((a * b) / m) m]
  exact (Nat.div_add_mod (a * b) m).symm

/-! ## Limb recomposition -/

/-- The integer value of an `n`-limb little-endian vector with limb base `β`:
`valOfLimbs ls β = Σᵢ ls i · β^i`. Models the in-circuit reconstruction
`Σᵢ β^i · limbᵢ` emitted by the limb recomposition in `crates/xark-bignum/src/lib.rs`, but
phrased generically over the number of limbs and over an arbitrary base.
The secp256k1 lowering instantiates `n = 3`, `β = 2 ^ 86`. -/
def valOfLimbs {n : ℕ} (ls : Fin n → ℕ) (β : ℕ) : ℕ :=
  ∑ i : Fin n, ls i * β ^ (i : ℕ)

/-- An empty limb vector recomposes to `0`. The degenerate `n = 0` base case
that makes `valOfLimbs_succ` go through cleanly. -/
theorem valOfLimbs_zero (ls : Fin 0 → ℕ) (β : ℕ) :
    valOfLimbs ls β = 0 := by
  unfold valOfLimbs
  exact Finset.sum_empty

/-- **Cons-style recomposition identity.** A length-`n+1` limb vector splits
into its `0`-th limb plus `β` times the recomposition of the tail. This is the
single inductive step you need to fold any limbwise statement into a whole-value
statement (e.g. for the `n = 3` secp256k1 case). -/
theorem valOfLimbs_succ {n : ℕ} (ls : Fin (n + 1) → ℕ) (β : ℕ) :
    valOfLimbs ls β
      = ls 0 + β * valOfLimbs (fun i : Fin n => ls i.succ) β := by
  unfold valOfLimbs
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## Gluing: limbwise identity ⇒ modular product -/

/-- **Limbwise prover-aided modular product.** Specialises `mul_mod_sound` to
limb-vector inputs. If the limb-recomposed values of `a, b, q, c, m` satisfy
the integer identity
`valOfLimbs a · valOfLimbs b = valOfLimbs q · valOfLimbs m + valOfLimbs c`
and `valOfLimbs c < valOfLimbs m`, then `valOfLimbs c` is the modular product.
This is the exact statement the limb-by-limb `Fr` constraints in `mul_mod` are
designed to discharge — once those constraints are shown to sum to the integer
identity (separate work, see the module docstring), this lemma closes the
soundness story for the non-native multiplication primitive. -/
theorem mul_mod_via_limbs {n : ℕ} (a b q c m : Fin n → ℕ) (β : ℕ)
    (_hm : 0 < valOfLimbs m β) (hc : valOfLimbs c β < valOfLimbs m β)
    (h : valOfLimbs a β * valOfLimbs b β
          = valOfLimbs q β * valOfLimbs m β + valOfLimbs c β) :
    valOfLimbs c β = (valOfLimbs a β * valOfLimbs b β) % valOfLimbs m β :=
  mul_mod_sound _ _ _ _ _ hc h

/-! ## Carry-no-wrap: column sums and the schoolbook product identity -/

/-- The recomposed value of an `n`-limb little-endian vector, phrased in the
`ℕ → ℕ` style (rather than `Fin n → ℕ`) so it composes cleanly with the
column-sum / Cauchy-product machinery below. Equal to `valOfLimbs` for limb
functions that vanish outside `[0, n)`. -/
def valOfNatLimbs (a : ℕ → ℕ) (n β : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, a i * β ^ i

/-- **Column sum (partial product) of two limb sequences.**
`colSum a b k = Σ_{i ≤ k} aᵢ · b_{k−i}` — the `k`-th column of the schoolbook
multiplication table. The ECDSA `mul_mod` gadget enforces, per output column,
an equation that compares `colSum a b k` against `colSum (q·m + c)-limbs k` up
to a propagating carry. -/
def colSum (a b : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), a i * b (k - i)

/-- **Schoolbook (Cauchy) product identity for limb-recomposed values.**
The product of two `n`-limb recompositions equals the `β`-weighted sum of column
sums, summed over columns `k ∈ [0, 2n)`. Standard Cauchy-product identity
proven by partitioning the index pair `(i, j)` by its sum `k = i + j` via
`Finset.sum_fiberwise_of_maps_to` and reading the inner sum as `colSum a b k`
under the support hypothesis. -/
theorem colSum_eq (a b : ℕ → ℕ) (n β : ℕ)
    (ha : ∀ i ≥ n, a i = 0) (hb : ∀ j ≥ n, b j = 0) :
    valOfNatLimbs a n β * valOfNatLimbs b n β
      = ∑ k ∈ Finset.range (2 * n), colSum a b k * β ^ k := by
  unfold valOfNatLimbs colSum
  -- Step 1: expand the product to a sum over `range n ×ˢ range n`.
  have h1 :
      (∑ i ∈ Finset.range n, a i * β ^ i) * (∑ j ∈ Finset.range n, b j * β ^ j)
        = ∑ p ∈ Finset.range n ×ˢ Finset.range n, a p.1 * b p.2 * β ^ (p.1 + p.2) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr rfl; intro p _
    rw [pow_add]; ring
  rw [h1]
  -- Step 2: partition the product set by `k = p.1 + p.2`, using fiberwise summation.
  have hmaps : ∀ p ∈ (Finset.range n ×ˢ Finset.range n),
      p.1 + p.2 ∈ Finset.range (2 * n) := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Finset.mem_range] at hp1 hp2 ⊢; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun p : ℕ × ℕ => a p.1 * b p.2 * β ^ (p.1 + p.2))]
  -- Step 3: For each column `k`, show the fiber sum equals `colSum a b k * β^k`.
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  -- Show fiber sum equals colSum a b k * β^k after factoring β^k.
  -- Strategy: split RHS as in-range ∪ out-of-range; the latter vanishes by ha/hb;
  -- the former bijects with the fiber via `i ↦ (i, k - i)`.
  -- Actually, simpler: show the equation pointwise via two sum rewrites.
  -- First, rewrite the fiber-side β^(p.1 + p.2): for p in the filter, p.1 + p.2 = k.
  have fiber_rewrite :
      ∑ p ∈ (Finset.range n ×ˢ Finset.range n) with p.1 + p.2 = k,
          a p.1 * b p.2 * β ^ (p.1 + p.2)
        = ∑ p ∈ (Finset.range n ×ˢ Finset.range n) with p.1 + p.2 = k,
            a p.1 * b p.2 * β ^ k := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hp.2]
  rw [fiber_rewrite]
  -- Now both sides have β^k as the trailing factor; factor it out and reduce to base-sum equality.
  rw [show
        (∑ p ∈ (Finset.range n ×ˢ Finset.range n) with p.1 + p.2 = k,
            a p.1 * b p.2 * β ^ k)
          = (∑ p ∈ (Finset.range n ×ˢ Finset.range n) with p.1 + p.2 = k,
              a p.1 * b p.2) * β ^ k from (Finset.sum_mul _ _ _).symm]
  rw [show
        (∑ i ∈ Finset.range (k + 1), a i * b (k - i) * β ^ k)
          = (∑ i ∈ Finset.range (k + 1), a i * b (k - i)) * β ^ k from
        (Finset.sum_mul _ _ _).symm]
  congr 1
  -- Goal: ∑ p ∈ (range n ×ˢ range n) with p.1 + p.2 = k, a p.1 * b p.2
  --       = ∑ i ∈ range (k+1), a i * b (k - i)
  -- Drop out-of-range terms on RHS (those with `i ≥ n` or `k - i ≥ n` give zero), then
  -- bijection: fiber over k  ↔  (range (k+1)).filter (i < n ∧ k - i < n).
  classical
  -- The fiber set: {p ∈ range n ×ˢ range n | p.1 + p.2 = k}.
  -- The relevant subset of range (k+1): {i ∈ range (k+1) | i < n ∧ k - i < n}.
  have rhs_split :
      ∑ i ∈ Finset.range (k + 1), a i * b (k - i)
        = ∑ i ∈ Finset.range (k + 1) with i < n ∧ k - i < n, a i * b (k - i) := by
    rw [eq_comm]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hi'
    rw [Finset.mem_filter, not_and_or] at hi'
    -- Either i ≥ n (then a i = 0) or k - i ≥ n (then b (k - i) = 0).
    rcases hi' with hin | hin
    · exact absurd hi hin
    rcases not_and_or.mp hin with hbn | hbn
    · rw [ha i (Nat.le_of_not_lt hbn), zero_mul]
    · rw [hb (k - i) (Nat.le_of_not_lt hbn), mul_zero]
  rw [rhs_split]
  -- Now both sides are over subsets parameterized by `(i, j)` (LHS) or `i` (RHS).
  -- Reindex via the bijection fiber ↔ range filter given by `p ↦ p.1` (LHS → RHS).
  refine Finset.sum_nbij' (i := fun p => p.1) (j := fun i => (i, k - i))
    ?_ ?_ ?_ ?_ ?_
  · -- Forward: p ∈ fiber → p.1 ∈ range (k+1) ∩ (p.1 < n ∧ k - p.1 < n).
    intro p hp
    simp only at *
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hp1, ?_⟩
    · omega
    · omega
  · -- Backward: i ∈ range filter → (i, k - i) ∈ fiber.
    intro i hi
    simp only at *
    rw [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hi1, hi2, hi3⟩ := hi
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    refine ⟨⟨hi2, hi3⟩, ?_⟩
    omega
  · -- Left-inverse: p ↦ p.1 ↦ (p.1, k - p.1) = p (since p.1 + p.2 = k).
    intro p hp
    simp only at *
    rw [Finset.mem_filter] at hp
    have hkk : p.1 + p.2 = k := hp.2
    ext
    · rfl
    · change k - p.1 = p.2
      omega
  · -- Right-inverse: i ↦ (i, k - i) ↦ i.
    intros; rfl
  · -- Function values match: a p.1 * b p.2 = a p.1 * b (k - p.1) (since p.1 + p.2 = k).
    intro p hp
    simp only at *
    rw [Finset.mem_filter] at hp
    have hkk : p.1 + p.2 = k := hp.2
    have : k - p.1 = p.2 := by omega
    rw [this]

/-! ## Carry-no-wrap: telescoping cancellation -/

/-- **Carry telescope.** Auxiliary sum-shift identity: if a sequence `c : ℕ → ℕ` is
zero at both endpoints `0` and `N`, then the `β`-weighted sums of `c` and of its
left-shift `c ∘ (· + 1)` agree (the latter is rescaled by `β`). This is the
combinatorial heart of the carry-propagation argument: the carry tower
`carry k · β^k` (LHS contributions) matches `carry (k+1) · β^(k+1)` (RHS
contributions) after summing, because the boundary terms vanish. -/
theorem carry_telescope (carry : ℕ → ℕ) (β N : ℕ)
    (h0 : carry 0 = 0) (hN : carry N = 0) :
    ∑ k ∈ Finset.range N, carry k * β ^ k
      = ∑ k ∈ Finset.range N, carry (k + 1) * β ^ (k + 1) := by
  -- Both sides equal `∑ k ∈ range (N + 1), carry k * β^k`.
  have hL : ∑ k ∈ Finset.range (N + 1), carry k * β ^ k
              = ∑ k ∈ Finset.range N, carry k * β ^ k := by
    rw [Finset.sum_range_succ, hN, zero_mul, add_zero]
  have hR : ∑ k ∈ Finset.range (N + 1), carry k * β ^ k
              = ∑ k ∈ Finset.range N, carry (k + 1) * β ^ (k + 1) := by
    rw [Finset.sum_range_succ' (fun k => carry k * β ^ k) N, h0, zero_mul, add_zero]
  exact hL.symm.trans hR

/-- **Carry-propagation soundness.** If the per-column field constraints
`colA k + carry k = colQM k + β · carry (k+1)` hold for every `k ∈ [0, N)`,
with the carries pinned at the boundaries `carry 0 = 0` and `carry N = 0`, then
the polynomial values `Σₖ colA k · β^k` and `Σₖ colQM k · β^k` agree.

In the ECDSA `mul_mod` context: `N = 2n`, `colA k = colSum a b k` (column of the
product `a · b`), `colQM k = colSum_qm k` (column of `q · m + c`). The boundary
carries are zero by construction, and the no-wrap condition is exactly that
each `carry k` is an honest natural number rather than a wrapped field element. -/
theorem colSum_carry_telescope (colA colQM carry : ℕ → ℕ) (β N : ℕ)
    (h0 : carry 0 = 0) (hN : carry N = 0)
    (hcol : ∀ k ∈ Finset.range N,
        colA k + carry k = colQM k + β * carry (k + 1)) :
    ∑ k ∈ Finset.range N, colA k * β ^ k
      = ∑ k ∈ Finset.range N, colQM k * β ^ k := by
  -- Add the carry tower to both sides; the telescope lemma cancels it.
  have key :
      ∑ k ∈ Finset.range N, (colA k + carry k) * β ^ k
        = ∑ k ∈ Finset.range N, (colQM k + β * carry (k + 1)) * β ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcol k hk]
  -- Expand both sides using `add_mul` and split the sums.
  have hL :
      ∑ k ∈ Finset.range N, (colA k + carry k) * β ^ k
        = (∑ k ∈ Finset.range N, colA k * β ^ k)
          + ∑ k ∈ Finset.range N, carry k * β ^ k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intros; ring
  have hR :
      ∑ k ∈ Finset.range N, (colQM k + β * carry (k + 1)) * β ^ k
        = (∑ k ∈ Finset.range N, colQM k * β ^ k)
          + ∑ k ∈ Finset.range N, carry (k + 1) * β ^ (k + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]; ring
  -- Combine: LHS_sum + T = RHS_sum + T', and T = T' by `carry_telescope`.
  have htele := carry_telescope carry β N h0 hN
  -- Substitute and cancel the common carry-tower term.
  rw [hL, hR] at key
  rw [htele] at key
  exact Nat.add_right_cancel key

/-! ## Gluing: limbwise constraints ⇒ modular product -/

/-- Zero-extend a `Fin n → ℕ` limb vector to `ℕ → ℕ`. Limbs past index `n` are
zero. This is the indexing convention used by the column-sum machinery — limb
constraints are stated over column indices `k ∈ [0, 2n)` that range past the
natural limb range. -/
def ext {n : ℕ} (ls : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then ls ⟨i, h⟩ else 0

/-- `ext` vanishes outside `[0, n)` — the support hypothesis required by
`colSum_eq`. -/
theorem ext_eq_zero {n : ℕ} (ls : Fin n → ℕ) (i : ℕ) (h : n ≤ i) :
    ext ls i = 0 := by
  unfold ext; simp [Nat.not_lt_of_ge h]

/-- The recomposed value of a `Fin n` limb vector via `valOfLimbs` equals the
`ℕ`-indexed recomposition of its zero-extension. -/
theorem valOfLimbs_eq_valOfNatLimbs_ext {n : ℕ} (ls : Fin n → ℕ) (β : ℕ) :
    valOfLimbs ls β = valOfNatLimbs (ext ls) n β := by
  unfold valOfLimbs valOfNatLimbs ext
  rw [← Fin.sum_univ_eq_sum_range
        (fun i => (if h : i < n then ls ⟨i, h⟩ else 0) * β ^ i)]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i : ℕ) < n := i.is_lt
  simp [hi, Fin.eta]

/-- **Limbwise constraints + carry-no-wrap ⇒ modular product (gluing).**

This is the full soundness chain for the non-native `mod_mul` gadget
(`crates/xark-bignum/src/lib.rs`):
the limb-by-limb `Fr` column constraints, modeled as plain-ℕ equations on the
extended limbs (which is sound provided the in-circuit carry range gadget
ensures no carry wraps in `Fr`), force the recomposed value of `c` to be the
modular product `(a · b) mod m`.

Hypotheses:
* `carry : ℕ → ℕ` — column-by-column carry, pinned to `0` at both ends
  (`h0`, `h2n`).
* `hcol` — the per-column equation enforced by `mul_mod`:
  `colSum a b k + carry k = colSum q m k + c k + β · carry (k+1)`,
  for `k ∈ [0, 2n)`. (Here `a, b, q, m, c` are zero-extended past index `n` via
  `ext`; the `c k` term is `0` for `k ≥ n`, so the equation degenerates to a
  pure `q · m` equation in the high columns.)
* `hm` — modulus is positive.
* `hc_lt` — gadget-side bit-decomposition range check: `c < m`.

Conclusion: the limb-recomposed `c` is the unique modular product. -/
theorem mul_mod_via_limbwise_constraints {n : ℕ} (a b q c m : Fin n → ℕ)
    (carry : ℕ → ℕ) (β : ℕ)
    (h0 : carry 0 = 0) (h2n : carry (2 * n) = 0)
    (hcol : ∀ k ∈ Finset.range (2 * n),
        colSum (ext a) (ext b) k + carry k
          = colSum (ext q) (ext m) k + ext c k + β * carry (k + 1))
    (_hm : 0 < valOfLimbs m β) (hc_lt : valOfLimbs c β < valOfLimbs m β) :
    valOfLimbs c β = (valOfLimbs a β * valOfLimbs b β) % valOfLimbs m β := by
  -- Step 1: the carry telescope reduces the per-column equations to a polynomial identity.
  have htele :
      ∑ k ∈ Finset.range (2 * n), colSum (ext a) (ext b) k * β ^ k
        = ∑ k ∈ Finset.range (2 * n),
            (colSum (ext q) (ext m) k + ext c k) * β ^ k := by
    refine colSum_carry_telescope _ _ _ β _ h0 h2n ?_
    intro k hk
    have := hcol k hk
    -- Reassociate to match the telescope shape (colA + carry = colQM + β * carry').
    -- Here colQM k = colSum q m k + ext c k.
    linarith
  -- Step 2: Cauchy product identity on both sides.
  have ha_supp : ∀ i ≥ n, ext a i = 0 := fun i h => ext_eq_zero a i h
  have hb_supp : ∀ j ≥ n, ext b j = 0 := fun j h => ext_eq_zero b j h
  have hq_supp : ∀ i ≥ n, ext q i = 0 := fun i h => ext_eq_zero q i h
  have hm_supp : ∀ j ≥ n, ext m j = 0 := fun j h => ext_eq_zero m j h
  have hc_supp : ∀ i ≥ n, ext c i = 0 := fun i h => ext_eq_zero c i h
  have h_a_b := colSum_eq (ext a) (ext b) n β ha_supp hb_supp
  have h_q_m := colSum_eq (ext q) (ext m) n β hq_supp hm_supp
  -- Step 3: split the RHS into `q · m` part and `c` part.
  have hsplit :
      ∑ k ∈ Finset.range (2 * n),
            (colSum (ext q) (ext m) k + ext c k) * β ^ k
        = (∑ k ∈ Finset.range (2 * n), colSum (ext q) (ext m) k * β ^ k)
          + ∑ k ∈ Finset.range (2 * n), ext c k * β ^ k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intros; ring
  -- Step 4: the `c` part equals `valOfNatLimbs (ext c) n β`, since
  -- `ext c k = 0` for `k ≥ n`.
  have hc_sum :
      ∑ k ∈ Finset.range (2 * n), ext c k * β ^ k
        = valOfNatLimbs (ext c) n β := by
    unfold valOfNatLimbs
    have hn_le : n ≤ 2 * n := by omega
    rw [eq_comm]
    apply Finset.sum_subset (Finset.range_subset_range.mpr hn_le)
    intro k _ hk_notin
    rw [Finset.mem_range, not_lt] at hk_notin
    rw [hc_supp k hk_notin, zero_mul]
  -- Step 5: put together the integer identity at recomposed values.
  rw [hsplit, hc_sum] at htele
  rw [← h_a_b, ← h_q_m] at htele
  -- Step 6: rewrite via the `Fin n → ℕ` ↔ `ℕ → ℕ` bridge in the goal and `hc_lt`.
  rw [valOfLimbs_eq_valOfNatLimbs_ext c, valOfLimbs_eq_valOfNatLimbs_ext a,
      valOfLimbs_eq_valOfNatLimbs_ext b, valOfLimbs_eq_valOfNatLimbs_ext m]
  rw [valOfLimbs_eq_valOfNatLimbs_ext c, valOfLimbs_eq_valOfNatLimbs_ext m] at hc_lt
  exact mul_mod_sound _ _ _ _ _ hc_lt htele

/-! ## `Fr` ↔ `ℕ` bridge: no-wrap value semantics -/

/-- **`Fr`-addition agrees with `ℕ`-addition under a no-wrap bound.** If the
sum of the natural-number `.val`s stays strictly below the modulus `r`, then
the `Fr`-addition does not reduce, so `(a + b).val = a.val + b.val` in `ℕ`.
This is the additive half of the `ZMod r ↔ ℕ` bridge consumed by the column
no-wrap argument. -/
theorem add_val_no_wrap {a b : ZMod r} (h : a.val + b.val < r) :
    (a + b).val = a.val + b.val :=
  ZMod.val_add_of_lt h

/-- **`Fr`-multiplication agrees with `ℕ`-multiplication under a no-wrap bound.**
If the product of the natural-number `.val`s stays strictly below `r`, then the
`Fr`-multiplication does not reduce, so `(a * b).val = a.val * b.val` in `ℕ`.
This is the multiplicative half of the `ZMod r ↔ ℕ` bridge. -/
theorem mul_val_no_wrap {a b : ZMod r} (h : a.val * b.val < r) :
    (a * b).val = a.val * b.val :=
  ZMod.val_mul_of_lt h

/-! ## Column-sum budget bound -/

/-- **Pointwise term bound.** Each summand `aᵢ · b_{k−i}` in `colSum a b k` is
bounded by `(β − 1)²` when every limb is strictly bounded by `β`. Auxiliary
for `colSum_le`. -/
theorem colSum_term_le (a b : ℕ → ℕ) (β : ℕ)
    (ha : ∀ i, a i < β) (hb : ∀ j, b j < β) (i k : ℕ) :
    a i * b (k - i) ≤ (β - 1) * (β - 1) := by
  have h1 : a i ≤ β - 1 := Nat.le_sub_one_of_lt (ha i)
  have h2 : b (k - i) ≤ β - 1 := Nat.le_sub_one_of_lt (hb (k - i))
  exact Nat.mul_le_mul h1 h2

/-- **Column-sum budget bound.** When every limb is strictly bounded by `β`, the
`k`-th schoolbook column sum is bounded by `(k + 1) · (β − 1)²`. This is the
coarse "all terms maxed out" bound — tighter (`min (k+1) (2n-1-k)`) bounds exist
under additional support hypotheses, but `(k + 1)` always suffices and avoids
case-splitting on `k`. In particular, for `k < 2n`, `colSum a b k ≤ 2n · (β−1)²`.
-/
theorem colSum_le (a b : ℕ → ℕ) (β k : ℕ)
    (ha : ∀ i, a i < β) (hb : ∀ j, b j < β) :
    colSum a b k ≤ (k + 1) * ((β - 1) * (β - 1)) := by
  unfold colSum
  calc ∑ i ∈ Finset.range (k + 1), a i * b (k - i)
      ≤ ∑ _i ∈ Finset.range (k + 1), (β - 1) * (β - 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact colSum_term_le a b β ha hb i k
    _ = (k + 1) * ((β - 1) * (β - 1)) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ## Carry budget bound (ℕ-side) -/

/-- **Carry-budget bound.** Assuming the per-column ℕ-equation
`colSum a b k + carry k = colSum q m k + ext c k + β · carry (k+1)` with limbs
bounded by a base `β ≥ 2`, the `k`-th carry stays bounded by
`(k + 1) · (β − 1)²` (a coarse uniform bound; tighter `n · (β − 1)` bounds are
possible but unnecessary for the secp256k1 budget). Proved by induction on `k`,
using `β · carry (k+1) ≤ colSum a b k + carry k` from the equation. -/
theorem carry_le {n : ℕ} (a b q c m : Fin n → ℕ)
    (carry : ℕ → ℕ) (β : ℕ) (hβ : 2 ≤ β)
    (ha : ∀ i, a i < β) (hb : ∀ i, b i < β)
    (h0 : carry 0 = 0)
    (hcol : ∀ k,
        colSum (ext a) (ext b) k + carry k
          = colSum (ext q) (ext m) k + ext c k + β * carry (k + 1)) :
    ∀ k, carry k ≤ (k + 1) * ((β - 1) * (β - 1)) := by
  have hβ_pos : 0 < β := by omega
  -- Limb bounds extend to the zero-extension.
  have ha_ext : ∀ i, ext a i < β := by
    intro i; unfold ext
    by_cases hi : i < n
    · simp only [hi, dite_true]; exact ha _
    · simp only [hi, dite_false]; exact hβ_pos
  have hb_ext : ∀ i, ext b i < β := by
    intro i; unfold ext
    by_cases hi : i < n
    · simp only [hi, dite_true]; exact hb _
    · simp only [hi, dite_false]; exact hβ_pos
  intro k
  induction k with
  | zero =>
    rw [h0]; exact Nat.zero_le _
  | succ k ih =>
    -- From the equation: β · carry (k+1) ≤ colSum (ext a)(ext b) k + carry k.
    have hk := hcol k
    have hle : β * carry (k + 1) ≤ colSum (ext a) (ext b) k + carry k := by omega
    -- colSum bound: ≤ (k+1)·(β-1)².
    have hcol_le := colSum_le (ext a) (ext b) β k ha_ext hb_ext
    -- Combine: β · carry (k+1) ≤ (k+1)·(β-1)² + (k+1)·(β-1)² = 2·(k+1)·(β-1)².
    have hbound : β * carry (k + 1) ≤ 2 * ((k + 1) * ((β - 1) * (β - 1))) := by
      have h1 : carry k ≤ (k + 1) * ((β - 1) * (β - 1)) := ih
      calc β * carry (k + 1)
          ≤ colSum (ext a) (ext b) k + carry k := hle
        _ ≤ (k + 1) * ((β - 1) * (β - 1)) + (k + 1) * ((β - 1) * (β - 1)) :=
            Nat.add_le_add hcol_le h1
        _ = 2 * ((k + 1) * ((β - 1) * (β - 1))) := by ring
    -- Now `β ≥ 2`, so `β · ((k+2)·X) ≥ 2 · ((k+1)·X) + 2·X ≥ 2 · ((k+1)·X)`.
    -- Concretely, we show carry (k+1) ≤ (k+2) · (β-1)².
    -- It suffices to show β · ((k+2) · (β-1)²) ≥ 2 · ((k+1) · (β-1)²).
    -- Equivalently β·(k+2) ≥ 2·(k+1), which from β ≥ 2 gives 2(k+2) ≥ 2(k+1) — true.
    have hkey : 2 * ((k + 1) * ((β - 1) * (β - 1)))
                  ≤ β * ((k + 1 + 1) * ((β - 1) * (β - 1))) := by
      have h_mul : 2 * (k + 1) ≤ β * (k + 1 + 1) := by
        calc 2 * (k + 1) ≤ 2 * (k + 1 + 1) := by nlinarith
          _ ≤ β * (k + 1 + 1) := Nat.mul_le_mul_right _ hβ
      calc 2 * ((k + 1) * ((β - 1) * (β - 1)))
          = (2 * (k + 1)) * ((β - 1) * (β - 1)) := by ring
        _ ≤ (β * (k + 1 + 1)) * ((β - 1) * (β - 1)) :=
            Nat.mul_le_mul_right _ h_mul
        _ = β * ((k + 1 + 1) * ((β - 1) * (β - 1))) := by ring
    have hcombine : β * carry (k + 1) ≤ β * ((k + 1 + 1) * ((β - 1) * (β - 1))) :=
      le_trans hbound hkey
    -- Cancel β on the left.
    exact Nat.le_of_mul_le_mul_left hcombine hβ_pos

/-! ## Headline theorem: Fr-level limbwise constraints ⇒ modular product

The constraints emitted by the non-native `mod_mul` gadget (`crates/xark-bignum/src/lib.rs`)
live in `Fr = ZMod r`. The
column equation we prove sound here is

  `(∑ i ∈ [0, k+1), aᵢ · b_{k-i}) + carry k`
  `= (∑ i ∈ [0, k+1), qᵢ · m_{k-i}) + cₖ + (β : Fr) · carry (k+1)`

where every quantity is `Fr`-valued. The "no field wrap" obligation is the
prover-side circuit range gadget on each `carry k`. For the secp256k1
instantiation `n = 3`, `β = 2 ^ 86`, the budget chain

  `colSum ≤ 3 · (2^86 - 1)²  <  2^175`
  `carry k  <  2^92`                              (in-circuit range check, `k < 2n = 6`)
  `colSum + carry k + β · carry (k+1) < 2^179 < 2^253 < r`

shows that no column-equation expression overflows `Fr`, so the `Fr`-equation
can be read off as an `ℕ`-equation via `.val`. The conclusion is then exactly
what `mul_mod_via_limbwise_constraints` discharges.
-/

/-- `Fr`-extension of an `n`-limb vector. Returns the underlying `ZMod r`-limb at
index `i < n`, and `0 : ZMod r` otherwise. The `Fr`-analogue of `ext`. -/
def extFr {n : ℕ} (ls : Fin n → ZMod r) (i : ℕ) : ZMod r :=
  if h : i < n then ls ⟨i, h⟩ else 0

/-- `.val` of the `Fr`-extension equals the ℕ-extension of the limb `.val`s. -/
theorem val_extFr {n : ℕ} (ls : Fin n → ZMod r) (i : ℕ) :
    (extFr ls i).val = ext (fun j => (ls j).val) i := by
  unfold extFr ext
  by_cases hi : i < n
  · simp only [hi, dite_true]
  · simp only [hi, dite_false]
    exact ZMod.val_zero

set_option maxRecDepth 8000 in
/-- **Fr-level no-wrap soundness for the limbwise modular product (3-limb).**
Non-native modular-product soundness at `n = 3`, `β = 2^86`, matching the
`mod_mul` gadget in `xark-bignum` (5 product columns; carries range-checked to
`< 2^92`). The budget chain keeps every column expression far below `r`, so the
`Fr`-equation is sound as a `ℕ`-equation on limb `.val`s and the conclusion
follows from `mul_mod_via_limbwise_constraints`. -/
theorem mul_mod_via_Fr_limbwise_constraints
    (a b q c m : Fin 3 → ZMod r)
    (carry : ℕ → ZMod r)
    (ha : ∀ i, (a i).val < 2 ^ 86) (hb : ∀ i, (b i).val < 2 ^ 86)
    (hq : ∀ i, (q i).val < 2 ^ 86) (hc : ∀ i, (c i).val < 2 ^ 86)
    (hmL : ∀ i, (m i).val < 2 ^ 86)
    (hcarry : ∀ k, (carry k).val < 2 ^ 92)
    (h0 : carry 0 = 0) (h2n : carry 6 = 0)
    (hcol_Fr : ∀ k ∈ Finset.range 6,
        (∑ i ∈ Finset.range (k + 1), extFr a i * extFr b (k - i)) + carry k
          = (∑ i ∈ Finset.range (k + 1), extFr q i * extFr m (k - i))
              + extFr c k + (2 ^ 86 : ZMod r) * carry (k + 1))
    (hm_pos : 0 < valOfLimbs (fun i => (m i).val) (2 ^ 86))
    (hc_lt : valOfLimbs (fun i => (c i).val) (2 ^ 86)
              < valOfLimbs (fun i => (m i).val) (2 ^ 86)) :
    valOfLimbs (fun i => (c i).val) (2 ^ 86)
      = (valOfLimbs (fun i => (a i).val) (2 ^ 86)
          * valOfLimbs (fun i => (b i).val) (2 ^ 86))
          % valOfLimbs (fun i => (m i).val) (2 ^ 86) := by
  -- Abbreviations for the ℕ-side limbs.
  set aN : Fin 3 → ℕ := fun i => (a i).val
  set bN : Fin 3 → ℕ := fun i => (b i).val
  set qN : Fin 3 → ℕ := fun i => (q i).val
  set cN : Fin 3 → ℕ := fun i => (c i).val
  set mN : Fin 3 → ℕ := fun i => (m i).val
  set carryN : ℕ → ℕ := fun k => (carry k).val
  -- Bound on each `extFr · extFr` product (≤ (β-1)² < 2^128 < r).
  have rgt : 2 ^ 253 < r := two_pow_lt_r
  have r_ne : (r : ℕ) ≠ 0 := by
    have hrpos : 0 < r := by unfold r; norm_num
    exact Nat.pos_iff_ne_zero.mp hrpos
  -- Boundary carry values are 0 in ℕ.
  have h0N : carryN 0 = 0 := by simp [carryN, h0, ZMod.val_zero]
  have h2nN : carryN 6 = 0 := by simp [carryN, h2n, ZMod.val_zero]
  -- Bound on aN, bN, qN, cN, mN.
  have haN : ∀ i, aN i < 2 ^ 86 := ha
  have hbN : ∀ i, bN i < 2 ^ 86 := hb
  have hqN : ∀ i, qN i < 2 ^ 86 := hq
  have hcN : ∀ i, cN i < 2 ^ 86 := hc
  have hmN : ∀ i, mN i < 2 ^ 86 := hmL
  -- ext bounds for the column-sum bound lemma.
  have ha_ext : ∀ i, ext aN i < 2 ^ 86 := by
    intro i; unfold ext
    by_cases hi : i < 3
    · simp only [hi, dite_true]; exact haN _
    · simp only [hi, dite_false]; positivity
  have hb_ext : ∀ i, ext bN i < 2 ^ 86 := by
    intro i; unfold ext
    by_cases hi : i < 3
    · simp only [hi, dite_true]; exact hbN _
    · simp only [hi, dite_false]; positivity
  have hq_ext : ∀ i, ext qN i < 2 ^ 86 := by
    intro i; unfold ext
    by_cases hi : i < 3
    · simp only [hi, dite_true]; exact hqN _
    · simp only [hi, dite_false]; positivity
  have hm_ext : ∀ i, ext mN i < 2 ^ 86 := by
    intro i; unfold ext
    by_cases hi : i < 3
    · simp only [hi, dite_true]; exact hmN _
    · simp only [hi, dite_false]; positivity
  -- Cast helper: for any natural n, (n : ZMod r) cast back equals n.val if n < r.
  -- We'll bridge the Fr-equation to an ℕ-equation column-by-column.
  -- Strategy: from hcol_Fr, derive ℕ-equation `colSum aN bN k + carryN k = ...`
  -- using that all relevant quantities have .val < r and computations don't wrap.
  -- Define the natural-number bound that bounds every expression in a column equation.
  -- The bound `(2*3) * (2^86)² ≈ 2^175 + 2^92 (carry) + 2^86 * 2^92` — these
  -- need to be < r ≈ 2^254. We need to be careful.
  -- Step 1: convert the per-column Fr equation to a per-column ℕ equation.
  have hcolN : ∀ k ∈ Finset.range 6,
      colSum (ext aN) (ext bN) k + carryN k
        = colSum (ext qN) (ext mN) k + ext cN k + 2 ^ 86 * carryN (k + 1) := by
    intro k hk
    -- ℕ-side quantities for column k.
    -- Cast `extFr ls i` and `(ls j).val` between sides.
    -- Key identity: `(extFr ls i).val = ext (fun j => (ls j).val) i`.
    -- And `((ext (fun j => (ls j).val) i : ℕ) : ZMod r) = extFr ls i` since val < r.
    -- We'll show LHS_Fr = ↑LHS_ℕ and RHS_Fr = ↑RHS_ℕ; then natCast_eq_natCast_iff
    -- + Nat.mod_eq_of_lt gives LHS_ℕ = RHS_ℕ.
    have h_lhs_nat :
        ((colSum (ext aN) (ext bN) k + carryN k : ℕ) : ZMod r)
          = (∑ i ∈ Finset.range (k + 1), extFr a i * extFr b (k - i)) + carry k := by
      push_cast
      unfold colSum
      congr 1
      · rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
        -- ↑(ext aN i) = extFr a i
        have h1 : ((ext aN i : ℕ) : ZMod r) = extFr a i := by
          unfold ext extFr aN
          by_cases hi : i < 3
          · simp only [hi, dite_true]
            exact ZMod.natCast_zmod_val _
          · simp only [hi, dite_false, Nat.cast_zero]
        have h2 : ((ext bN (k - i) : ℕ) : ZMod r) = extFr b (k - i) := by
          unfold ext extFr bN
          by_cases hi : k - i < 3
          · simp only [hi, dite_true]
            exact ZMod.natCast_zmod_val _
          · simp only [hi, dite_false, Nat.cast_zero]
        rw [h1, h2]
      · -- ↑(carryN k) = carry k
        unfold carryN
        exact ZMod.natCast_zmod_val _
    have h_rhs_nat :
        ((colSum (ext qN) (ext mN) k + ext cN k + 2 ^ 86 * carryN (k + 1) : ℕ)
            : ZMod r)
          = (∑ i ∈ Finset.range (k + 1), extFr q i * extFr m (k - i))
              + extFr c k + (2 ^ 86 : ZMod r) * carry (k + 1) := by
      push_cast
      unfold colSum
      congr 1
      · congr 1
        · rw [Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Nat.cast_mul]
          have h1 : ((ext qN i : ℕ) : ZMod r) = extFr q i := by
            unfold ext extFr qN
            by_cases hi : i < 3
            · simp only [hi, dite_true]
              exact ZMod.natCast_zmod_val _
            · simp only [hi, dite_false, Nat.cast_zero]
          have h2 : ((ext mN (k - i) : ℕ) : ZMod r) = extFr m (k - i) := by
            unfold ext extFr mN
            by_cases hi : k - i < 3
            · simp only [hi, dite_true]
              exact ZMod.natCast_zmod_val _
            · simp only [hi, dite_false, Nat.cast_zero]
          rw [h1, h2]
        · -- ↑(ext cN k) = extFr c k
          unfold ext extFr cN
          by_cases hi : k < 3
          · simp only [hi, dite_true]
            exact ZMod.natCast_zmod_val _
          · simp only [hi, dite_false, Nat.cast_zero]
      · -- ↑(2^64 * carryN (k+1)) = (2^64 : ZMod r) * carry (k+1)
        unfold carryN
        rw [ZMod.natCast_zmod_val]
        norm_num
    -- Combine: ↑LHS_ℕ = ↑RHS_ℕ in ZMod r.
    have hcastEq :
        ((colSum (ext aN) (ext bN) k + carryN k : ℕ) : ZMod r)
          = ((colSum (ext qN) (ext mN) k + ext cN k + 2 ^ 86 * carryN (k + 1) : ℕ)
              : ZMod r) := by
      rw [h_lhs_nat, h_rhs_nat]
      exact hcol_Fr k hk
    -- Convert to MOD r congruence.
    have hmod : (colSum (ext aN) (ext bN) k + carryN k)
                  ≡ (colSum (ext qN) (ext mN) k + ext cN k + 2 ^ 86 * carryN (k + 1))
                  [MOD r] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcastEq
    -- Bound both sides < r to drop the mod.
    -- LHS bound: colSum ≤ (k+1)·(β-1)² ≤ 6·(2^86-1)² < 2^175, + carryN k < 2^92.
    -- Total < 2^176 < 2^253 < r.
    have h_colSum_ab := colSum_le (ext aN) (ext bN) (2 ^ 86) k ha_ext hb_ext
    have h_colSum_qm := colSum_le (ext qN) (ext mN) (2 ^ 86) k hq_ext hm_ext
    have hk_lt8 : k < 6 := Finset.mem_range.mp hk
    have h_carryNk : carryN k < 2 ^ 92 := hcarry k
    have h_carryNk1 : carryN (k + 1) < 2 ^ 92 := hcarry (k + 1)
    have h_extcN : ext cN k < 2 ^ 86 := by
      unfold ext
      by_cases hi : k < 3
      · simp only [hi, dite_true]; exact hcN _
      · simp only [hi, dite_false]; positivity
    -- Pack everything into a numeric bound that fits below 2^253.
    have hβm1 : (2 ^ 86 : ℕ) - 1 < 2 ^ 86 := by norm_num
    -- (k+1) ≤ 6 so colSum ≤ 6 · (2^86-1)².
    have h_kplus1 : k + 1 ≤ 6 := by omega
    have h_colSum_ab' : colSum (ext aN) (ext bN) k
                          ≤ 6 * ((2 ^ 86 - 1) * (2 ^ 86 - 1)) := by
      apply le_trans h_colSum_ab
      apply Nat.mul_le_mul_right
      exact h_kplus1
    have h_colSum_qm' : colSum (ext qN) (ext mN) k
                          ≤ 6 * ((2 ^ 86 - 1) * (2 ^ 86 - 1)) := by
      apply le_trans h_colSum_qm
      apply Nat.mul_le_mul_right
      exact h_kplus1
    -- The numeric bounds: 6 * (2^86-1)² < 2^175; carry < 2^92; β · carry < 2^178.
    have h_lhs_lt_r : colSum (ext aN) (ext bN) k + carryN k < r := by
      have : colSum (ext aN) (ext bN) k + carryN k
              ≤ 6 * ((2 ^ 86 - 1) * (2 ^ 86 - 1)) + 2 ^ 92 := by
        exact Nat.add_le_add h_colSum_ab' (le_of_lt h_carryNk)
      apply lt_of_le_of_lt this
      have hr : 6 * ((2 ^ 86 - 1) * (2 ^ 86 - 1)) + 2 ^ 92 < 2 ^ 253 := by norm_num
      exact lt_trans hr rgt
    have h_rhs_lt_r :
        colSum (ext qN) (ext mN) k + ext cN k + 2 ^ 86 * carryN (k + 1) < r := by
      have hβ_carry : 2 ^ 86 * carryN (k + 1) ≤ 2 ^ 86 * 2 ^ 92 :=
        Nat.mul_le_mul_left _ (le_of_lt h_carryNk1)
      have hbound :
          colSum (ext qN) (ext mN) k + ext cN k + 2 ^ 86 * carryN (k + 1)
            ≤ 6 * ((2 ^ 86 - 1) * (2 ^ 86 - 1)) + 2 ^ 86 + 2 ^ 86 * 2 ^ 92 := by
        refine Nat.add_le_add (Nat.add_le_add h_colSum_qm' (le_of_lt h_extcN)) hβ_carry
      apply lt_of_le_of_lt hbound
      have hr :
          6 * ((2 ^ 86 - 1) * (2 ^ 86 - 1)) + 2 ^ 86 + 2 ^ 86 * 2 ^ 92 < 2 ^ 253 := by
        norm_num
      exact lt_trans hr rgt
    -- Drop the congruence to equality.
    rw [Nat.ModEq] at hmod
    rw [Nat.mod_eq_of_lt h_lhs_lt_r, Nat.mod_eq_of_lt h_rhs_lt_r] at hmod
    exact hmod
  -- Step 2: apply `mul_mod_via_limbwise_constraints` to the ℕ-equation.
  have hm_pos' : 0 < valOfLimbs mN (2 ^ 86) := hm_pos
  have hc_lt' : valOfLimbs cN (2 ^ 86) < valOfLimbs mN (2 ^ 86) := hc_lt
  exact mul_mod_via_limbwise_constraints aN bN qN cN mN carryN (2 ^ 86) h0N h2nN
    (fun k hk => hcolN k hk) hm_pos' hc_lt'


end Xark
