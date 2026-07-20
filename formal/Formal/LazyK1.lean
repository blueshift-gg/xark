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
# xark secp256k1 lazy-reduction soundness — the Mersenne fold — in Lean 4 / mathlib

The secp256k1 base field is `p = 2²⁵⁶ − 2³² − 977`. `crates/xark-bignum`'s
`mul_lazy_k1` multiplies two 4×64-bit values mod `p` with the same
quotient-free, deferred-reduction strategy as `mul_lazy_25519`
(`Formal.Lazy25519`): form the schoolbook column products `cols[0..6]` (positions
`2^(64·k)`), then *fold* the high columns into the low ones by multiplying by the
reduction constant `c = 2³² + 977 = 4294968273`, and carry-normalize base `2⁶⁴`.
This is the multiply used by k1's incomplete-affine EC add (`ec_add_k1` /
`ec_double_k1`), the path `Formal.Secp256k1.ec_add_incomplete_secp256k1_sound`
reasons about at the field level.

The fold is value-preserving because `2²⁵⁶ ≡ c (mod p)`: a unit at position
`2^(64·4) = 2²⁵⁶` is congruent to `c` at position `0`, one at `2^(64·5)` to `c·2⁶⁴`,
and one at `2^(64·6)` to `c·2¹²⁸`. So replacing the three high columns by `c·`
their values changes nothing mod `p` — exactly the reduction the gadget performs.

Mirrors `Formal.Lazy25519` for the `2²⁵⁵ − 19` field.

* `pK1` — the prime `2²⁵⁶ − 2³² − 977`.
* `two256_eq_c` — the Mersenne relation `2²⁵⁶ = 4294968273` in `ZMod pK1`.
* `lazy_fold_value_preserving_k1` — the 7-column fold equals its 4-column image
  in `ZMod pK1`: `mul_lazy_k1`'s reduction is sound mod `p`.
* `lazy_s1_lt_k1` — the output-limb bound: `s1 = r1 + k0 < 2⁶⁵`.
-/

namespace Xark

/-- The secp256k1 reduction constant `c = 2³² + 977`. -/
def cK1 : ℕ := 4294968273

/-- The secp256k1 base-field prime `p = 2²⁵⁶ − 2³² − 977 = 2²⁵⁶ − c`. -/
def pK1 : ℕ := 2 ^ 256 - 4294968273

/-- The limb base for the 4×64-bit layout, `β = 2⁶⁴`. -/
def beta64 : ℕ := 2 ^ 64

/-- **The pseudo-Mersenne relation.** In `ZMod pK1`, `2²⁵⁶ = c = 4294968273` — the
    fact that makes reduction mod `p` a cheap high-limb ×c fold. -/
theorem two256_eq_c : (2 ^ 256 : ZMod pK1) = 4294968273 := by
  have hp : (2 : ℕ) ^ 256 = pK1 + 4294968273 := by
    unfold pK1; norm_num
  have key : ((2 ^ 256 : ℕ) : ZMod pK1) = ((4294968273 : ℕ) : ZMod pK1) := by
    rw [hp, Nat.cast_add, ZMod.natCast_self, zero_add]
  exact_mod_cast key

/-- `β⁴ = 2²⁵⁶ = c` in `ZMod pK1` (the fourth column folds by `c`). -/
theorem beta64_pow4_eq_c : ((beta64 : ZMod pK1)) ^ 4 = 4294968273 := by
  have : ((beta64 : ZMod pK1)) ^ 4 = (2 ^ 256 : ZMod pK1) := by
    unfold beta64; push_cast; ring
  rw [this, two256_eq_c]

/-- **Lazy-fold value preservation.** The 7-column schoolbook value equals the
    gadget's folded 4-column value in `ZMod pK1`, so `mul_lazy_k1`'s ×c fold
    computes `a·b mod p` correctly — the reduction is sound, not assumed. -/
theorem lazy_fold_value_preserving_k1 (c0 c1 c2 c3 c4 c5 c6 : ZMod pK1) :
    let β : ZMod pK1 := beta64
    c0 + c1 * β + c2 * β ^ 2 + c3 * β ^ 3 + c4 * β ^ 4 + c5 * β ^ 5 + c6 * β ^ 6
      = (c0 + 4294968273 * c4) + (c1 + 4294968273 * c5) * β
        + (c2 + 4294968273 * c6) * β ^ 2 + c3 * β ^ 3 := by
  intro β
  have h4 : β ^ 4 = 4294968273 := beta64_pow4_eq_c
  have h5 : β ^ 5 = 4294968273 * β := by
    have : β ^ 5 = β ^ 4 * β := by ring
    rw [this, h4]
  have h6 : β ^ 6 = 4294968273 * β ^ 2 := by
    have : β ^ 6 = β ^ 4 * β ^ 2 := by ring
    rw [this, h4]
  rw [h4, h5, h6]; ring

/-- **Output limb bound.** `mul_lazy_k1`'s output limbs are `< 2⁶⁵`: `s0, r2, r3`
    come from `range_bits::<64>` checks (`< 2⁶⁴`), and `s1 = r1 + k0` with
    `r1 < 2⁶⁴` (a 64-bit remainder) and `k0 < 2⁵²` (a range-checked carry), so
    `s1 < 2⁶⁴ + 2⁵² < 2⁶⁵`. This keeps the output within the `< 2⁷⁰` precondition
    of the next lazy op with no canonical reduction. -/
theorem lazy_s1_lt_k1 (r1 k0 : ℕ) (hr1 : r1 < 2 ^ 64) (hk0 : k0 < 2 ^ 52) :
    r1 + k0 < 2 ^ 65 := by
  have hk : (2 : ℕ) ^ 52 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h65 : (2 : ℕ) ^ 65 = 2 ^ 64 + 2 ^ 64 := by rw [pow_succ]; ring
  omega

/-- **End-to-end `mul_lazy_k1` value-correctness.** Given the five carry-chain
    equalities the gadget pins with `assert_eq` — the base-`2⁶⁴` division relations
    for the four columns and the top-carry refold `u0` — the recomposed output
    `s0 + s1·β + r2·β² + r3·β³` (with `s1 = r1 + k0`) equals the product `a·b` in
    `ZMod pK1`. Chains the schoolbook product, the ×c high-limb fold, the carry
    normalization, and the ×c top-carry refold into "the gadget outputs `a·b mod
    p`". Only hypotheses: the pinned constraints plus `β⁴ = c` (`beta64_pow4_eq_c`);
    no value assumed. Mirrors `mul_lazy_25519_value_correct`. -/
theorem mul_lazy_k1_value_correct
    (β a0 a1 a2 a3 b0 b1 b2 b3 c0 r0 c1 r1 c2 r2 c3 r3 k0 s0 : ZMod pK1)
    (hβ : β ^ 4 = 4294968273)
    (ht0 : a0 * b0 + 4294968273 * (a1 * b3 + a2 * b2 + a3 * b1) = β * c0 + r0)
    (ht1 : a0 * b1 + a1 * b0 + 4294968273 * (a2 * b3 + a3 * b2) + c0 = β * c1 + r1)
    (ht2 : a0 * b2 + a1 * b1 + a2 * b0 + 4294968273 * (a3 * b3) + c1 = β * c2 + r2)
    (ht3 : a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + c2 = β * c3 + r3)
    (hu0 : r0 + 4294968273 * c3 = β * k0 + s0) :
    (a0 + a1 * β + a2 * β ^ 2 + a3 * β ^ 3) *
        (b0 + b1 * β + b2 * β ^ 2 + b3 * β ^ 3)
      = s0 + (r1 + k0) * β + r2 * β ^ 2 + r3 * β ^ 3 := by
  linear_combination
    ((a1 * b3 + a2 * b2 + a3 * b1) + (a2 * b3 + a3 * b2) * β + a3 * b3 * β ^ 2 + c3) * hβ
      + ht0 + β * ht1 + β ^ 2 * ht2 + β ^ 3 * ht3 + hu0

/-- **`weak_reduce_k1` value-correctness.** The k1 carry-normalize op (positive
    4-limb value, limbs `< 2⁷²`, to a loosely reduced one `< 2⁶⁵`, `≡` input mod
    `p`): given the base-`2⁶⁴` division equalities and the ×c top-carry refold, the
    output recomposes to the input value in `ZMod pK1`. Same Mersenne top-carry
    refold as `mul_lazy_k1_value_correct`, without the columns. Mirrors
    `weak_reduce_25519_value_correct`. -/
theorem weak_reduce_k1_value_correct
    (β v0 v1 v2 v3 c0 r0 c1 r1 c2 r2 c3 r3 k0 s0 : ZMod pK1)
    (hβ : β ^ 4 = 4294968273)
    (hv0 : v0 = β * c0 + r0)
    (hv1 : v1 + c0 = β * c1 + r1)
    (hv2 : v2 + c1 = β * c2 + r2)
    (hv3 : v3 + c2 = β * c3 + r3)
    (hu0 : r0 + 4294968273 * c3 = β * k0 + s0) :
    v0 + v1 * β + v2 * β ^ 2 + v3 * β ^ 3
      = s0 + (r1 + k0) * β + r2 * β ^ 2 + r3 * β ^ 3 := by
  linear_combination c3 * hβ + hv0 + β * hv1 + β ^ 2 * hv2 + β ^ 3 * hv3 + hu0

end Xark
