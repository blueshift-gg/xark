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
# xark ed25519 lazy-reduction soundness — the Mersenne fold — in Lean 4 / mathlib

`gadgets/xark-bignum/src/lib.rs`'s `mul_lazy_25519` multiplies two 3×85-bit
values mod `p = 2²⁵⁵ − 19` **without** a quotient hint: it forms the schoolbook
column products `cols[0..4]` (positions `2^(85·k)`), then *folds* the high
columns into the low ones by multiplying by 19 —

    t0 = cols[0] + 19·cols[3]
    t1 = cols[1] + 19·cols[4]
    t2 = cols[2]

— and carry-normalizes base `2^85`. This deferred ("lazy") reduction is what the
whole ed25519 extended-coordinate path is built on, and — unlike the eager
non-native `mulmod` (`Formal.NonNative`, with its `colSum_le`/`carry_le` budget)
— it had **no** mechanised soundness: `Formal.Edwards` proves the addition law
over an abstract field and names "the non-native limb bridges" as its residual
trust boundary. This file discharges the algebraic heart of that bridge for the
`2²⁵⁵ − 19` fold: **the ×19 high-limb fold preserves the represented value mod
`p`.** (The carry-chain-to-limb-bounds half — that each range-checked carry keeps
the output limbs `< 2⁸⁶` — is the remaining companion lemma.)

The reason the fold is value-preserving is the pseudo-Mersenne identity
`2²⁵⁵ ≡ 19 (mod p)`: a unit at position `2^(85·3) = 2²⁵⁵` is congruent to `19` at
position `2⁰`, and one at `2^(85·4) = 2²⁵⁵·2⁸⁵` to `19·2⁸⁵`. So replacing
`cols[3]·2²⁵⁵ + cols[4]·2³⁴⁰` by `19·cols[3] + 19·cols[4]·2⁸⁵` changes nothing
mod `p` — exactly the fold the gadget performs.

* `p25519` — the prime `2²⁵⁵ − 19`.
* `two255_eq_nineteen` — the Mersenne relation `2²⁵⁵ = 19` in `ZMod p25519`.
* `lazy_fold_value_preserving` — the full 5-column fold equals its 3-column image
  in `ZMod p25519`: the reduction the gadget does is sound mod `p`.
-/

namespace Xark

/-- The ed25519 base-field prime `p = 2²⁵⁵ − 19`. -/
def p25519 : ℕ := 2 ^ 255 - 19

/-- The limb base for the 3×85-bit layout, `β = 2⁸⁵`. -/
def beta85 : ℕ := 2 ^ 85

/-- **The pseudo-Mersenne relation.** In `ZMod p25519`, `2²⁵⁵ = 19` — the fact
    that makes reduction mod `2²⁵⁵ − 19` a cheap high-limb ×19 fold rather than a
    full division. -/
theorem two255_eq_nineteen : (2 ^ 255 : ZMod p25519) = 19 := by
  have hp : (2 : ℕ) ^ 255 = p25519 + 19 := by
    unfold p25519; norm_num
  have key : ((2 ^ 255 : ℕ) : ZMod p25519) = ((19 : ℕ) : ZMod p25519) := by
    rw [hp, Nat.cast_add, ZMod.natCast_self, zero_add]
  exact_mod_cast key

/-- `β³ = 2²⁵⁵ = 19` in `ZMod p25519` (the third column folds by 19). -/
theorem beta_cubed_eq_nineteen : ((beta85 : ZMod p25519)) ^ 3 = 19 := by
  have : ((beta85 : ZMod p25519)) ^ 3 = (2 ^ 255 : ZMod p25519) := by
    unfold beta85; push_cast; ring
  rw [this, two255_eq_nineteen]

/-- **Lazy-fold value preservation.** The 5-column schoolbook value
    `Σ cols[k]·β^k` (`k < 5`) equals the gadget's folded 3-column value
    `(cols₀ + 19·cols₃) + (cols₁ + 19·cols₄)·β + cols₂·β²` in `ZMod p25519`. So
    `mul_lazy_25519`'s ×19 fold computes `a·b mod p` correctly — the reduction is
    sound, not merely assumed. -/
theorem lazy_fold_value_preserving (c0 c1 c2 c3 c4 : ZMod p25519) :
    let β : ZMod p25519 := beta85
    c0 + c1 * β + c2 * β ^ 2 + c3 * β ^ 3 + c4 * β ^ 4
      = (c0 + 19 * c3) + (c1 + 19 * c4) * β + c2 * β ^ 2 := by
  intro β
  have h3 : β ^ 3 = 19 := beta_cubed_eq_nineteen
  have h4 : β ^ 4 = 19 * β := by
    have : β ^ 4 = β ^ 3 * β := by ring
    rw [this, h3]
  rw [h3, h4]; ring

/-- **Top-carry refold.** `mul_lazy_25519`'s carry chain finishes by folding the
    top carry `c2` — which sits at position `2^170 · 2^85 = 2²⁵⁵` — back into the
    low limb as `u0 = r0 + 19·c2`. That refold is value-preserving mod `p` for the
    same Mersenne reason (`2²⁵⁵ = 19`): a carry out of the top is congruent to `19`
    at position `0`. So the whole normalization, not just the column fold,
    preserves the represented value mod `p`. -/
theorem lazy_topcarry_refold (r0 c2 : ZMod p25519) :
    r0 + c2 * 2 ^ 255 = r0 + 19 * c2 := by
  rw [two255_eq_nineteen]; ring

/-- **Output limb bound.** The gadget claims `mul_lazy_25519`'s output limbs are
    `< 2⁸⁶`. Two of the three come straight from a `range_bits::<85>` check
    (`s0, r2 < 2⁸⁵`); the third is `s1 = r1 + k0` with `r1 < 2⁸⁵` (a 85-bit
    remainder) and `k0 < 2¹⁶` (a range-checked top carry), so `s1 < 2⁸⁵ + 2¹⁶ <
    2⁸⁶`. This is what lets the output feed the next lazy op (whose precondition is
    `< 2⁸⁸`) without a canonical reduction. -/
theorem lazy_s1_lt (r1 k0 : ℕ) (hr1 : r1 < 2 ^ 85) (hk0 : k0 < 2 ^ 16) :
    r1 + k0 < 2 ^ 86 := by
  have hk : (2 : ℕ) ^ 16 ≤ 2 ^ 85 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h86 : (2 : ℕ) ^ 86 = 2 ^ 85 + 2 ^ 85 := by rw [pow_succ]; ring
  omega

/-- **End-to-end `mul_lazy_25519` value-correctness.** Given the four carry-chain
    equalities the gadget pins with `assert_eq` — the base-`2⁸⁵` division relations
    for the three columns and the top-carry refold `u0` — the recomposed output
    `s0 + s1·β + r2·β²` (with `s1 = r1 + k0`) equals the product `a·b` in
    `ZMod p25519`. This is the whole reduction: the schoolbook product, the ×19
    high-limb fold, the carry normalization, and the ×19 top-carry refold, chained
    into "the gadget outputs `a·b mod p`". The only hypotheses are the pinned
    constraints plus `β³ = 19` (`beta_cubed_eq_nineteen`); no value is assumed. -/
theorem mul_lazy_25519_value_correct
    (β a0 a1 a2 b0 b1 b2 c0 r0 c1 r1 c2 r2 k0 s0 : ZMod p25519)
    (hβ : β ^ 3 = 19)
    (ht0 : a0 * b0 + 19 * (a1 * b2 + a2 * b1) = β * c0 + r0)
    (ht1 : a0 * b1 + a1 * b0 + 19 * (a2 * b2) + c0 = β * c1 + r1)
    (ht2 : a0 * b2 + a1 * b1 + a2 * b0 + c1 = β * c2 + r2)
    (hu0 : r0 + 19 * c2 = β * k0 + s0) :
    (a0 + a1 * β + a2 * β ^ 2) * (b0 + b1 * β + b2 * β ^ 2)
      = s0 + (r1 + k0) * β + r2 * β ^ 2 := by
  linear_combination
    (a1 * b2 + a2 * b1 + a2 * b2 * β + c2) * hβ + ht0 + β * ht1 + β ^ 2 * ht2 + hu0

/-- **`weak_reduce_25519` value-correctness.** The other lazy op the ed25519 path
    uses: carry-normalize a positive 3-limb value (limbs `< 2⁸⁹`) to a loosely
    reduced one (limbs `< 2⁸⁶`, `≡` input mod `p`), with no product and no
    canonical reduce. Given the base-`2⁸⁵` division equalities the gadget pins and
    the top-carry refold, the output recomposes to the input value in `ZMod p25519`
    — so the deferred normalization is value-preserving, not assumed. Same Mersenne
    top-carry ×19 refold as `mul_lazy_25519_value_correct`, without the columns. -/
theorem weak_reduce_25519_value_correct
    (β v0 v1 v2 c0 r0 c1 r1 c2 r2 k0 s0 : ZMod p25519)
    (hβ : β ^ 3 = 19)
    (hv0 : v0 = β * c0 + r0)
    (hv1 : v1 + c0 = β * c1 + r1)
    (hv2 : v2 + c1 = β * c2 + r2)
    (hu0 : r0 + 19 * c2 = β * k0 + s0) :
    v0 + v1 * β + v2 * β ^ 2 = s0 + (r1 + k0) * β + r2 * β ^ 2 := by
  linear_combination c2 * hβ + hv0 + β * hv1 + β ^ 2 * hv2 + hu0

/-! ## No-wrap magnitude bounds

The value-correctness theorems above hold in `ZMod p25519`; they are the true
statement only if the gadget's `Field` (BN254 `Fr = ZMod r`) arithmetic does not
*wrap* before the carry decompositions pin it — i.e. every schoolbook column and
biased intermediate, as a natural number, stays below `r`. `Formal.NonNative`
proves `2²⁵³ < r`; the lemmas here bound the lazy intermediates below `2²⁵³`, so
the `ZMod r ↔ ℕ` bridge (`NonNative.mul_val_no_wrap` / `add_val_no_wrap`) applies
and the lifted integer identities the value theorems assume are faithful. -/

/-- A single schoolbook product of two `< 2⁸⁸` limbs is `< 2¹⁷⁶`. -/
theorem lazy_prod_lt {a b : ℕ} (ha : a < 2 ^ 88) (hb : b < 2 ^ 88) : a * b < 2 ^ 176 := by
  calc a * b < 2 ^ 88 * 2 ^ 88 := by
        exact mul_lt_mul'' ha hb (Nat.zero_le _) (Nat.zero_le _)
    _ = 2 ^ 176 := by rw [← pow_add]

/-- A lazy column (≤ 3 products, each `< 2¹⁷⁶`) is `< 2¹⁷⁸`. -/
theorem lazy_col_lt {p0 p1 p2 : ℕ} (h0 : p0 < 2 ^ 176) (h1 : p1 < 2 ^ 176)
    (h2 : p2 < 2 ^ 176) : p0 + p1 + p2 < 2 ^ 178 := by
  have hb : (2 : ℕ) ^ 178 = 2 ^ 176 + 2 ^ 176 + 2 ^ 176 + 2 ^ 176 := by
    rw [show (178 : ℕ) = 176 + 2 from rfl, pow_add]; ring
  omega

/-- The largest lazy intermediate `t = col₀ + 19·col₃` (a folded column, each
    `< 2¹⁷⁸`) is `< 2¹⁸³` — hence `< 2²⁵³ < r`, so it never wraps `Fr`. This is the
    magnitude the range-checked carry decompositions rest on. -/
theorem lazy_t_no_wrap {col0 col3 : ℕ} (h0 : col0 < 2 ^ 178) (h3 : col3 < 2 ^ 178) :
    col0 + 19 * col3 < 2 ^ 253 := by
  have hpos : 0 < (2 : ℕ) ^ 178 := by positivity
  have h183 : (2 : ℕ) ^ 183 = 32 * 2 ^ 178 := by
    rw [show (183 : ℕ) = 178 + 5 from rfl, pow_add]; ring
  have hlt : col0 + 19 * col3 < 2 ^ 183 := by omega
  calc col0 + 19 * col3 < 2 ^ 183 := hlt
    _ < 2 ^ 253 := by
        apply Nat.pow_lt_pow_right (by norm_num)
        norm_num

end Xark
