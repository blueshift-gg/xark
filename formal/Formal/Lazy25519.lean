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

`crates/xark-bignum/src/lib.rs`'s `mul_lazy_25519` multiplies two 3×85-bit
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

end Xark
