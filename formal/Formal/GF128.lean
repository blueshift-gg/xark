/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Wrappers
import Mathlib

set_option linter.style.setOption false
set_option linter.style.header false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxHeartbeats 800000

/-!
# GF(2¹²⁸) algebraic infrastructure for GCM / GHASH

GHASH multiplies 128-bit blocks in the binary field
`GF(2¹²⁸) = GF(2)[x] / (x¹²⁸ + x⁷ + x² + x + 1)`
(NIST SP 800-38D §6.3). This file establishes the field's *computational* model
in the same style `Formal.GF256` uses for the AES GF(2⁸) field: the carryless
polynomial product reduced modulo the GCM polynomial, on `ℕ` bit representations.

* `gf128_timesX` — multiply a reduced 128-bit value by `x` (shift + conditional
  fold `x¹²⁸ ≡ x⁷ + x² + x + 1`, the constant `0x87`), matching the `V ← V<<1 ⊕
  V[127]·R` step of the gadget's bit-serial multiply.
* `gf128_xpow k` — `xᵏ mod P`, the reduction table entry the cross-product bit `k`
  reads (`k = i + j`, `i, j < 128`).
* `gf128_mul` — the GF(2¹²⁸) product on 128-bit values, matching the gadget's
  emission (each output bit is the GF(2) parity-sum of cross-products).
* `gf128_mul_lt_two128` — the product is closed in `[0, 2¹²⁸)` (well-defined).

The gadget (`crates/xark-aes::gf128_mul`) computes this same product bit-serially
(NIST Algorithm 1); its mult-gate shape is pinned to this model by the
`gf128_mul_matches_lean_model` R1CS↔Lean bridge test.
-/

namespace Xark

/-- Extract bit `i` (LSB-first) of a natural number. -/
def gf128_bit (n i : ℕ) : ℕ := (n / 2 ^ i) % 2

/-- Multiply a reduced value `v < 2¹²⁸` by `x` in the GCM field: shift left by one
(`2 * v`) and, if that overflows bit 127 (bit 128 of `2v` is set), fold in the
reduction polynomial `x⁷ + x² + x + 1 = 0x87` and clear bit 128. This is exactly
the gadget's `V ← (V << 1) ⊕ (carry · R)` step (in the GCM bit convention `R`'s set
bits are `{0,1,2,7}`, i.e. the byte `0x87`). -/
def gf128_timesX (v : ℕ) : ℕ :=
  (2 * v % 2 ^ 128) ^^^ (0x87 * (2 * v / 2 ^ 128))

/-- `xᵏ mod P`, built by iterating [`gf128_timesX`] from `x⁰ = 1`. -/
def gf128_xpow : ℕ → ℕ
  | 0 => 1
  | (k + 1) => gf128_timesX (gf128_xpow k)

/-- Reduction-table coefficient for the `(i, j) → k` cross-product contribution:
`bit k of (x^(i+j) mod P)`. For `i, j < 128` the exponent `i + j` is `< 255`. -/
def gf128_coeff (i j k : ℕ) : ℕ := gf128_bit (gf128_xpow (i + j)) k

/-- `bit k` of the GF(2¹²⁸) product: the GF(2) parity of every cross-product
`bit_i(x) · bit_j(y)` that lands on output bit `k` after reduction. -/
def gf128_prodBit (x y k : ℕ) : ℕ :=
  (∑ i ∈ Finset.range 128, ∑ j ∈ Finset.range 128,
    gf128_coeff i j k * gf128_bit x i * gf128_bit y j) % 2

/-- GF(2¹²⁸) multiplication on 128-bit values (`ℕ` in `[0, 2¹²⁸)`), as the
XOR-parity sum over cross-products per output bit — the same product the gadget's
bit-serial `gf128_mul` computes. -/
def gf128_mul (x y : ℕ) : ℕ :=
  ∑ k ∈ Finset.range 128, gf128_prodBit x y k * 2 ^ k

/-- Every product bit is `0` or `1` (it is a parity, `_ % 2`). -/
theorem gf128_prodBit_lt_2 (x y k : ℕ) : gf128_prodBit x y k < 2 := by
  unfold gf128_prodBit; exact Nat.mod_lt _ (by decide)

/-- **`gf128_mul` is closed in `[0, 2¹²⁸)`** — each output bit is `0/1`, weighted by
`2ᵏ` for `k < 128`, so the maximum is `2¹²⁸ − 1`. The GHASH multiply is therefore
well-defined on 128-bit blocks (mirrors `Formal.GF256.gf256_mul_lt_256`). -/
theorem gf128_mul_lt_two128 (x y : ℕ) : gf128_mul x y < 2 ^ 128 := by
  unfold gf128_mul
  have h_sum_le :
      (∑ k ∈ Finset.range 128, gf128_prodBit x y k * 2 ^ k)
        ≤ ∑ k ∈ Finset.range 128, (2 : ℕ) ^ k := by
    apply Finset.sum_le_sum
    intro k _
    have hb := gf128_prodBit_lt_2 x y k
    have h_pow_pos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
    nlinarith
  have h_geom : (∑ k ∈ Finset.range 128, (2 : ℕ) ^ k) = 2 ^ 128 - 1 := by
    rw [Nat.geomSum_eq (by norm_num) 128]; simp
  omega

/-- `gf128_timesX` (multiply-by-`x`) applied to a reduced value `v < 2¹²⁸` stays in
`[0, 2¹²⁸)`: the low-128-bit shift is `< 2¹²⁸`, the fold `0x87 · carry` is `0` or
`0x87` (`< 2¹²⁸`), and `Nat.xor` of two `< 2¹²⁸` values is `< 2¹²⁸`. -/
theorem gf128_timesX_lt_two128 (v : ℕ) (hv : v < 2 ^ 128) : gf128_timesX v < 2 ^ 128 := by
  unfold gf128_timesX
  -- `s = 2v < 2^129 = 2·2^128`, so the carry `s / 2^128 ≤ 1`.
  have hpow : (2 : ℕ) ^ 129 = 2 * 2 ^ 128 := by ring
  have hs : 2 * v < 2 ^ 129 := by omega
  have hcarry : (2 * v) / 2 ^ 128 ≤ 1 := by
    have hlt : (2 * v) / 2 ^ 128 < 2 :=
      (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
    omega
  have hlo : (2 * v) % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  have hfold : 0x87 * ((2 * v) / 2 ^ 128) < 2 ^ 128 := by
    have : 0x87 * ((2 * v) / 2 ^ 128) ≤ 0x87 * 1 := by
      exact Nat.mul_le_mul_left _ hcarry
    have h87 : (0x87 : ℕ) < 2 ^ 128 := by norm_num
    omega
  have := Nat.xor_lt_two_pow (n := 128) hlo hfold
  simpa using this

/-! ## The bit-serial multiply (NIST SP 800-38D Algorithm 1)

The gadget computes `gf128_mul` bit-serially: a running value `V` (initialised to
`Y`) is multiplied by `x` each step (`gf128_timesX`), and the accumulator `Z`
XORs in `V` whenever the corresponding bit of `X` is set. The following model the
recurrence directly and prove it stays a valid 128-bit value. -/

/-- The bit-serial running value `V` after `i` steps: `x^i · Y mod P`, computed by
iterating [`gf128_timesX`] from `Y` (the gadget's `V ← (V << 1) ⊕ (V[127]·R)`). -/
def gf128_V (y : ℕ) : ℕ → ℕ
  | 0 => y
  | (i + 1) => gf128_timesX (gf128_V y i)

/-- The bit-serial accumulator `Z` after `i` steps: `⊕_{t < i} X_t · V_t`. -/
def gf128_Z (x y : ℕ) : ℕ → ℕ
  | 0 => 0
  | (i + 1) => (gf128_Z x y i) ^^^ (gf128_bit x i * gf128_V y i)

/-- The full 128-step bit-serial multiply — the gadget's `gf128_mul` algorithm. -/
def gf128_bitserial (x y : ℕ) : ℕ := gf128_Z x y 128

/-- Every running value `V_i` stays a reduced 128-bit element (by [`gf128_timesX_lt_two128`]). -/
theorem gf128_V_lt_two128 (y : ℕ) (hy : y < 2 ^ 128) (i : ℕ) : gf128_V y i < 2 ^ 128 := by
  induction i with
  | zero => exact hy
  | succ n ih => exact gf128_timesX_lt_two128 _ ih

/-- The accumulator stays a 128-bit value: each step XORs in `X_i · V_i` (`0` or a
reduced `V_i`), and `Nat.xor` of two `< 2¹²⁸` values is `< 2¹²⁸`. -/
theorem gf128_Z_lt_two128 (x y : ℕ) (hy : y < 2 ^ 128) (i : ℕ) : gf128_Z x y i < 2 ^ 128 := by
  induction i with
  | zero => simp only [gf128_Z]; positivity
  | succ n ih =>
    unfold gf128_Z
    have hb : gf128_bit x n ≤ 1 := by
      have : (x / 2 ^ n) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      unfold gf128_bit; omega
    have hterm : gf128_bit x n * gf128_V y n < 2 ^ 128 := by
      have hVlt := gf128_V_lt_two128 y hy n
      calc gf128_bit x n * gf128_V y n
          ≤ 1 * gf128_V y n := Nat.mul_le_mul_right _ hb
        _ = gf128_V y n := one_mul _
        _ < 2 ^ 128 := hVlt
    exact Nat.xor_lt_two_pow ih hterm

/-- **The bit-serial multiply is well-defined**: it produces a reduced 128-bit
element. (Its equality to the field product [`gf128_mul`] is the deeper soundness
statement; the R1CS↔Lean bridge test pins the gadget to this recurrence's shape.) -/
theorem gf128_bitserial_lt_two128 (x y : ℕ) (hy : y < 2 ^ 128) : gf128_bitserial x y < 2 ^ 128 :=
  gf128_Z_lt_two128 x y hy 128

/-! ## Soundness: the bit-serial multiply *is* the field product

We prove `gf128_bitserial x y = gf128_mul x y`. The crux is that `gf128_timesX`
computes bit `k` of `x·v` as a fixed GF(2)-linear function of the bits of `v`
(shift + fold), from which a 128-step induction gives the running value's bit `k`
as the reduction-weighted parity of `y`'s bits — matching `gf128_mul` per bit. -/

/-- Bridge from the `div/mod` bit to `Nat.testBit` (for mathlib's bit API). -/
theorem gf128_bit_eq_testBit (n i : ℕ) : gf128_bit n i = (Nat.testBit n i).toNat := by
  unfold gf128_bit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;> simp [h]

/-- Each bit value is `0` or `1`. -/
theorem gf128_bit_le_one (n i : ℕ) : gf128_bit n i ≤ 1 := by
  rw [gf128_bit_eq_testBit]; cases Nat.testBit n i <;> simp

/-- For a reduced `v < 2¹²⁸`, the bit shifted out by the `×2` is `v`'s top bit. -/
theorem gf128_timesX_carry (v : ℕ) (hv : v < 2 ^ 128) : 2 * v / 2 ^ 128 = gf128_bit v 127 := by
  have hpow : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by ring
  have h1 : 2 * v / 2 ^ 128 = v / 2 ^ 127 := by
    rw [hpow]; exact Nat.mul_div_mul_left v (2 ^ 127) (by norm_num)
  have hlt : v / 2 ^ 127 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc v < 2 ^ 128 := hv
      _ = 2 * 2 ^ 127 := hpow
  unfold gf128_bit
  omega

/-- The shifted bit `(2·v)[k]` is `0` at `k=0`, else `v[k-1]`. -/
theorem gf128_shift_bit (v k : ℕ) :
    ((2 * v).testBit k).toNat = (if k = 0 then 0 else gf128_bit v (k - 1)) := by
  cases k with
  | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
  | succ k' =>
    rw [Nat.testBit_succ, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
      gf128_bit_eq_testBit]
    simp

/-- Bool-xor as a `mod 2` sum of the two bit values. -/
theorem toNat_xor (a b : Bool) : (a ^^ b).toNat = (a.toNat + b.toNat) % 2 := by
  cases a <;> cases b <;> rfl

/-- **`gf128_timesX` acts GF(2)-linearly on bits** — the key reduction fact. Bit `k`
of `x · v` is the shifted bit `v[k-1]` XOR the fold `v[127] · R[k]` (`R = 0x87`). -/
theorem gf128_timesX_bit (v : ℕ) (hv : v < 2 ^ 128) (k : ℕ) (hk : k < 128) :
    gf128_bit (gf128_timesX v) k =
      ((if k = 0 then 0 else gf128_bit v (k - 1)) + gf128_bit v 127 * gf128_bit 0x87 k) % 2 := by
  have hc : 2 * v / 2 ^ 128 = gf128_bit v 127 := gf128_timesX_carry v hv
  have hc1 : gf128_bit v 127 ≤ 1 := gf128_bit_le_one v 127
  have hfold : ((0x87 * gf128_bit v 127).testBit k).toNat = gf128_bit v 127 * gf128_bit 0x87 k := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with h0 | h1
    · rw [h0]; simp
    · rw [h1, mul_one, one_mul, gf128_bit_eq_testBit 0x87 k]
  conv_lhs => rw [gf128_bit_eq_testBit]
  simp only [gf128_timesX, hc, Nat.testBit_xor, Nat.testBit_mod_two_pow, hk, decide_true,
    Bool.true_and, toNat_xor, gf128_shift_bit, hfold]

/-- `x · 2^j = 2^(j+1)` with no reduction while `j+1 < 128`. -/
theorem gf128_timesX_two_pow (j : ℕ) (h : j + 1 < 128) : gf128_timesX (2 ^ j) = 2 ^ (j + 1) := by
  unfold gf128_timesX
  have h1 : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
  have h2 : (2 : ℕ) ^ (j + 1) < 2 ^ 128 := Nat.pow_lt_pow_right (by norm_num) h
  rw [h1, Nat.mod_eq_of_lt h2, Nat.div_eq_of_lt h2]
  simp

/-- `x^j mod P = 2^j` (no reduction) for `j < 128` — the base-case reduction table. -/
theorem gf128_xpow_small (j : ℕ) (h : j < 128) : gf128_xpow j = 2 ^ j := by
  induction j with
  | zero => rfl
  | succ n ih => rw [gf128_xpow, ih (by omega), gf128_timesX_two_pow n (by omega)]

/-- `gf128_coeff 0 j k = if j = k then 1 else 0` (the identity reduction table row). -/
theorem gf128_coeff_zero (j k : ℕ) (hj : j < 128) : gf128_coeff 0 j k = if j = k then 1 else 0 := by
  unfold gf128_coeff
  rw [Nat.zero_add, gf128_xpow_small j hj, gf128_bit_eq_testBit, Nat.testBit_two_pow]
  by_cases h : j = k <;> simp [h]

/-- Every reduction table entry `xᵏ mod P` is a reduced 128-bit value. -/
theorem gf128_xpow_lt_two128 (k : ℕ) : gf128_xpow k < 2 ^ 128 := by
  induction k with
  | zero => norm_num [gf128_xpow]
  | succ n ih => exact gf128_timesX_lt_two128 _ ih

/-- The reduction-weighted parity of `y`'s bits — the claimed bit `k` of `y · xⁱ mod P`. -/
def gf128_Ycoeff (y i k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range 128, gf128_coeff i j k * gf128_bit y j) % 2

/-- One reduction step of a coefficient: `coeff (i+1) j k` is `timesX` applied to
`coeff i j ·`, i.e. its shift XOR fold (by [`gf128_timesX_bit`] on `xpow (i+j)`). -/
theorem gf128_coeff_succ (i j k : ℕ) (hk : k < 128) :
    gf128_coeff (i + 1) j k =
      ((if k = 0 then 0 else gf128_coeff i j (k - 1)) + gf128_coeff i j 127 * gf128_bit 0x87 k) % 2 := by
  unfold gf128_coeff
  have hstep : gf128_xpow (i + 1 + j) = gf128_timesX (gf128_xpow (i + j)) := by
    rw [show i + 1 + j = (i + j) + 1 by ring, gf128_xpow]
  rw [hstep, gf128_timesX_bit _ (gf128_xpow_lt_two128 _) k hk]

/-- Dropping an inner `% 2` under a `Σ (· * gᵢ) % 2`: since `fᵢ % 2 ≡ fᵢ (mod 2)`. -/
theorem sum_mul_mod_two (s : Finset ℕ) (f g : ℕ → ℕ) :
    (∑ j ∈ s, f j % 2 * g j) % 2 = (∑ j ∈ s, f j * g j) % 2 := by
  rw [Finset.sum_nat_mod s 2 (fun j => f j % 2 * g j), Finset.sum_nat_mod s 2 (fun j => f j * g j)]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Nat.mul_mod, Nat.mod_mod]

/-- **`Ycoeff` satisfies the same reduction recurrence** as the running value's bits:
`Ycoeff (i+1) k = (shift ⊕ fold) mod 2`. This is the length-128 `Finset` sum push of
[`gf128_coeff_succ`], and is what makes the invariant a clean induction. -/
theorem gf128_Ycoeff_succ (y n k : ℕ) (hk : k < 128) :
    gf128_Ycoeff y (n + 1) k =
      ((if k = 0 then 0 else gf128_Ycoeff y n (k - 1)) + gf128_Ycoeff y n 127 * gf128_bit 0x87 k) %
        2 := by
  -- Expand `coeff (n+1)` and drop the inner `% 2`.
  have h1 : gf128_Ycoeff y (n + 1) k =
      (∑ j ∈ Finset.range 128,
        ((if k = 0 then 0 else gf128_coeff n j (k - 1)) + gf128_coeff n j 127 * gf128_bit 0x87 k) *
          gf128_bit y j) % 2 := by
    unfold gf128_Ycoeff
    rw [Finset.sum_congr rfl (fun j _ => by rw [gf128_coeff_succ n j k hk])]
    exact sum_mul_mod_two _ _ _
  -- Distribute `(A + B)·yⱼ` and split the sum; factor the `if` and `R` out.
  rw [h1, Finset.sum_congr rfl (fun j _ => add_mul _ _ _), Finset.sum_add_distrib]
  have hAsum : (∑ j ∈ Finset.range 128, (if k = 0 then 0 else gf128_coeff n j (k - 1)) * gf128_bit y j)
      = if k = 0 then 0 else ∑ j ∈ Finset.range 128, gf128_coeff n j (k - 1) * gf128_bit y j := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · simp only [if_neg hk0]
  have hBsum : (∑ j ∈ Finset.range 128, gf128_coeff n j 127 * gf128_bit 0x87 k * gf128_bit y j)
      = gf128_bit 0x87 k * ∑ j ∈ Finset.range 128, gf128_coeff n j 127 * gf128_bit y j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hAsum, hBsum, gf128_Ycoeff, gf128_Ycoeff]
  -- Final `mod 2` normalisation: case the bit `R ∈ {0,1}` and `k = 0`.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (gf128_bit_le_one 0x87 k) with hR | hR <;>
    · rw [hR]; by_cases hk0 : k = 0 <;> simp only [hk0, if_true, if_false, if_neg] <;> omega

/-- **The invariant**: bit `k` of `V_i = xⁱ·Y mod P` is the reduction-weighted parity
of `Y`'s bits. Clean induction: base `gf128_coeff_zero`, step `gf128_timesX_bit`
(value) matched to `gf128_Ycoeff_succ` (coefficient). -/
theorem gf128_V_bit (y : ℕ) (hy : y < 2 ^ 128) (i k : ℕ) (hk : k < 128) :
    gf128_bit (gf128_V y i) k = gf128_Ycoeff y i k := by
  induction i generalizing k with
  | zero =>
    simp only [gf128_V, gf128_Ycoeff]
    have hc : (∑ j ∈ Finset.range 128, gf128_coeff 0 j k * gf128_bit y j)
        = ∑ j ∈ Finset.range 128, if j = k then gf128_bit y j else 0 := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [gf128_coeff_zero j k (Finset.mem_range.mp hj)]; split <;> simp
    rw [hc, Finset.sum_ite_eq' (Finset.range 128) k (fun j => gf128_bit y j)]
    simp only [Finset.mem_range.mpr hk, if_true]
    have := gf128_bit_le_one y k; omega
  | succ n ih =>
    rw [gf128_V, gf128_timesX_bit _ (gf128_V_lt_two128 y hy n) k hk, gf128_Ycoeff_succ y n k hk]
    by_cases hk0 : k = 0
    · simp [hk0, ih 127 (by norm_num)]
    · rw [if_neg hk0, if_neg hk0, ih (k - 1) (by omega), ih 127 (by norm_num)]

/-- Bit `k` of a `Nat.xor` is the `mod 2` sum of the two bits. -/
theorem gf128_bit_xor (a b k : ℕ) : gf128_bit (a ^^^ b) k = (gf128_bit a k + gf128_bit b k) % 2 := by
  rw [gf128_bit_eq_testBit, gf128_bit_eq_testBit, gf128_bit_eq_testBit, Nat.testBit_xor, toNat_xor]

/-- Multiplying by a bit `∈ {0,1}` commutes with taking a bit. -/
theorem gf128_bit_mul_bit (x m v k : ℕ) :
    gf128_bit (gf128_bit x m * v) k = gf128_bit x m * gf128_bit v k := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (gf128_bit_le_one x m) with h | h <;>
    rw [h] <;> simp [gf128_bit]

/-- **Step A — bit `k` of the accumulator `Z`** is the XOR-parity of the selected
running values: `⊕_{i<m} X_i · bit_k(V_i)`. Induction on `m` via [`gf128_bit_xor`]. -/
theorem gf128_Z_bit (x y : ℕ) (k m : ℕ) :
    gf128_bit (gf128_Z x y m) k =
      (∑ i ∈ Finset.range m, gf128_bit x i * gf128_bit (gf128_V y i) k) % 2 := by
  induction m with
  | zero => simp [gf128_Z, gf128_bit]
  | succ n ih =>
    rw [gf128_Z, gf128_bit_xor, ih, gf128_bit_mul_bit, Finset.sum_range_succ]
    omega

/-- Adding a multiple of `2^(k+1)` leaves bit `k` unchanged. -/
theorem gf128_bit_add_two_pow_succ_mul (a b k : ℕ) :
    gf128_bit (a + 2 ^ (k + 1) * b) k = gf128_bit a k := by
  unfold gf128_bit
  have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
  rw [show 2 ^ (k + 1) * b = 2 * b * 2 ^ k by ring, Nat.add_mul_div_right _ _ hpos]
  omega

/-- **Step D — digit extraction**: for a base-2 digit sum with `0/1` digits, bit `k`
recovers digit `k`. This is exactly `gf128_bit (gf128_mul …) = gf128_prodBit …`. -/
theorem digit_sum_bit (d : ℕ → ℕ) (hd : ∀ i, d i < 2) :
    ∀ N k, k < N → gf128_bit (∑ i ∈ Finset.range N, d i * 2 ^ i) k = d k := by
  intro N
  induction N with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k n with hkn | hkn
    · -- k < n: the top term is a multiple of 2^(k+1); drop it and recurse.
      have hexp : d n * 2 ^ n = 2 ^ (k + 1) * (d n * 2 ^ (n - (k + 1))) := by
        rw [mul_comm (2 ^ (k + 1)), mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
      rw [hexp, gf128_bit_add_two_pow_succ_mul]
      exact ih k hkn
    · -- k = n: the low part is < 2^k, so bit k reads digit n.
      have hkn' : k = n := by omega
      subst hkn'
      have hlow : (∑ i ∈ Finset.range k, d i * 2 ^ i) < 2 ^ k := by
        calc (∑ i ∈ Finset.range k, d i * 2 ^ i)
            ≤ ∑ i ∈ Finset.range k, 1 * 2 ^ i := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              have := hd i; have := pow_pos (show 0 < 2 by norm_num) i; nlinarith
          _ = 2 ^ k - 1 := by
              rw [Finset.sum_congr rfl (fun i _ => one_mul _), Nat.geomSum_eq (by norm_num)]; simp
          _ < 2 ^ k := by have := pow_pos (show 0 < 2 by norm_num) k; omega
      unfold gf128_bit
      rw [Nat.add_mul_div_right _ _ (pow_pos (show 0 < 2 by norm_num) k), Nat.div_eq_of_lt hlow]
      have := hd k; omega

/-- Bit `k` of the field product is the parity `gf128_prodBit x y k` (for `k < 128`). -/
theorem gf128_mul_bit (x y k : ℕ) (hk : k < 128) :
    gf128_bit (gf128_mul x y) k = gf128_prodBit x y k :=
  digit_sum_bit (fun k' => gf128_prodBit x y k') (fun i => gf128_prodBit_lt_2 x y i) 128 k hk

/-- **Step C — combine**: the XOR-parity of the `Ycoeff`-weighted `X` bits is exactly
`gf128_prodBit`. Drops the inner `% 2` ([`sum_mul_mod_two`]) and reorders the double
sum to the cross-product form. -/
theorem gf128_combine (x y k : ℕ) :
    (∑ i ∈ Finset.range 128, gf128_bit x i * gf128_Ycoeff y i k) % 2 = gf128_prodBit x y k := by
  unfold gf128_Ycoeff gf128_prodBit
  have h1 : (∑ i ∈ Finset.range 128,
        gf128_bit x i * ((∑ j ∈ Finset.range 128, gf128_coeff i j k * gf128_bit y j) % 2))
      = ∑ i ∈ Finset.range 128,
        ((∑ j ∈ Finset.range 128, gf128_coeff i j k * gf128_bit y j) % 2) * gf128_bit x i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [h1, sum_mul_mod_two (Finset.range 128)
      (fun i => ∑ j ∈ Finset.range 128, gf128_coeff i j k * gf128_bit y j) (fun i => gf128_bit x i)]
  have h2 : (∑ i ∈ Finset.range 128,
        (∑ j ∈ Finset.range 128, gf128_coeff i j k * gf128_bit y j) * gf128_bit x i)
      = ∑ i ∈ Finset.range 128, ∑ j ∈ Finset.range 128,
          gf128_coeff i j k * gf128_bit x i * gf128_bit y j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h2]

/-- **GHASH multiply soundness**: the gadget's bit-serial multiply computes exactly
the GF(2¹²⁸) field product. Bit-by-bit ([`Nat.eq_of_testBit_eq`]): for `k < 128`,
`Z`-accumulation ([`gf128_Z_bit`]) + the running-value invariant ([`gf128_V_bit`]) +
the combine ([`gf128_combine`]) match `gf128_mul`'s digit ([`gf128_mul_bit`]); for
`k ≥ 128` both are `< 2¹²⁸` so the bit is `0`. -/
theorem gf128_bitserial_eq_mul (x y : ℕ) (hy : y < 2 ^ 128) :
    gf128_bitserial x y = gf128_mul x y := by
  have key : ∀ k, gf128_bit (gf128_bitserial x y) k = gf128_bit (gf128_mul x y) k := by
    intro k
    rcases Nat.lt_or_ge k 128 with hk | hk
    · rw [gf128_bitserial, gf128_Z_bit, gf128_mul_bit x y k hk]
      have hV : (∑ i ∈ Finset.range 128, gf128_bit x i * gf128_bit (gf128_V y i) k)
          = ∑ i ∈ Finset.range 128, gf128_bit x i * gf128_Ycoeff y i k :=
        Finset.sum_congr rfl (fun i _ => by rw [gf128_V_bit y hy i k hk])
      rw [hV]; exact gf128_combine x y k
    · have hle : (2 : ℕ) ^ 128 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      unfold gf128_bit
      rw [Nat.div_eq_of_lt (by have := gf128_bitserial_lt_two128 x y hy; omega),
          Nat.div_eq_of_lt (by have := gf128_mul_lt_two128 x y; omega)]
  apply Nat.eq_of_testBit_eq
  intro k
  have hk := key k
  rw [gf128_bit_eq_testBit, gf128_bit_eq_testBit] at hk
  revert hk
  cases Nat.testBit (gf128_bitserial x y) k <;> cases Nat.testBit (gf128_mul x y) k <;> simp

end Xark
