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

/-!
# GF(2^8) algebraic infrastructure for the AES S-box

The AES S-box is `S(x) = Affine(x⁻¹) ⊕ 0x63` where `x⁻¹` is the
multiplicative inverse in GF(2^8) = GF(2)[t] / (t^8 + t^4 + t^3 + t + 1)
(with the convention `0⁻¹ = 0`). This file establishes the algebraic
identities needed by `Formal.Aes.aesSubBytes_bit_sound`:

* `gf256_mul` — GF(2^8) multiplication on byte values (ℕ in `[0, 256)`),
  matching the gadget's cross-product/XOR-chain exactly.
* `gf256_inv` — multiplicative inverse via a precomputed 256-entry table.
* `gf256_mul_inv` — `∀ x ∈ [1, 256), gf256_mul x (gf256_inv x) = 1`.
* `gf256_inv_unique` — `∀ x ∈ [1, 256), y ∈ [0, 256), gf256_mul x y = 1 → y = gf256_inv x`.
* `aesSbox_algebraic_eq_table` — `Affine(gf256_inv x) ⊕ 0x63 = SBOX[x]`.

All facts verified via `native_decide` over the finite range. The
inverse is defined as a literal table (not by `x^254`) so the
`native_decide` compilation stays small.
-/

namespace Xark

/-- GF(2^8) reduction-polynomial bit-pattern table: `gf256_xk_bits k`
is the byte representative of `t^k mod m(t)` for `m(t) = t^8 + t^4 +
t^3 + t + 1`. Used to reduce `t^k` for `k ∈ [8, 15)` (the range of
cross-product exponents `i + j` for `i, j < 8`). Matches
`gf256_xk_bits` in `crates/xark-aes/src/lib.rs` line-for-line. -/
def gf256_xk_bits : Fin 15 → ℕ
  | ⟨0, _⟩  => 0x01
  | ⟨1, _⟩  => 0x02
  | ⟨2, _⟩  => 0x04
  | ⟨3, _⟩  => 0x08
  | ⟨4, _⟩  => 0x10
  | ⟨5, _⟩  => 0x20
  | ⟨6, _⟩  => 0x40
  | ⟨7, _⟩  => 0x80
  | ⟨8, _⟩  => 0x1b
  | ⟨9, _⟩  => 0x36
  | ⟨10, _⟩ => 0x6c
  | ⟨11, _⟩ => 0xd8
  | ⟨12, _⟩ => 0xab
  | ⟨13, _⟩ => 0x4d
  | ⟨14, _⟩ => 0x9a

/-- Extract bit `i` (LSB-first) of a natural number. -/
def gf256_bit (n i : ℕ) : ℕ := (n / 2 ^ i) % 2

/-- Cross-product / reduction-table coefficient for the `(i, j) → k`
contribution: `bit k of (t^(i+j) mod m)` if `i + j < 15`, else `0`. -/
def gf256_coeff (i j k : ℕ) : ℕ :=
  if h : i + j < 15 then gf256_bit (gf256_xk_bits ⟨i + j, h⟩) k else 0

/-- The parity-sum of cross-product contributions to bit `k`, i.e.
`bit k` of `gf256_mul x y`. Defined separately so theorems can
manipulate it without unfolding nested `let`s. -/
def gf256_prodBit (x y k : ℕ) : ℕ :=
  (∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8,
    gf256_coeff i j k * gf256_bit x i * gf256_bit y j) % 2

/-- GF(2^8) multiplication on byte values (`ℕ` representation in
`[0, 256)`). Matches the gadget's emission: for each bit-pair `(i, j) ∈
[0, 8)²`, the cross-product `bit_i(x) AND bit_j(y)` contributes (with
coefficient 1 in GF(2)) to output bit `k` iff `bit k of (t^(i+j) mod m)
= 1`. The result is the XOR-parity sum over all (i, j) per output bit. -/
def gf256_mul (x y : ℕ) : ℕ :=
  ∑ k ∈ Finset.range 8, gf256_prodBit x y k * 2 ^ k

/-- **AES GF(2^8) multiplicative-inverse table** (the standard table
used in the AES S-box; matches `gf256_inv` in
`crates/xark-aes/src/lib.rs`). Entry `i` is the multiplicative inverse
of byte `i`; entry `0` is `0` by convention. Verified at the byte
level by `gf256_mul_inv` below. -/
def gf256_inv_table : List ℕ :=
  [0x00, 0x01, 0x8d, 0xf6, 0xcb, 0x52, 0x7b, 0xd1, 0xe8, 0x4f, 0x29, 0xc0, 0xb0, 0xe1, 0xe5, 0xc7,
   0x74, 0xb4, 0xaa, 0x4b, 0x99, 0x2b, 0x60, 0x5f, 0x58, 0x3f, 0xfd, 0xcc, 0xff, 0x40, 0xee, 0xb2,
   0x3a, 0x6e, 0x5a, 0xf1, 0x55, 0x4d, 0xa8, 0xc9, 0xc1, 0x0a, 0x98, 0x15, 0x30, 0x44, 0xa2, 0xc2,
   0x2c, 0x45, 0x92, 0x6c, 0xf3, 0x39, 0x66, 0x42, 0xf2, 0x35, 0x20, 0x6f, 0x77, 0xbb, 0x59, 0x19,
   0x1d, 0xfe, 0x37, 0x67, 0x2d, 0x31, 0xf5, 0x69, 0xa7, 0x64, 0xab, 0x13, 0x54, 0x25, 0xe9, 0x09,
   0xed, 0x5c, 0x05, 0xca, 0x4c, 0x24, 0x87, 0xbf, 0x18, 0x3e, 0x22, 0xf0, 0x51, 0xec, 0x61, 0x17,
   0x16, 0x5e, 0xaf, 0xd3, 0x49, 0xa6, 0x36, 0x43, 0xf4, 0x47, 0x91, 0xdf, 0x33, 0x93, 0x21, 0x3b,
   0x79, 0xb7, 0x97, 0x85, 0x10, 0xb5, 0xba, 0x3c, 0xb6, 0x70, 0xd0, 0x06, 0xa1, 0xfa, 0x81, 0x82,
   0x83, 0x7e, 0x7f, 0x80, 0x96, 0x73, 0xbe, 0x56, 0x9b, 0x9e, 0x95, 0xd9, 0xf7, 0x02, 0xb9, 0xa4,
   0xde, 0x6a, 0x32, 0x6d, 0xd8, 0x8a, 0x84, 0x72, 0x2a, 0x14, 0x9f, 0x88, 0xf9, 0xdc, 0x89, 0x9a,
   0xfb, 0x7c, 0x2e, 0xc3, 0x8f, 0xb8, 0x65, 0x48, 0x26, 0xc8, 0x12, 0x4a, 0xce, 0xe7, 0xd2, 0x62,
   0x0c, 0xe0, 0x1f, 0xef, 0x11, 0x75, 0x78, 0x71, 0xa5, 0x8e, 0x76, 0x3d, 0xbd, 0xbc, 0x86, 0x57,
   0x0b, 0x28, 0x2f, 0xa3, 0xda, 0xd4, 0xe4, 0x0f, 0xa9, 0x27, 0x53, 0x04, 0x1b, 0xfc, 0xac, 0xe6,
   0x7a, 0x07, 0xae, 0x63, 0xc5, 0xdb, 0xe2, 0xea, 0x94, 0x8b, 0xc4, 0xd5, 0x9d, 0xf8, 0x90, 0x6b,
   0xb1, 0x0d, 0xd6, 0xeb, 0xc6, 0x0e, 0xcf, 0xad, 0x08, 0x4e, 0xd7, 0xe3, 0x5d, 0x50, 0x1e, 0xb3,
   0x5b, 0x23, 0x38, 0x34, 0x68, 0x46, 0x03, 0x8c, 0xdd, 0x9c, 0x7d, 0xa0, 0xcd, 0x1a, 0x41, 0x1c]

/-- GF(2^8) multiplicative inverse: a literal 256-entry table lookup
matching the gadget's `gf256_inv` function. `gf256_inv 0 = 0` by
convention. Verified at the byte level by `gf256_mul_inv` below. -/
def gf256_inv (x : ℕ) : ℕ := (gf256_inv_table[x]?).getD 0

/-! ## Key algebraic facts (verified by `native_decide`)

Each `_all` theorem is a single bounded `∀` over `Fin 256` (or `Fin
256 × Fin 256`) whose body is a closed-form computation in `ℕ`.
`native_decide` compiles the body to bytecode and runs it. Compared
to the previous `x^254`-based definition (which expanded into a
recursive cascade), the table-lookup form keeps the bytecode small. -/

/-- The prodBit is `0` or `1`. -/
theorem gf256_prodBit_lt_2 (x y k : ℕ) : gf256_prodBit x y k < 2 := by
  unfold gf256_prodBit; exact Nat.mod_lt _ (by decide)

/-- **`gf256_mul` is closed in `[0, 256)`** (each output bit is `0` or
`1`, summed weighted by `2^k`; max = `2^8 − 1 = 255`). -/
theorem gf256_mul_lt_256 (x y : ℕ) : gf256_mul x y < 256 := by
  unfold gf256_mul
  have h_sum_le :
      (∑ k ∈ Finset.range 8, gf256_prodBit x y k * 2 ^ k)
        ≤ ∑ k ∈ Finset.range 8, (2 : ℕ) ^ k := by
    apply Finset.sum_le_sum
    intro k _
    have hb := gf256_prodBit_lt_2 x y k
    have h_pow_pos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
    nlinarith
  have h_geom : (∑ k ∈ Finset.range 8, (2 : ℕ) ^ k) = 2 ^ 8 - 1 := by
    rw [Nat.geomSum_eq (by norm_num) 8]; simp
  omega

/-- **`gf256_mul 0 y = 0`**: every cross-product has a zero `x` bit. -/
theorem gf256_mul_zero_left (y : ℕ) : gf256_mul 0 y = 0 := by
  unfold gf256_mul
  apply Finset.sum_eq_zero
  intro k _
  change gf256_prodBit 0 y k * 2 ^ k = 0
  apply mul_eq_zero.mpr; left
  unfold gf256_prodBit gf256_bit
  have h_inner_zero :
      (∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8,
        gf256_coeff i j k * ((0 : ℕ) / 2 ^ i % 2) * (y / 2 ^ j % 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    simp
  rw [h_inner_zero]
  rfl

/-- **`gf256_inv x < 256`** for any byte `x ∈ [0, 256)`. -/
theorem gf256_inv_lt_256_all : ∀ x : Fin 256, gf256_inv x.val < 256 := by
  native_decide

theorem gf256_inv_lt_256 (x : Fin 256) : gf256_inv x.val < 256 :=
  gf256_inv_lt_256_all x

/-- **`gf256_inv 0 = 0`**. -/
theorem gf256_inv_zero : gf256_inv 0 = 0 := by
  native_decide

/-- **Multiplicative inverse correctness.** For every nonzero byte `x ∈
[1, 256)`, `gf256_mul x (gf256_inv x) = 1`. Verified over the 255
nonzero bytes by `native_decide`. -/
theorem gf256_mul_inv_all :
    ∀ x : Fin 256, 0 < x.val → gf256_mul x.val (gf256_inv x.val) = 1 := by
  native_decide

theorem gf256_mul_inv (x : Fin 256) (hx : 0 < x.val) :
    gf256_mul x.val (gf256_inv x.val) = 1 := gf256_mul_inv_all x hx

/-- **Multiplicative inverse uniqueness.** Given a nonzero byte `x ∈
[1, 256)` and any byte `y ∈ [0, 256)`, if `gf256_mul x y = 1` then
`y = gf256_inv x`. Verified over `256 × 256 = 65536` cases by
`native_decide`. This is the inverse-uniqueness fact the AES S-box
gadget soundness proof needs to pin the prover-supplied `x_inv` to
`gf256_inv x`. -/
theorem gf256_inv_unique_all :
    ∀ x y : Fin 256, 0 < x.val → gf256_mul x.val y.val = 1 →
      y.val = gf256_inv x.val := by
  native_decide

theorem gf256_inv_unique (x y : Fin 256) (hx : 0 < x.val)
    (h : gf256_mul x.val y.val = 1) : y.val = gf256_inv x.val :=
  gf256_inv_unique_all x y hx h

/-- GF(2^8) exponentiation by repeated `gf256_mul` (the operation the AES gadget
computes via the Itoh–Tsujii chain, here in its naive folded form). -/
def gf256_pow (x : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => gf256_mul (gf256_pow x n) x

/-- **Itoh–Tsujii inverse.** For every byte `x ∈ [0, 256)`, `x^254` in GF(2^8)
equals the multiplicative inverse `gf256_inv x` (`x^254 = x^(-1)` since `x^255 = 1`
for `x ≠ 0`, and `0^254 = 0 = gf256_inv 0`). This grounds the gadget's algebraic,
table-free S-box (`affine(b^254)`) in the proven inverse. Verified over all 256
bytes by `native_decide` (compiled bytecode — the fold, unlike an unrolled
definition, keeps the bytecode small). -/
theorem gf256_pow254_eq_inv_all : ∀ x : Fin 256, gf256_pow x.val 254 = gf256_inv x.val := by
  native_decide

theorem gf256_pow254_eq_inv (x : Fin 256) : gf256_pow x.val 254 = gf256_inv x.val :=
  gf256_pow254_eq_inv_all x

/-! ## AES affine transform

Affine transform applied to a byte: each output bit `i` is
`bit_i(x) ⊕ bit_{(i+4) mod 8}(x) ⊕ bit_{(i+5) mod 8}(x)
   ⊕ bit_{(i+6) mod 8}(x) ⊕ bit_{(i+7) mod 8}(x)`. The S-box is
`Affine(gf256_inv x) ⊕ 0x63`, per FIPS 197 §5.1.1. -/

/-- AES affine transform on a byte (`ℕ` representation). Each output
bit is the parity of 5 specific input bits. -/
def aesAffine_nat (x : ℕ) : ℕ :=
  let bit (n i : ℕ) : ℕ := (n / 2 ^ i) % 2
  (Finset.range 8).sum fun i =>
    ((bit x i + bit x ((i + 4) % 8) + bit x ((i + 5) % 8)
      + bit x ((i + 6) % 8) + bit x ((i + 7) % 8)) % 2) * 2 ^ i

/-- The algebraic S-box: `Affine(gf256_inv x) ⊕ 0x63`. -/
def aesSbox_algebraic (x : ℕ) : ℕ :=
  Nat.xor (aesAffine_nat (gf256_inv x)) 0x63

/-- **The algebraic S-box matches the lookup table.** `Affine(gf256_inv
x) ⊕ 0x63` equals `aesSboxTable[x]` for every byte `x ∈ [0, 256)`.
Verified by `native_decide`. -/
theorem aesSbox_algebraic_eq_table_all :
    ∀ x : Fin 256, aesSbox_algebraic x.val = (aesSboxTable[x.val]?).getD 0 := by
  native_decide

theorem aesSbox_algebraic_eq_table (x : Fin 256) :
    aesSbox_algebraic x.val = (aesSboxTable[x.val]?).getD 0 :=
  aesSbox_algebraic_eq_table_all x

/-- **Frontend AES S-box soundness.** Our gadget computes the S-box *without a
table*: `affine(b²⁵⁴) ⊕ 0x63`, where `b²⁵⁴` is the Itoh–Tsujii inverse. This
theorem proves that value equals the AES lookup-table S-box for every byte,
composing `gf256_pow254_eq_inv` (`b²⁵⁴ = inv b`) with `aesSbox_algebraic_eq_table`
(`affine(inv b) ⊕ 0x63 = table[b]`). It grounds the `xark-aes` algebraic S-box in
the same table the rest of `Aes.lean` reasons over. -/
theorem aesSbox_pow_eq_table (x : Fin 256) :
    Nat.xor (aesAffine_nat (gf256_pow x.val 254)) 0x63 = (aesSboxTable[x.val]?).getD 0 := by
  rw [gf256_pow254_eq_inv x]
  exact aesSbox_algebraic_eq_table x

/-! ## Byte8 ↔ ℕ recomposition over `ZMod r`-valued wires

The `addMod32` chain in `Formal.Blake` built `Fr ↔ ℕ` bridges for
32-bit-wide wire vectors. The AES S-box gadget's cross-product / XOR
constraints live at the byte (8-bit) width. We provide the byte-width
analogue here.

`r ≈ 2^254` so any 8-bit-or-narrower sum fits with huge margin — the
no-wrap arguments are trivial. -/

/-- Indicator: ℕ value `0` if `w = 0`, `1` if `w = 1`, else `0`
(only meaningful for boolean wires). Used to recompose into ℕ
without case-splitting at every site. -/
def wireBitNat (w : ZMod r) : ℕ := if w = 1 then 1 else 0

theorem wireBitNat_le_one (w : ZMod r) : wireBitNat w ≤ 1 := by
  unfold wireBitNat; split <;> simp

theorem wireBitNat_eq_zero_of_eq_zero {w : ZMod r} (h : w = 0) :
    wireBitNat w = 0 := by
  unfold wireBitNat
  rw [h]
  simp

theorem wireBitNat_eq_one_of_eq_one {w : ZMod r} (h : w = 1) :
    wireBitNat w = 1 := by
  unfold wireBitNat
  rw [h]
  simp

/-- For a `BitOf`-witnessed `Byte8` wire, `wireBitNat (wX j)` equals
`if (x j) then 1 else 0`. -/
theorem wireBitNat_eq_of_BitOf {x : Bool} {w : ZMod r}
    (h : BitOf w x) : wireBitNat w = if x then 1 else 0 := by
  unfold BitOf at h
  unfold wireBitNat
  cases x
  · simp at h
    simp [h, zero_ne_one]
  · simp at h
    simp [h]

/-- ℕ-level byte recomposition of a wire vector: `∑ 2^i · wireBitNat (w
i)`. -/
def byteWireToNat (w : Fin 8 → ZMod r) : ℕ :=
  ∑ i : Fin 8, wireBitNat (w i) * 2 ^ i.val

theorem byteWireToNat_lt_256 (w : Fin 8 → ZMod r) : byteWireToNat w < 256 := by
  unfold byteWireToNat
  have h_each : ∀ i ∈ Finset.univ, wireBitNat (w i) * 2 ^ i.val ≤ 2 ^ i.val := by
    intro i _
    have := wireBitNat_le_one (w i)
    nlinarith [pow_pos (by norm_num : (0:ℕ) < 2) i.val]
  have h_sum : (∑ i : Fin 8, wireBitNat (w i) * 2 ^ i.val) ≤ ∑ i : Fin 8, 2 ^ i.val :=
    Finset.sum_le_sum h_each
  have h_geom : (∑ i : Fin 8, (2 : ℕ) ^ i.val) = 2 ^ 8 - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) 8, Nat.geomSum_eq (by norm_num) 8]
    simp
  omega

/-- For a `BitOf`-witnessed wire vector, `byteWireToNat` agrees with
`byteToNat`. -/
theorem byteWireToNat_eq_byteToNat {x : Byte8} {wX : Fin 8 → ZMod r}
    (hX : ∀ j, BitOf (wX j) (x j)) :
    byteWireToNat wX = byteToNat x := by
  unfold byteWireToNat byteToNat
  apply Finset.sum_congr rfl
  intro i _
  rw [wireBitNat_eq_of_BitOf (hX i)]

end Xark
