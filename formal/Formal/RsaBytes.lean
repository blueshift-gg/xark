/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.GroupedColumns
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `bytes_to_wide`: packing bits into 25×82 limbs

`xark_rsa::bytes_to_wide` decomposes each of 256 bytes with `to_bits::<8>` and places
bit `t` of byte `i` at integer position `8·(255−i) + t` (byte 0 most significant), then
packs the 2048 bits into 25 limbs by

`out q = Σ_{t<82, 82q+t<2048} bits (82q+t) · 2^t`.

Two identities make the packing faithful:

* `packing`: recombining the limbs at their weights is the bit string's value,
  `Σ_{q<25} out q · 2^(82q) = Σ_{j<2048} bits j · 2^j`, by the bijection
  `(q, t) ↦ 82q + t` between the limb grid and `[0, 2048)`;
* `bytes_of_bits`: if each byte is the sum of its eight placed bits, the byte
  string read big-endian is that same value,
  `Σ_{i<256} bytes i · 256^(255−i) = Σ_{j<2048} bits j · 2^j`, by `(i, t) ↦ 8·(255−i)+t`.

So the octet input and the 25×82 limbs denote one number. The per-call pins
(`to_bits::<8>` on every byte, and `out`'s limbs read from `bits`) are the rows'
obligation; this file is the arithmetic they carry.
-/

namespace Xark.Rsa.Bytes

/-- Limb `q` of a packing of width `a` covering `N` bits: the bits of the window
starting at `aq`, the last window truncated at `N`. -/
def limbOf (bits : ℕ → ℤ) (a N q : ℕ) : ℤ :=
  ∑ t ∈ Finset.range a, if a * q + t < N then bits (a * q + t) * 2 ^ t else 0

/-- Limb `q` of `bytes_to_wide`'s 25×82 packing. -/
def limb (bits : ℕ → ℤ) (q : ℕ) : ℤ := limbOf bits 82 2048 q

/-- A position below `N` in a width-`a` grid of `m` limbs. -/
theorem div_mod_lt {j m a N : ℕ} (ha : 0 < a) (hN : N ≤ m * a) (hj : j < N) :
    j / a < m ∧ j % a < a :=
  ⟨(Nat.div_lt_iff_lt_mul ha).mpr (lt_of_lt_of_le hj hN), Nat.mod_lt _ ha⟩

/-- The low digit of `a·q + t` is `t`, for `t < a`. -/
theorem add_mod (a t q : ℕ) (ht : t < a) : (a * q + t) % a = t := by
  rw [Nat.add_comm (a * q) t, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

/-- `a·q + t` as a pair is injective on the limb grid. -/
theorem add_mul_inj {a q q' t t' : ℕ} (ha : 0 < a) (ht : t < a) (ht' : t' < a)
    (h : a * q + t = a * q' + t') : q = q' ∧ t = t' := by
  have hmod : t % a = t' % a := by
    rw [← add_mod a t q ht, ← add_mod a t' q' ht', h]
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at hmod
  have hq : a * q = a * q' := by omega
  constructor
  · exact Nat.mul_left_cancel ha hq
  · exact hmod

/-- **The packing recombines to the bit string.** Rebuilding each limb at its weight
gives the whole `N`-bit number: `Σ_q limb_q · 2^(aq) = Σ_{j<N} bits j · 2^j`. The
bijection is `(q, t) ↦ aq + t` between the limb grid and `[0, N)`. -/
theorem packing_of (bits : ℕ → ℤ) (m a N : ℕ) (ha : 0 < a) (hN : N ≤ m * a) :
    ∑ q ∈ Finset.range m, limbOf bits a N q * 2 ^ (a * q)
      = ∑ j ∈ Finset.range N, bits j * 2 ^ j := by
  have hlimb : ∀ q, limbOf bits a N q * 2 ^ (a * q) =
      ∑ t ∈ Finset.range a,
        if a * q + t < N then bits (a * q + t) * 2 ^ (a * q + t) else 0 := by
    intro q
    rw [limbOf, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : a * q + t < N
    · rw [if_pos h, if_pos h, mul_assoc, ← pow_add, Nat.add_comm]
    · rw [if_neg h, if_neg h, zero_mul]
  have hflat : (∑ q ∈ Finset.range m, ∑ t ∈ Finset.range a,
        if a * q + t < N then bits (a * q + t) * 2 ^ (a * q + t) else 0)
      = ∑ p ∈ Finset.range m ×ˢ Finset.range a,
        (if a * p.1 + p.2 < N then bits (a * p.1 + p.2) * 2 ^ (a * p.1 + p.2) else 0) := by
    rw [Finset.sum_product]
  simp only [hlimb, hflat]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun p _ => a * p.1 + p.2) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  · intro p hp p' hp' h
    obtain ⟨_, hpt⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    obtain ⟨_, hpt'⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp').1
    have h1 := add_mul_inj ha (Finset.mem_range.mp hpt) (Finset.mem_range.mp hpt') h
    exact Prod.ext h1.1 h1.2
  · intro j hj
    obtain ⟨hjq, hjt⟩ := div_mod_lt ha hN (Finset.mem_range.mp hj)
    refine ⟨(j / a, j % a), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_range.mpr hjq
      · exact Finset.mem_range.mpr hjt
      · rw [Nat.div_add_mod]
        exact Finset.mem_range.mp hj
    · rw [Nat.div_add_mod]
  · intro p _
    rfl

/-- **The 25×82 packing recombines to the 2048-bit string.** -/
theorem packing (bits : ℕ → ℤ) :
    ∑ q ∈ Finset.range 25, limb bits q * 2 ^ (82 * q)
      = ∑ j ∈ Finset.range 2048, bits j * 2 ^ j :=
  packing_of bits 25 82 2048 (by norm_num) (by norm_num)

/-- The low digit of `8·(255 − i) + t` is `t`, for `t < 8`. -/
theorem byte_add_mod (t i : ℕ) (ht : t < 8) : (8 * (255 - i) + t) % 8 = t := by
  rw [Nat.add_comm (8 * (255 - i)) t, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

/-- Placed byte positions are injective: `(i, t) ↦ 8·(255 − i) + t`. -/
theorem byte_inj {i i' t t' : ℕ} (hi : i < 256) (hi' : i' < 256) (ht : t < 8) (ht' : t' < 8)
    (h : 8 * (255 - i) + t = 8 * (255 - i') + t') : i = i' ∧ t = t' := by
  have hmod : t % 8 = t' % 8 := by
    rw [← byte_add_mod t i ht, ← byte_add_mod t' i' ht', h]
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at hmod
  constructor <;> omega

set_option maxRecDepth 100000 in
/-- **The big-endian byte string is the bit string.** If each byte is the sum of its
eight placed bits, the byte string read big-endian is exactly `Σ_j bits j · 2^j` — the
octet-input half of `bytes_to_wide`. -/
theorem bytes_of_bits (bits bytes : ℕ → ℤ)
    (hbyte : ∀ i < 256, bytes i =
      ∑ t ∈ Finset.range 8, bits (8 * (255 - i) + t) * 2 ^ t) :
    ∑ i ∈ Finset.range 256, bytes i * 256 ^ (255 - i)
      = ∑ j ∈ Finset.range 2048, bits j * 2 ^ j := by
  have hstep : ∀ i < 256, bytes i * 256 ^ (255 - i) =
      ∑ t ∈ Finset.range 8, bits (8 * (255 - i) + t) * 2 ^ (8 * (255 - i) + t) := by
    intro i hi
    rw [hbyte i hi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show (256 : ℤ) = 2 ^ 8 by norm_num, ← pow_mul, mul_assoc, ← pow_add, Nat.add_comm]
  calc ∑ i ∈ Finset.range 256, bytes i * 256 ^ (255 - i)
      = ∑ i ∈ Finset.range 256, ∑ t ∈ Finset.range 8,
          bits (8 * (255 - i) + t) * 2 ^ (8 * (255 - i) + t) :=
        Finset.sum_congr rfl fun i hi => hstep i (Finset.mem_range.mp hi)
    _ = ∑ p ∈ Finset.range 256 ×ˢ Finset.range 8,
          bits (8 * (255 - p.1) + p.2) * 2 ^ (8 * (255 - p.1) + p.2) := by
        rw [Finset.sum_product]
    _ = ∑ j ∈ Finset.range 2048, bits j * 2 ^ j := by
        refine Finset.sum_bij (fun p _ => 8 * (255 - p.1) + p.2) ?_ ?_ ?_ ?_
        · intro p hp
          obtain ⟨hpi, hpt⟩ := Finset.mem_product.mp hp
          have hi := Finset.mem_range.mp hpi
          have ht := Finset.mem_range.mp hpt
          exact Finset.mem_range.mpr (by omega)
        · intro p hp p' hp' h
          obtain ⟨hpi, hpt⟩ := Finset.mem_product.mp hp
          obtain ⟨hpi', hpt'⟩ := Finset.mem_product.mp hp'
          have h1 := byte_inj (Finset.mem_range.mp hpi) (Finset.mem_range.mp hpi')
            (Finset.mem_range.mp hpt) (Finset.mem_range.mp hpt') h
          exact Prod.ext h1.1 h1.2
        · intro j hj
          have hj' := Finset.mem_range.mp hj
          have hi : 255 - j / 8 < 256 := by omega
          have ht : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
          refine ⟨(255 - j / 8, j % 8), ?_, ?_⟩
          · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr ht⟩
          · change 8 * (255 - (255 - j / 8)) + j % 8 = j
            have h : 255 - (255 - j / 8) = j / 8 := by omega
            rw [h, Nat.div_add_mod]
        · intro p _
          rfl

/-- **`bytes_to_wide` denotes one number.** The 25 packed limbs and the 256-byte
big-endian input have the same value: `Σ_q out_q·2^(82q) = Σ_i bytes_i·256^(255−i)`,
given the rows place each byte's bits at `8·(255−i)+t`. -/
theorem bytes_to_wide (bits bytes : ℕ → ℤ)
    (hbyte : ∀ i < 256, bytes i =
      ∑ t ∈ Finset.range 8, bits (8 * (255 - i) + t) * 2 ^ t) :
    ∑ q ∈ Finset.range 25, limb bits q * 2 ^ (82 * q)
      = ∑ i ∈ Finset.range 256, bytes i * 256 ^ (255 - i) := by
  rw [packing, bytes_of_bits bits bytes hbyte]

end Xark.Rsa.Bytes
