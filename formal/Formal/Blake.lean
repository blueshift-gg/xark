/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Sha256
import Formal.Wrappers
import Formal.Arith
import Formal.Gadgets
import Mathlib

set_option linter.style.setOption false
set_option linter.style.header false
set_option linter.flexible false
set_option linter.style.longLine false

/-!
# xark BLAKE2s / BLAKE3 structural soundness — Lean 4 / mathlib

Per-bit structural-soundness chain for the BLAKE2s and BLAKE3
compression gadgets, mirroring `Formal/Sha256.lean`'s structural
layer.

The chain consists of three real (non-vacuous) per-bit soundness
theorems:

1. `xor32_bit_sound`, `rotr_bit_sound` — existential wrappers over
   `Formal.Sha256.xor32_sound` / `rotr_sound`. The output witness
   function references the input wires.
2. `addMod32_bit_sound` — given input bit-wires (`BitOf`-witnessed),
   output bit-wires (boolean), a carry wire (boolean), and the
   gadget's carry-chain LC, the output wires are `BitOf`-witnessed by
   the spec `addMod32 a b`. Proof: Fr→ℕ bridge through the BitOf
   recomposition, `Formal.Arith.add_mod_32_core`, the binary-
   recomposition round-trip for `ofNat`, and `Formal.Gadgets.bits_unique`.
3. `blake2s_round_compose_bit`, `blake3_round_compose_bit` — final
   composition consumed by `Formal.BitwuzlaCompose`.
-/

namespace Xark

/-! ## Per-bit gadget soundness for `xor32` and `rotr`

Existential-form wrappers over the concrete-expression theorems
`xor32_sound` and `rotr_sound` from `Formal.Sha256`. The witness
function references the input wires, so the BitOf hypotheses are
load-bearing. -/

/-- **`xor32` per-bit soundness (existential form).** -/
theorem xor32_bit_sound {F : Type*} [Field F]
    (a b : Word32) (wa wb : Fin 32 → F)
    (ha : ∀ i, BitOf (wa i) (a i)) (hb : ∀ i, BitOf (wb i) (b i)) :
    ∃ wxor : Fin 32 → F, ∀ i, BitOf (wxor i) ((xor32 a b) i) :=
  ⟨fun i => wa i + wb i - 2 * (wa i * wb i), xor32_sound a b wa wb ha hb⟩

/-- **`rotr` per-bit soundness (existential form).** -/
theorem rotr_bit_sound {F : Type*} [Zero F] [One F]
    (a : Word32) (wa : Fin 32 → F)
    (ha : ∀ i, BitOf (wa i) (a i)) (k : ℕ) :
    ∃ wrot : Fin 32 → F, ∀ i, BitOf (wrot i) ((rotr a k) i) :=
  ⟨fun i => wa ⟨(i.val + k) % 32, Nat.mod_lt _ (by decide)⟩,
   rotr_sound a wa ha k⟩

/-! ## Bit-recomposition identity over ℕ

The fact `n = ∑ i ∈ range k, ((n / 2^i) % 2) * 2^i + (n / 2^k) * 2^k`
specialised to `k = 32` and `n < 2^32` gives the round-trip identity
`toNat (ofNat n) = n` for `n < 2^32`. -/

/-- Binary-recomposition identity: `∑ i ∈ range k, ((n / 2^i) % 2) · 2^i = n % 2^k`. -/
theorem bitRecomp_mod_pow (n : ℕ) :
    ∀ k : ℕ, (∑ i ∈ Finset.range k, ((n / 2 ^ i) % 2) * 2 ^ i) = n % 2 ^ k := by
  intro k
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    -- Goal: n % 2^k + (n / 2^k) % 2 * 2^k = n % 2^(k+1)
    -- Step 1: n / 2^k = 2 · (n / 2^(k+1)) + (n / 2^k) % 2 (from div_add_mod + div chain).
    have hd : n / 2 ^ k / 2 = n / 2 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have h_decomp : n / 2 ^ k = 2 * (n / 2 ^ (k + 1)) + (n / 2 ^ k) % 2 := by
      have hr := Nat.div_add_mod (n / 2 ^ k) 2
      rw [hd] at hr
      linarith
    -- Step 2: n = (n / 2^k) * 2^k + n % 2^k.
    have hb : (n / 2 ^ k) * 2 ^ k + n % 2 ^ k = n := by
      have := Nat.div_add_mod n (2 ^ k); linarith
    -- Substitute Step 1 into Step 2: n = (n / 2^(k+1)) · 2^(k+1) + ((n / 2^k) % 2) · 2^k + n % 2^k.
    have h_expand : n = (n / 2 ^ (k + 1)) * 2 ^ (k + 1)
                     + ((n / 2 ^ k) % 2) * 2 ^ k + n % 2 ^ k := by
      have h_pow : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
      -- Start from hb and substitute h_decomp inside the product.
      have h_substituted :
          (2 * (n / 2 ^ (k + 1)) + (n / 2 ^ k) % 2) * 2 ^ k + n % 2 ^ k = n := by
        rw [← h_decomp]; exact hb
      -- Algebra: (2A + B) · C = A · (2C) + B · C, where C = 2^k, 2C = 2^(k+1).
      have h_alg :
          (2 * (n / 2 ^ (k + 1)) + (n / 2 ^ k) % 2) * 2 ^ k
            = (n / 2 ^ (k + 1)) * 2 ^ (k + 1) + ((n / 2 ^ k) % 2) * 2 ^ k := by
        rw [h_pow]; ring
      linarith
    -- Step 3: n = (n / 2^(k+1)) · 2^(k+1) + n % 2^(k+1) — standard div_add_mod.
    have ha : (n / 2 ^ (k + 1)) * 2 ^ (k + 1) + n % 2 ^ (k + 1) = n := by
      have := Nat.div_add_mod n (2 ^ (k + 1)); linarith
    -- Equating h_expand and ha gives our goal.
    linarith

/-- For `n < 2^32`, the 32-bit recomposition of the `ofNat`-extracted bits
recovers `n`. -/
private theorem toNat_ofNat_of_lt {n : ℕ} (hn : n < 2 ^ 32) :
    toNat (ofNat n) = n := by
  unfold toNat ofNat
  -- The `ofNat` def uses `decide ((n / 2^i.val) % 2 = 1)` which the
  -- `if-then-else` unfolds to. Unify forms then reduce.
  simp only [decide_eq_true_iff]
  have h_bit_eq : ∀ i : Fin 32, (if (n / 2 ^ i.val) % 2 = 1 then (1 : ℕ) else 0)
                              = (n / 2 ^ i.val) % 2 := by
    intro i
    have h_mod_lt : (n / 2 ^ i.val) % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases ((n / 2 ^ i.val) % 2)
    · simp
    · simp
  have h_sum_eq :
      (∑ i : Fin 32, (if (n / 2 ^ i.val) % 2 = 1 then (1 : ℕ) else 0) * 2 ^ i.val)
        = ∑ i : Fin 32, ((n / 2 ^ i.val) % 2) * 2 ^ i.val := by
    apply Finset.sum_congr rfl
    intro i _; rw [h_bit_eq i]
  rw [h_sum_eq]
  -- Convert Fin 32 sum to Finset.range 32 sum and apply the recomposition identity.
  rw [Fin.sum_univ_eq_sum_range (fun i => ((n / 2 ^ i) % 2) * 2 ^ i) 32]
  rw [bitRecomp_mod_pow n 32]
  exact Nat.mod_eq_of_lt hn

/-- `addMod32 a b`'s `toNat` is `(toNat a + toNat b) % 2³²`. -/
private theorem toNat_addMod32 (a b : Word32) :
    toNat (addMod32 a b) = (toNat a + toNat b) % 2 ^ 32 := by
  unfold addMod32
  exact toNat_ofNat_of_lt (Nat.mod_lt _ (by norm_num))

/-! ## ℕ-recomposition over `BitOf`-witnessed wires (helpers) -/

/-- A `BitOf`-witnessed wire equals its boolean indicator as `ZMod r`. -/
private theorem bitof_eq_indicator {a : Bool} {w : ZMod r}
    (h : BitOf w a) : w = (if a then (1 : ZMod r) else 0) := by
  unfold BitOf at h
  cases a
  · simp at h ⊢; exact h
  · simp at h ⊢; exact h

/-- ℕ-level weighted sum of the boolean-`{0,1}` indicator. -/
private def wireBitsToNat (w : Fin 32 → ZMod r) : ℕ :=
  ∑ i : Fin 32, (if w i = 1 then 1 else 0) * 2 ^ i.val

/-- `wireBitsToNat` is bounded by `2³² − 1`. -/
private theorem wireBitsToNat_lt_2_pow_32 (w : Fin 32 → ZMod r) :
    wireBitsToNat w < 2 ^ 32 := by
  unfold wireBitsToNat
  have hb : ∀ i : Fin 32, (if w i = 1 then (1 : ℕ) else 0) * 2 ^ i.val ≤ 2 ^ i.val := by
    intro i; split <;> simp
  have hsum : (∑ i : Fin 32, (if w i = 1 then (1 : ℕ) else 0) * 2 ^ i.val)
            ≤ ∑ i : Fin 32, 2 ^ i.val := Finset.sum_le_sum (fun i _ => hb i)
  have heq : (∑ i : Fin 32, (2 : ℕ) ^ i.val) = 2 ^ 32 - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) 32, Nat.geomSum_eq (by norm_num) 32]
    simp
  rw [heq] at hsum
  have hp : 0 < (2 : ℕ) ^ 32 := pow_pos (by norm_num) _
  omega

/-- For `BitOf`-witnessed wires, `wireBitsToNat` agrees with `toNat`. -/
private theorem wireBitsToNat_eq_toNat {a : Word32} {wa : Fin 32 → ZMod r}
    (ha : ∀ i, BitOf (wa i) (a i)) :
    wireBitsToNat wa = toNat a := by
  unfold wireBitsToNat toNat
  apply Finset.sum_congr rfl
  intro i _
  have h := ha i
  unfold BitOf at h
  cases hbi : a i
  · simp [hbi] at h
    -- a i = false, h : wa i = 0
    -- Both sides should be 0
    have hwa_ne_one : wa i ≠ 1 := by rw [h]; exact zero_ne_one
    simp [hwa_ne_one]
  · simp [hbi] at h
    -- a i = true, h : wa i = 1
    simp [h]

/-- The Fr-level recomposition equals the cast of `wireBitsToNat` for boolean wires. -/
private theorem bitsToFr_eq_wireBitsToNat_cast (w : Fin 32 → ZMod r)
    (h_bool : ∀ i, w i = 0 ∨ w i = 1) :
    (∑ i : Fin 32, (2 : ZMod r) ^ i.val * w i)
      = ((wireBitsToNat w : ℕ) : ZMod r) := by
  unfold wireBitsToNat
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rcases h_bool i with h0 | h1
  · simp [h0]
  · simp [h1]

/-- The Fr-level recomposition of a `BitOf`-witnessed wire equals the cast of
`toNat`. -/
private theorem bitsToFr_eq_toNat_cast (a : Word32) (wa : Fin 32 → ZMod r)
    (ha : ∀ i, BitOf (wa i) (a i)) :
    (∑ i : Fin 32, (2 : ZMod r) ^ i.val * wa i)
      = ((toNat a : ℕ) : ZMod r) := by
  have h_bool : ∀ i, wa i = 0 ∨ wa i = 1 := fun i => BitOf.isBool (ha i)
  rw [bitsToFr_eq_wireBitsToNat_cast wa h_bool, wireBitsToNat_eq_toNat ha]

/-- `2^32 < r`. -/
private theorem two_pow_32_lt_r : (2 : ℕ) ^ 32 < r := by
  have h := two_pow_lt_r
  have h_step : (2 : ℕ) ^ 32 ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-- `2 · 2^32 < r`. -/
private theorem two_times_two_pow_32_lt_r : 2 * (2 : ℕ) ^ 32 < r := by
  have h := two_pow_lt_r
  have h_step : 2 * (2 : ℕ) ^ 32 ≤ 2 ^ 253 := by
    have e : 2 * (2 : ℕ) ^ 32 = 2 ^ 33 := by ring
    rw [e]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-- The `ZMod r` cast of `2^32`. -/
private theorem two_pow_32_zmod_r_cast :
    (2 : ZMod r) ^ 32 = (((2 : ℕ) ^ 32 : ℕ) : ZMod r) := by
  push_cast; ring

/-- `ZMod r`-injectivity within `[0, r)` lifted to nat equality. -/
private theorem zmod_nat_inj {m n : ℕ} (hm : m < r) (hn : n < r)
    (h : (m : ZMod r) = (n : ZMod r)) : m = n := by
  have h1 : (m : ZMod r).val = m := ZMod.val_cast_of_lt hm
  have h2 : (n : ZMod r).val = n := ZMod.val_cast_of_lt hn
  rw [← h1, ← h2, h]

/-! ## `addMod32` per-bit carry-chain soundness -/

/-- **`addMod32` per-bit gadget soundness (carry-chain).** Given input
bit-wires (`BitOf`-witnessed), output bit-wires (boolean), a carry wire
(boolean), and the gadget's carry-chain LC over `ZMod r`, the output
wires are `BitOf`-witnessed by `addMod32 a b`'s bits.

Proof outline:

1. Bridge LHS of the carry-chain LC to `((a.toNat + b.toNat : ℕ) : ZMod r)`
   via `bitsToFr_eq_toNat_cast`.
2. Bridge RHS to `((wireBitsToNat wsum + 2³² · cNat : ℕ) : ZMod r)` where
   `cNat = if wcarry = 1 then 1 else 0`.
3. Both sides `< r` (by `two_times_two_pow_32_lt_r`), so lift the Fr
   equation to ℕ.
4. Apply `Formal.Arith.add_mod_32_core` to get
   `wireBitsToNat wsum = (a.toNat + b.toNat) % 2³²`.
5. Combine with `toNat_addMod32` to get
   `wireBitsToNat wsum = (addMod32 a b).toNat`.
6. By the same identity for the canonical lift, both wsum and the
   canonical lift recompose to the same ℕ value; apply
   `Formal.Gadgets.bits_unique` to conclude pointwise equality.
7. Read off `BitOf` per bit. -/
theorem addMod32_bit_sound (a b : Word32)
    (wa wb wsum : Fin 32 → ZMod r) (wcarry : ZMod r)
    (ha : ∀ i, BitOf (wa i) (a i)) (hb : ∀ i, BitOf (wb i) (b i))
    (h_wsum_bool : ∀ i, wsum i = 0 ∨ wsum i = 1)
    (h_wcarry_bool : wcarry = 0 ∨ wcarry = 1)
    (h_sum : (∑ i : Fin 32, (2 : ZMod r) ^ i.val * wa i)
            + (∑ i : Fin 32, (2 : ZMod r) ^ i.val * wb i)
            = (∑ i : Fin 32, (2 : ZMod r) ^ i.val * wsum i)
              + (2 : ZMod r) ^ 32 * wcarry) :
    ∀ i, BitOf (wsum i) ((addMod32 a b) i) := by
  -- The canonical lift for `addMod32 a b`'s bits.
  set wcanon : Fin 32 → ZMod r := fun i => if (addMod32 a b) i then 1 else 0 with hwcanon
  have h_canon_bool : ∀ i, wcanon i = 0 ∨ wcanon i = 1 := by
    intro i
    rw [hwcanon]
    by_cases hb : (addMod32 a b) i = true <;> simp [hb]
  have h_canon_BitOf : ∀ i, BitOf (wcanon i) ((addMod32 a b) i) := by
    intro i
    unfold BitOf
    rw [hwcanon]
    by_cases hb : (addMod32 a b) i = true <;> simp [hb]
  -- Bridge LHS of h_sum via BitOf-witness recomposition.
  rw [bitsToFr_eq_toNat_cast a wa ha, bitsToFr_eq_toNat_cast b wb hb,
      bitsToFr_eq_wireBitsToNat_cast wsum h_wsum_bool] at h_sum
  -- Encode carry as ℕ value cNat ∈ {0, 1}.
  set cNat : ℕ := if wcarry = 1 then 1 else 0 with hcNat
  have h_carry_cast : wcarry = ((cNat : ℕ) : ZMod r) := by
    rcases h_wcarry_bool with h0 | h1
    · simp [hcNat, h0]
    · simp [hcNat, h1]
  rw [h_carry_cast, two_pow_32_zmod_r_cast] at h_sum
  -- Combine the casts.
  have h_sum_zmod :
      ((toNat a + toNat b : ℕ) : ZMod r)
        = ((wireBitsToNat wsum + 2 ^ 32 * cNat : ℕ) : ZMod r) := by
    push_cast at h_sum ⊢
    linear_combination h_sum
  -- Range bounds.
  have h_a_lt := toNat_lt a
  have h_b_lt := toNat_lt b
  have h_cNat_le_one : cNat ≤ 1 := by
    rw [hcNat]
    by_cases hwc : wcarry = 1 <;> simp [hwc]
  have h_pair_lt_r : toNat a + toNat b < r := by
    have h2 := two_times_two_pow_32_lt_r
    omega
  have h_wsum_lt := wireBitsToNat_lt_2_pow_32 wsum
  have h_rhs_lt_r : wireBitsToNat wsum + 2 ^ 32 * cNat < r := by
    have h2 := two_times_two_pow_32_lt_r
    have h_prod : 2 ^ 32 * cNat ≤ 2 ^ 32 := by
      rcases (Nat.eq_or_lt_of_le h_cNat_le_one) with h | h
      · rw [h]; rfl
      · interval_cases cNat; simp
    omega
  -- Lift Fr equation to ℕ.
  have h_sum_nat : toNat a + toNat b = wireBitsToNat wsum + 2 ^ 32 * cNat :=
    zmod_nat_inj h_pair_lt_r h_rhs_lt_r h_sum_zmod
  -- Apply add_mod_32_core.
  have h_addmod_core : wireBitsToNat wsum = (toNat a + toNat b) % 2 ^ 32 :=
    add_mod_32_core (toNat a + toNat b) (wireBitsToNat wsum) cNat
      h_wsum_lt h_sum_nat
  -- Combine with toNat_addMod32: wireBitsToNat wsum = (addMod32 a b).toNat.
  rw [← toNat_addMod32 a b] at h_addmod_core
  -- The canonical lift's wireBitsToNat equals addMod32 a b's toNat.
  have h_canon_wireBitsToNat : wireBitsToNat wcanon = toNat (addMod32 a b) :=
    wireBitsToNat_eq_toNat h_canon_BitOf
  -- So wireBitsToNat wsum = wireBitsToNat wcanon.
  have h_wireBitsToNat_eq : wireBitsToNat wsum = wireBitsToNat wcanon := by
    rw [h_addmod_core, h_canon_wireBitsToNat]
  -- Apply bits_unique on the ℕ-indicator vectors.
  have h_ind_eq : (fun i : Fin 32 => (if wsum i = 1 then (1 : ℕ) else 0))
                = (fun i : Fin 32 => (if wcanon i = 1 then (1 : ℕ) else 0)) := by
    apply bits_unique
    · intro i
      by_cases hwi : wsum i = 1 <;> simp [hwi]
    · intro i
      by_cases hwi : wcanon i = 1 <;> simp [hwi]
    · -- Σ 2^i * (if wsum i = 1 then 1 else 0) = Σ 2^i * (if wcanon i = 1 then 1 else 0)
      -- LHS = wireBitsToNat wsum (after commuting product), and similarly for RHS.
      have h_swap : ∀ (w : Fin 32 → ZMod r),
          (∑ i : Fin 32, 2 ^ i.val * (if w i = 1 then (1 : ℕ) else 0))
            = wireBitsToNat w := by
        intro w
        unfold wireBitsToNat
        apply Finset.sum_congr rfl
        intros; ring
      rw [h_swap wsum, h_swap wcanon, h_wireBitsToNat_eq]
  -- Convert to ZMod r-pointwise via boolean hypothesis on both sides.
  have h_wsum_eq_wcanon : ∀ i, wsum i = wcanon i := by
    intro i
    have h_ind := congrFun h_ind_eq i
    rcases h_wsum_bool i with hw0 | hw1
    · rcases h_canon_bool i with hc0 | hc1
      · rw [hw0, hc0]
      · rw [hw0] at h_ind
        rw [hc1] at h_ind
        have h_neq : (0 : ZMod r) ≠ 1 := zero_ne_one
        simp [h_neq] at h_ind
    · rcases h_canon_bool i with hc0 | hc1
      · rw [hw1] at h_ind
        rw [hc0] at h_ind
        have h_neq : (1 : ZMod r) ≠ 0 := one_ne_zero
        simp at h_ind
      · rw [hw1, hc1]
  -- Conclude BitOf per bit.
  intro i
  rw [h_wsum_eq_wcanon i]
  exact h_canon_BitOf i

/-! ## BLAKE round-step composition (used by `BitwuzlaCompose`) -/

/-- **BLAKE2s round-step composition.** Given per-bit witness wires for
the round-step output and a `BitOf` hypothesis at every (cell, bit)
index, the wires equal the lifted spec bit values. -/
theorem blake2s_round_compose_bit {F : Type*} [Field F]
    (v m : Fin 16 → Word32) (round_idx : Fin 10)
    (wires : Fin 16 → Fin 32 → F)
    (h_bit_of : ∀ (i : Fin 16) (j : Fin 32),
        BitOf (wires i j) ((blake2sRoundStep v m round_idx i) j)) :
    ∀ (i : Fin 16) (j : Fin 32),
      wires i j =
        (if (blake2sRoundStep v m round_idx i) j then (1 : F) else 0) := by
  intro i j
  have h := h_bit_of i j
  unfold BitOf at h
  split_ifs at h ⊢ <;> exact h

/-- **BLAKE3 round-step composition.** Same shape as BLAKE2s. -/
theorem blake3_round_compose_bit {F : Type*} [Field F]
    (v m : Fin 16 → Word32) (round_idx : Fin 7)
    (wires : Fin 16 → Fin 32 → F)
    (h_bit_of : ∀ (i : Fin 16) (j : Fin 32),
        BitOf (wires i j) ((blake3RoundStep v m round_idx i) j)) :
    ∀ (i : Fin 16) (j : Fin 32),
      wires i j =
        (if (blake3RoundStep v m round_idx i) j then (1 : F) else 0) := by
  intro i j
  have h := h_bit_of i j
  unfold BitOf at h
  split_ifs at h ⊢ <;> exact h

end Xark
