/-
Copyright (c) 2026 Xark. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
-/
import Formal.Aes

/-!
# AES-256 key schedule soundness

The AES-256 rounds are already covered by the key-size-independent
`aesRoundStep_bit_sound` in `Formal.Aes`. What differs from AES-128 is the *key
schedule*: `Nk = 8` (so `w[i] = w[i-8] ⊕ temp`, 60 words for 15 round keys) and an
**extra `SubWord` at `i % 8 = 4`** (with no `RotWord` and no `Rcon`) — the FIPS-197
§5.2 special case for `Nk > 6`.

This file gives the FIPS-197 AES-256 word recurrence (`aes256KeyExpansionWord`) and
proves that any prover-supplied byte trace satisfying the four recurrence fields
(init / non-special / `RotWord`-boundary / mid-`SubWord`) equals the spec at every
word (`wordBytes_eq_proof`), hence the round-key trace equals the expanded key
(`aes256KeyExpansion_from_witness`). The S-box / `xor8` / `RotWord` / `Rcon`
primitives are reused unchanged from the (already-proven) AES-128 development.
-/

namespace Xark

/-- One word of the AES-256 expanded key (`i ∈ [0, 60)`), viewed as 4 bytes. The
first 8 words are the 32-byte master key; then `w[i] = w[i-8] ⊕ temp` where
`temp = SubWord(RotWord(w[i-1])) ⊕ Rcon[i/8]` at `i % 8 = 0`, `temp = SubWord(w[i-1])`
at `i % 8 = 4` (the `Nk > 6` special case), and `temp = w[i-1]` otherwise. -/
def aes256KeyExpansionWord (key : Fin 32 → Byte8) : Fin 60 → Fin 4 → Byte8
  | ⟨0, _⟩ => fun b => key ⟨4 * 0 + b.val, by have := b.isLt; omega⟩
  | ⟨1, _⟩ => fun b => key ⟨4 * 1 + b.val, by have := b.isLt; omega⟩
  | ⟨2, _⟩ => fun b => key ⟨4 * 2 + b.val, by have := b.isLt; omega⟩
  | ⟨3, _⟩ => fun b => key ⟨4 * 3 + b.val, by have := b.isLt; omega⟩
  | ⟨4, _⟩ => fun b => key ⟨4 * 4 + b.val, by have := b.isLt; omega⟩
  | ⟨5, _⟩ => fun b => key ⟨4 * 5 + b.val, by have := b.isLt; omega⟩
  | ⟨6, _⟩ => fun b => key ⟨4 * 6 + b.val, by have := b.isLt; omega⟩
  | ⟨7, _⟩ => fun b => key ⟨4 * 7 + b.val, by have := b.isLt; omega⟩
  | ⟨n + 8, hn⟩ =>
      if (n + 8) % 8 = 0 then
        fun b =>
          xor8 (xor8 (aes256KeyExpansionWord key ⟨n, by omega⟩ b)
                     (aesSbox ((aesRotWord (aes256KeyExpansionWord key ⟨n + 7, by omega⟩)) b)))
               (if b = (0 : Fin 4) then aesRcon ⟨(n + 8) / 8, by omega⟩ else byteOfNat 0)
      else if (n + 8) % 8 = 4 then
        fun b =>
          xor8 (aes256KeyExpansionWord key ⟨n, by omega⟩ b)
               (aesSbox (aes256KeyExpansionWord key ⟨n + 7, by omega⟩ b))
      else
        fun b =>
          xor8 (aes256KeyExpansionWord key ⟨n, by omega⟩ b)
               (aes256KeyExpansionWord key ⟨n + 7, by omega⟩ b)
  termination_by w => w.val

/-- **AES-256 key expansion.** 15 round keys, each 16 bytes; round key `r` is the
four words `[4r, 4r+1, 4r+2, 4r+3]` concatenated (column-major, byte `i` at word
`4r + i/4`, byte-in-word `i % 4`). -/
def aes256KeyExpansion (key : Fin 32 → Byte8) : Fin 15 → Fin 16 → Byte8 :=
  fun r i =>
    aes256KeyExpansionWord key
      ⟨4 * r.val + i.val / 4, by have := r.isLt; have := i.isLt; omega⟩
      ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- A prover-supplied AES-256 key-schedule byte trace, constrained to the FIPS-197
recurrence. Byte-level only — the S-box / bit-witness wiring is exactly the AES-128
`IsValidKeyExpansionConstraintWitness` machinery, reused per S-box invocation. -/
structure IsValidAes256KeyScheduleWitness (key : Fin 32 → Byte8) where
  /-- 60 expanded-key words, four bytes each. -/
  wordBytes : Fin 60 → Fin 4 → Byte8
  /-- The first 8 words are the 32-byte master key. -/
  hInit : ∀ (n : Fin 8) (b : Fin 4),
    wordBytes ⟨n.val, by have := n.isLt; omega⟩ b =
      key ⟨4 * n.val + b.val, by have := n.isLt; have := b.isLt; omega⟩
  /-- Non-special recurrence: `w[n] = w[n-8] ⊕ w[n-1]` (`n % 8 ∉ {0, 4}`). -/
  hNonspecial : ∀ (n : Fin 60), n.val ≥ 8 → n.val % 8 ≠ 0 → n.val % 8 ≠ 4 →
    ∀ (b : Fin 4),
      wordBytes n b =
        xor8 (wordBytes ⟨n.val - 8, by have := n.isLt; omega⟩ b)
             (wordBytes ⟨n.val - 1, by have := n.isLt; omega⟩ b)
  /-- `RotWord` boundary: `w[n] = w[n-8] ⊕ SubWord(RotWord(w[n-1])) ⊕ Rcon[n/8]`
  (`n % 8 = 0`). -/
  hBoundary : ∀ (n : Fin 60), n.val ≥ 8 → n.val % 8 = 0 →
    ∀ (b : Fin 4),
      wordBytes n b =
        xor8 (xor8 (wordBytes ⟨n.val - 8, by have := n.isLt; omega⟩ b)
                   (aesSbox ((aesRotWord
                     (wordBytes ⟨n.val - 1, by have := n.isLt; omega⟩)) b)))
             (if b = (0 : Fin 4) then aesRcon ⟨n.val / 8, by have := n.isLt; omega⟩
              else byteOfNat 0)
  /-- Mid `SubWord` (the `Nk > 6` special case): `w[n] = w[n-8] ⊕ SubWord(w[n-1])`
  (`n % 8 = 4`), with no `RotWord` and no `Rcon`. -/
  hMidSubword : ∀ (n : Fin 60), n.val ≥ 8 → n.val % 8 = 4 →
    ∀ (b : Fin 4),
      wordBytes n b =
        xor8 (wordBytes ⟨n.val - 8, by have := n.isLt; omega⟩ b)
             (aesSbox (wordBytes ⟨n.val - 1, by have := n.isLt; omega⟩ b))
  /-- Round-key byte trace. -/
  rk : Fin 15 → Fin 16 → Byte8
  /-- Round-key composition: `rk[r][i] = w[4r + i/4][i % 4]`. -/
  hRoundKey_from_words : ∀ (r : Fin 15) (i : Fin 16),
    rk r i = wordBytes ⟨4 * r.val + i.val / 4,
      by have := r.isLt; have := i.isLt; omega⟩
      ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- **The prover-supplied `wordBytes` matches the FIPS-197 AES-256 expansion at every
word.** Strong induction on the word index: 8 base cases (master key), then the three
recurrence branches, each discharged by the matching structure field + the two
inductive hypotheses (`w[n-8]`, `w[n-1]`). -/
theorem IsValidAes256KeyScheduleWitness.wordBytes_eq
    {key : Fin 32 → Byte8} (h : IsValidAes256KeyScheduleWitness key) :
    ∀ n : Fin 60, h.wordBytes n = aes256KeyExpansionWord key n := by
  suffices aux : ∀ (m : ℕ) (hm : m < 60),
      h.wordBytes ⟨m, hm⟩ = aes256KeyExpansionWord key ⟨m, hm⟩ from
    fun n => by rw [show n = ⟨n.val, n.isLt⟩ from Fin.ext rfl]; exact aux n.val n.isLt
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    funext b
    by_cases h_lt : m < 8
    · interval_cases m <;>
        [ rw [h.hInit ⟨0, by decide⟩ b, aes256KeyExpansionWord.eq_def];
          rw [h.hInit ⟨1, by decide⟩ b, aes256KeyExpansionWord.eq_def];
          rw [h.hInit ⟨2, by decide⟩ b, aes256KeyExpansionWord.eq_def];
          rw [h.hInit ⟨3, by decide⟩ b, aes256KeyExpansionWord.eq_def];
          rw [h.hInit ⟨4, by decide⟩ b, aes256KeyExpansionWord.eq_def];
          rw [h.hInit ⟨5, by decide⟩ b, aes256KeyExpansionWord.eq_def];
          rw [h.hInit ⟨6, by decide⟩ b, aes256KeyExpansionWord.eq_def];
          rw [h.hInit ⟨7, by decide⟩ b, aes256KeyExpansionWord.eq_def] ] <;>
        exact congrArg key (Fin.ext (by simp))
    · push_neg at h_lt
      obtain ⟨v, rfl⟩ : ∃ v, m = v + 8 := ⟨m - 8, by omega⟩
      have h_v_lt : v < v + 8 := by omega
      have h_v7_lt : v + 7 < v + 8 := by omega
      have IH8 := ih v h_v_lt (by omega)
      have IH1 := ih (v + 7) h_v7_lt (by omega)
      have fin_eq_8 : (⟨v + 8 - 8, by have := hm; omega⟩ : Fin 60) = ⟨v, by omega⟩ := by
        apply Fin.ext; change v + 8 - 8 = v; omega
      have fin_eq_1 : (⟨v + 8 - 1, by have := hm; omega⟩ : Fin 60) = ⟨v + 7, by omega⟩ := by
        apply Fin.ext; change v + 8 - 1 = v + 7; omega
      by_cases h_mod0 : (v + 8) % 8 = 0
      · have h_b := h.hBoundary ⟨v + 8, hm⟩ h_lt h_mod0 b
        rw [fin_eq_8, fin_eq_1] at h_b
        rw [h_b, IH8, IH1]
        conv_rhs => unfold aes256KeyExpansionWord
        simp only [h_mod0, ↓reduceIte]
      · by_cases h_mod4 : (v + 8) % 8 = 4
        · have h_m := h.hMidSubword ⟨v + 8, hm⟩ h_lt h_mod4 b
          rw [fin_eq_8, fin_eq_1] at h_m
          rw [h_m, IH8, IH1]
          conv_rhs => unfold aes256KeyExpansionWord
          rw [if_neg h_mod0, if_pos h_mod4]
        · have h_nb := h.hNonspecial ⟨v + 8, hm⟩ h_lt h_mod0 h_mod4 b
          rw [fin_eq_8, fin_eq_1] at h_nb
          rw [h_nb, IH8, IH1]
          conv_rhs => unfold aes256KeyExpansionWord
          simp only [h_mod0, h_mod4, ↓reduceIte]

/-- **AES-256 key-schedule soundness (byte level).** A witness constrained to the
FIPS-197 recurrence has a round-key trace equal to the AES-256 expanded key. -/
theorem aes256KeyExpansion_from_witness
    {key : Fin 32 → Byte8} (h : IsValidAes256KeyScheduleWitness key) :
    h.rk = aes256KeyExpansion key := by
  funext r i
  rw [h.hRoundKey_from_words r i, h.wordBytes_eq]
  unfold aes256KeyExpansion
  rfl

end Xark
