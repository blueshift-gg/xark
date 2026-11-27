/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.SigLt5

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- `emBytes_lt_nBytes` compares `2^2040`-scale constants, past `norm_num`'s default cap.
set_option exponentiation.threshold 4096

/-!
# `verify_wide`'s contract, from the circuit's rows alone

`docs/security.md` §2.18 states the RSA-2048 PKCS#1 v1.5 relation as three facts:
the modulus has 2048 bits, the signature is below it, and the encoded message is
`sig^65537` modulo it. Each is proved separately — `n_bits`, `chainSig_bytes_lt_bytes`
and `chain_congruence_public` — over the same public bytes. This file names the three
byte-level operands once (`nBytes`, `sigBytes`, `digestBytes`) and states the three
facts as one theorem, so a reader (or a downstream spec) can cite the gadget's
contract without reassembling it.

The digest is a public input: the statement is that the RSA relation holds *for the
given digest*, not that the digest is the SHA-256 of any particular message. The
modulus's oddness and semiprimality are deliberately not proved (the key allowlist
is the trust anchor).
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- The modulus, as the big-endian integer of its 256 public bytes. -/
def nBytes (σ : ℕ → F) : ℤ :=
  ∑ i ∈ Finset.range 256, ((σ i).val : ℤ) * 256 ^ (255 - i)

/-- The signature, as the big-endian integer of its 256 public bytes. -/
def sigBytes (σ : ℕ → F) : ℤ :=
  ∑ i ∈ Finset.range 256, ((σ (256 + i)).val : ℤ) * 256 ^ (255 - i)

/-- The digest, as the big-endian integer of its 32 public bytes. -/
def digestBytes (σ : ℕ → F) : ℤ :=
  ∑ k ∈ Finset.range 32, ((σ (512 + k)).val : ℤ) * 256 ^ (31 - k)

/-- The modulus is 2048 bits, read from the bytes. -/
theorem nBytes_bits (σ : ℕ → F) (h : Sat circuit σ) :
    (2 : ℤ) ^ 2047 ≤ nBytes σ ∧ nBytes σ < (2 : ℤ) ^ 2048 := by
  have hb := n_bits σ h
  rwa [chainN_eq_bytes σ h] at hb

/-- The signature is below the modulus, over the bytes. -/
theorem sigBytes_lt_nBytes (σ : ℕ → F) (h : Sat circuit σ) :
    sigBytes σ < nBytes σ := by
  simpa [sigBytes, nBytes] using chainSig_bytes_lt_bytes σ h


/-- Every digest byte is at most `255`. -/
theorem digestByte_lt (σ : ℕ → F) (h : Sat circuit σ) (k : ℕ) (hk : k < 32) :
    ((σ (512 + k)).val : ℤ) ≤ 255 := by
  rw [digestBits_eq σ h k hk]
  have hb : ∀ t < 8, digestBits σ (8 * (31 - k) + t) ≤ 1 := by
    intro t ht
    unfold digestBits
    have h1 : (8 * (31 - k) + t) / 8 = 31 - k := by omega
    have h2 : (8 * (31 - k) + t) % 8 = t := by omega
    have h3 : 31 - (31 - k) = k := by omega
    rw [h1, h2, h3]
    exact_mod_cast hbit σ h (512 + k) t (by omega) ht
  have hle : (∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - k) + t) * 2 ^ t)
      ≤ ∑ t ∈ Finset.range 8, (1 : ℤ) * 2 ^ t := by
    refine Finset.sum_le_sum fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hb t (Finset.mem_range.mp ht)) (by positivity)
  have h255 : (∑ t ∈ Finset.range 8, (1 : ℤ) * 2 ^ t) = 255 := by
    norm_num [Finset.sum_range_succ]
  rw [h255] at hle
  exact hle

/-- The digest is below `2^256`. -/
theorem digestBytes_lt (σ : ℕ → F) (h : Sat circuit σ) :
    digestBytes σ < (2 : ℤ) ^ 256 := by
  have hle : digestBytes σ ≤ ∑ k ∈ Finset.range 32, (255 : ℤ) * 256 ^ (31 - k) := by
    refine Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_right (digestByte_lt σ h k (Finset.mem_range.mp hk))
      (by positivity)
  have hgeom : (∑ k ∈ Finset.range 32, (255 : ℤ) * 256 ^ (31 - k))
      = (256 : ℤ) ^ 32 - 1 := by
    rw [← Finset.mul_sum]
    have h1 : (∑ k ∈ Finset.range 32, (256 : ℤ) ^ (31 - k))
        = ∑ j ∈ Finset.range 32, (256 : ℤ) ^ j := by
      rw [Finset.sum_range_reflect]
    rw [h1]
    have htel : ∀ n, ((255 : ℤ) * ∑ j ∈ Finset.range n, (256 : ℤ) ^ j)
        = (256 : ℤ) ^ n - 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
    exact htel 32
  have hlt : (256 : ℤ) ^ 32 - 1 < (2 : ℤ) ^ 256 := by
    have hpow : (256 : ℤ) ^ 32 = (2 : ℤ) ^ 256 := by
      rw [show (256 : ℤ) = 2 ^ 8 by norm_num, ← pow_mul]
    rw [hpow]
    have hpos : (0 : ℤ) < (2 : ℤ) ^ 256 := by positivity
    omega
  calc digestBytes σ
      ≤ ∑ k ∈ Finset.range 32, (255 : ℤ) * 256 ^ (31 - k) := hle
    _ = (256 : ℤ) ^ 32 - 1 := hgeom
    _ < (2 : ℤ) ^ 256 := hlt

/-- **The encoding is below the modulus.** The prefix's leading byte is `0x00`, so
`EM < 2^2040`, and the modulus is at least `2^2047`: the encoded message is the
canonical residue of `sig^65537`, not a shifted one. -/
theorem emBytes_lt_nBytes (σ : ℕ → F) (h : Sat circuit σ) :
    Xark.Rsa.Em.EM_PREFIX + digestBytes σ < nBytes σ := by
  have hd := digestBytes_lt σ h
  have hp : Xark.Rsa.Em.EM_PREFIX < (2 : ℤ) ^ 2040 := by decide +kernel
  have h2 : (2 : ℤ) ^ 256 < (2 : ℤ) ^ 2040 := by norm_num
  have h3 : (2 : ℤ) ^ 2040 + (2 : ℤ) ^ 256 < (2 : ℤ) ^ 2041 := by norm_num
  have h4 : (2 : ℤ) ^ 2041 < (2 : ℤ) ^ 2047 := by norm_num
  have hn := (nBytes_bits σ h).1
  linarith

/-- The encoded message, as the chain reads it, is below the chain's modulus. -/
theorem chainEm_lt_chainN (σ : ℕ → F) (h : Sat circuit σ) :
    chainEm σ < chainN σ := by
  have he : chainEm σ = Xark.Rsa.Em.EM_PREFIX + digestBytes σ := by
    rw [chainEm_eq σ h, chainEm_bytes_32 σ h]
    rfl
  rw [he, chainN_eq_bytes σ h]
  exact emBytes_lt_nBytes σ h

/-- The encoded message is `sig^65537` modulo the modulus, over the bytes. -/
theorem emBytes_congruence (σ : ℕ → F) (h : Sat circuit σ) :
    Xark.Rsa.Em.EM_PREFIX + digestBytes σ ≡ sigBytes σ ^ (2 ^ 16 + 1) [ZMOD nBytes σ] := by
  simpa [digestBytes, sigBytes, nBytes] using chain_congruence_public σ h

/-- **The standard verification equation.** The encoding is `0 ≤ EM < n`, so the
congruence is an equality of the canonical residue: `sig^65537 mod n` is the RFC 8017
encoded message itself, which is the check a PKCS#1 verifier runs. -/
theorem rsa_verify_equation (σ : ℕ → F) (h : Sat circuit σ) :
    (sigBytes σ) ^ (2 ^ 16 + 1) % nBytes σ = Xark.Rsa.Em.EM_PREFIX + digestBytes σ := by
  have hc : Xark.Rsa.Em.EM_PREFIX + digestBytes σ
      ≡ (sigBytes σ) ^ (2 ^ 16 + 1) [ZMOD nBytes σ] := emBytes_congruence σ h
  have hc' : (Xark.Rsa.Em.EM_PREFIX + digestBytes σ) % nBytes σ
      = (sigBytes σ) ^ (2 ^ 16 + 1) % nBytes σ := by
    simpa [Int.ModEq] using hc
  have hlt := emBytes_lt_nBytes σ h
  have hp : (0 : ℤ) < Xark.Rsa.Em.EM_PREFIX := by decide +kernel
  have hd : 0 ≤ digestBytes σ := by
    refine Finset.sum_nonneg fun k _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)
  have hmod : (Xark.Rsa.Em.EM_PREFIX + digestBytes σ) % nBytes σ
      = Xark.Rsa.Em.EM_PREFIX + digestBytes σ :=
    Int.emod_eq_of_lt (by linarith) hlt
  exact hc'.symm.trans hmod

/-- **`verify_wide`'s contract.** For every assignment satisfying the exported
`rsa2048` rows: the modulus is 2048 bits, the signature and the RFC 8017 encoded message
are below it, and the encoded message is `sig^(2^16+1)` modulo the modulus — all over
the public bytes. The two range facts make `rsa_verify_equation` the standard
`RSAVP1 = EM` check. -/
structure VerifyWideSpec (σ : ℕ → F) : Prop where
  /-- `2^2047 ≤ n < 2^2048`. -/
  n_bits : (2 : ℤ) ^ 2047 ≤ nBytes σ ∧ nBytes σ < (2 : ℤ) ^ 2048
  /-- `sig < n`. -/
  sig_lt : sigBytes σ < nBytes σ
  /-- `EM(n, digest) < n`: the encoding is the canonical residue. -/
  em_lt : Xark.Rsa.Em.EM_PREFIX + digestBytes σ < nBytes σ
  /-- `EM(n, digest) ≡ sig^65537 (mod n)`. -/
  em : Xark.Rsa.Em.EM_PREFIX + digestBytes σ ≡ sigBytes σ ^ (2 ^ 16 + 1) [ZMOD nBytes σ]

/-- **The end-to-end statement**: `VerifyWideSpec` for every satisfying assignment. -/
theorem verify_wide_spec (σ : ℕ → F) (h : Sat circuit σ) : VerifyWideSpec σ where
  n_bits := nBytes_bits σ h
  sig_lt := sigBytes_lt_nBytes σ h
  em_lt := emBytes_lt_nBytes σ h
  em := emBytes_congruence σ h

/-- The same facts as a plain conjunction, for callers that prefer one. -/
theorem verify_wide (σ : ℕ → F) (h : Sat circuit σ) :
    (2 : ℤ) ^ 2047 ≤ nBytes σ ∧ nBytes σ < (2 : ℤ) ^ 2048 ∧ sigBytes σ < nBytes σ ∧
      Xark.Rsa.Em.EM_PREFIX + digestBytes σ < nBytes σ ∧
      Xark.Rsa.Em.EM_PREFIX + digestBytes σ ≡ sigBytes σ ^ (2 ^ 16 + 1) [ZMOD nBytes σ] :=
  ⟨(verify_wide_spec σ h).n_bits.1, (verify_wide_spec σ h).n_bits.2,
    (verify_wide_spec σ h).sig_lt, (verify_wide_spec σ h).em_lt,
    (verify_wide_spec σ h).em⟩

end Xark.Circuits.Rsa2048
