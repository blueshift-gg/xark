/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.SigLt5

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

/-- The encoded message is `sig^65537` modulo the modulus, over the bytes. -/
theorem emBytes_congruence (σ : ℕ → F) (h : Sat circuit σ) :
    Xark.Rsa.Em.EM_PREFIX + digestBytes σ ≡ sigBytes σ ^ (2 ^ 16 + 1) [ZMOD nBytes σ] := by
  simpa [digestBytes, sigBytes, nBytes] using chain_congruence_public σ h

/-- **`verify_wide`'s contract.** For every assignment satisfying the exported
`rsa2048` rows: the modulus is 2048 bits, the signature is below it, and the RFC 8017
encoded message is `sig^(2^16+1)` modulo the modulus — all over the public bytes. -/
structure VerifyWideSpec (σ : ℕ → F) : Prop where
  /-- `2^2047 ≤ n < 2^2048`. -/
  n_bits : (2 : ℤ) ^ 2047 ≤ nBytes σ ∧ nBytes σ < (2 : ℤ) ^ 2048
  /-- `sig < n`. -/
  sig_lt : sigBytes σ < nBytes σ
  /-- `EM(n, digest) ≡ sig^65537 (mod n)`. -/
  em : Xark.Rsa.Em.EM_PREFIX + digestBytes σ ≡ sigBytes σ ^ (2 ^ 16 + 1) [ZMOD nBytes σ]

/-- **The end-to-end statement**: `VerifyWideSpec` for every satisfying assignment. -/
theorem verify_wide_spec (σ : ℕ → F) (h : Sat circuit σ) : VerifyWideSpec σ where
  n_bits := nBytes_bits σ h
  sig_lt := sigBytes_lt_nBytes σ h
  em := emBytes_congruence σ h

/-- The same three facts as a plain conjunction, for callers that prefer one. -/
theorem verify_wide (σ : ℕ → F) (h : Sat circuit σ) :
    (2 : ℤ) ^ 2047 ≤ nBytes σ ∧ nBytes σ < (2 : ℤ) ^ 2048 ∧ sigBytes σ < nBytes σ ∧
      Xark.Rsa.Em.EM_PREFIX + digestBytes σ ≡ sigBytes σ ^ (2 ^ 16 + 1) [ZMOD nBytes σ] :=
  ⟨(verify_wide_spec σ h).n_bits.1, (verify_wide_spec σ h).n_bits.2,
    (verify_wide_spec σ h).sig_lt, (verify_wide_spec σ h).em⟩

end Xark.Circuits.Rsa2048
