/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.RsaBytes
import Formal.GroupedColumns
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `sha256_em_bits_82`: the encoded message

The PKCS#1 v1.5 EM for a 2048-bit modulus and SHA-256 is

`00 01 || FF…FF (202 bytes) || 00 || 30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20 || digest (32 bytes)`

`EM82_CONST` is that with the digest zeroed, limb-decomposed at 82 bits; the Rust adds
the digest's 256 bits at weights `2^0 … 2^255` (82 bits to limbs 0–2, 10 to limb 3, so
the DigestInfo body starts exactly at bit 256).

This file proves:

* `em82_eq`: `EM82_CONST`'s integer is the RFC 8017 prefix — `decide +kernel` against
  the limb literals quoted from `gadgets/xark-rsa/src/lib.rs`, so the constants are
  checked against the RFC, not trusted;
* `em`: adding the digest's bits gives `prefix + Σ_{j<256} bits j · 2^j` — the encoded
  message is the public target `verify_wide` pins.
-/

namespace Xark.Rsa.Em

open Xark.Rsa.GroupedColumns (val W)

/-- The RFC 8017 encoded message with the digest zeroed, as an integer. -/
def EM_PREFIX : ℤ :=
  986236757547332986472011617696226561292849812918563355472727826767720188564083584387121625107510786855734801053524719833194566624465665316622563244215340671405971599343902468620306327831715457360719532421388780770165778156818229863337344187575566725786793391480600129482653072861971002459947277805295727097226389568776499707662505334062639449916265137796823793276300221537201727072401742985542559596685092673521228140822200236743113743661549252453726123450722876929538747702356573783116197523966334991563351853851212597377279504828784670372039686704594645256069324522370986176059658958007207913567344112617652224

/-- `EM82_CONST`'s 25 little-endian limbs, quoted from `gadgets/xark-rsa/src/lib.rs`. -/
def em82 (k : ℕ) : ℤ :=
  [0,
    0,
    0,
    1908058575186009548423168,
    227580944067680599951361,
    4835703278458516698824640,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    4835703278458516698824703,
    36893488147419103231].getD k 0

/-- The limbs after the Rust adds the digest's bits: 82 bits per limb, the 256-bit digest
ending in limb 3. -/
def emOut (bits : ℕ → ℤ) (k : ℕ) : ℤ := em82 k + Xark.Rsa.Bytes.limbOf bits 82 256 k

/-- **The constant is the RFC prefix.** -/
theorem em82_eq : val em82 = EM_PREFIX := by decide +kernel

/-- **Adding the digest's bits adds the digest's integer.** -/
theorem val_emOut (bits : ℕ → ℤ) :
    val (emOut bits) = val em82 + ∑ j ∈ Finset.range 256, bits j * 2 ^ j := by
  have hsplit : val (emOut bits)
      = (∑ k ∈ Finset.range 25, em82 k * W ^ k)
        + (∑ k ∈ Finset.range 25, Xark.Rsa.Bytes.limbOf bits 82 256 k * W ^ k) := by
    rw [val, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [emOut]
    ring
  rw [hsplit]
  congr 1
  have := Xark.Rsa.Bytes.packing_of bits 25 82 256 (by norm_num) (by norm_num)
  simpa only [show W = 2 ^ 82 from rfl, pow_mul] using this

/-- **The EM vector.** With the digest's 256 bits, the encoded message is the RFC 8017
prefix plus the digest's integer. -/
theorem em (bits : ℕ → ℤ) :
    val (emOut bits) = EM_PREFIX + ∑ j ∈ Finset.range 256, bits j * 2 ^ j := by
  rw [val_emOut, em82_eq]

end Xark.Rsa.Em
