/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.VerifyWide

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

/-!
# RFC 8017 conformance

`verify_wide_spec` states the RSA relation over the public bytes. zk.golf's
`RSASSAPKCS1v15` challenge (in `zksecurity/zk-golf-challenges`, the file
`Challenge/Specs/RSASSAPKCS1v15.lean`) states the same relation as
`verifySignature alg e n h sig = true`, over
RFC 8017's `OS2IP`/`I2OSP` and EMSA-PKCS1-v1_5 encoding. This file writes those
functions (they are RFC 8017 definitions; zk.golf's file has no license, so it is a
reference, not a dependency) and proves `verify_wide_spec` entails the verifier
returning `true` for the `2048 / SHA-256 / e = 65537` instance.

The digest is a public input: the spec is about the RSA relation for that digest, not
that the digest is any message's SHA-256.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

namespace Rfc8017

/-- RFC 8017 §4.2 `OS2IP`: a big-endian octet string as an integer. -/
def os2ip (xs : List ℕ) : ℕ := xs.foldl (fun acc x => acc * 256 + x) 0

/-- RFC 8017 §4.1 `I2OSP`: the big-endian octet string of `x` in `len` octets, or
`none` when `x` does not fit. -/
def i2osp (x len : ℕ) : Option (List ℕ) :=
  if x < 256 ^ len then
    some ((List.range len).map fun i => x / 256 ^ (len - 1 - i) % 256)
  else none

/-- An octet string: every element is below `256`. -/
def Octets (xs : List ℕ) : Prop := ∀ x ∈ xs, x < 256

/-- `x` has exactly `bits` bits (the modulus-size side condition). -/
def HasBitSize (x bits : ℕ) : Prop := 2 ^ (bits - 1) ≤ x ∧ x < 2 ^ bits

/-- The DER `DigestInfo` prefix for SHA-256 (RFC 8017 §9.2). -/
def sha256DigestInfoPrefix : List ℕ :=
  [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
   0x05, 0x00, 0x04, 0x20]

/-- `EMSA-PKCS1-v1_5` for SHA-256 and a 2048-bit modulus: `0x00 0x01`, 202 `0xff`
octets, `0x00`, the DigestInfo prefix and the 32 digest octets. -/
def emsaPkcs1v15Encode (digest : List ℕ) : List ℕ :=
  [0, 1] ++ List.replicate 202 255 ++ [0] ++ sha256DigestInfoPrefix ++ digest

/-- RFC 8017 §5.2.2 `RSAVP1`. -/
def rsavp1 (n e s : ℕ) : Option ℕ := if s < n then some (s ^ e % n) else none

/-- RFC 8017 §8.2.2 `RSASSA-PKCS1-v1_5-VERIFY`, SHA-256, 2048-bit modulus,
`e = 65537`, on the byte strings. This is the shape zk.golf's challenge takes as its
`Spec`. -/
def verifySignature (modulus digest sig : List ℕ) : Bool :=
  match rsavp1 (os2ip modulus) 65537 (os2ip sig) with
  | some r => decide (i2osp r 256 = some (emsaPkcs1v15Encode digest))
  | none => false

/-! ### `OS2IP` over a range -/

/-- Folding a byte into an accumulator scales the accumulator by `256`. -/
theorem foldl_scale (xs : List ℕ) (a : ℕ) :
    xs.foldl (fun acc x => acc * 256 + x) a = a * 256 ^ xs.length + os2ip xs := by
  induction xs generalizing a with
  | nil => simp [os2ip]
  | cons b xs ih =>
    have hb : os2ip (b :: xs) = b * 256 ^ xs.length + os2ip xs := by
      rw [os2ip, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
      exact ih b
    rw [List.foldl_cons, ih (a * 256 + b), hb, List.length_cons, pow_succ]
    ring

theorem os2ip_cons (a : ℕ) (xs : List ℕ) :
    os2ip (a :: xs) = a * 256 ^ xs.length + os2ip xs := by
  rw [os2ip, List.foldl_cons, foldl_scale]
  simp

theorem os2ip_append_singleton (xs : List ℕ) (a : ℕ) :
    os2ip (xs ++ [a]) = os2ip xs * 256 + a := by
  rw [os2ip, List.foldl_append]
  simp [os2ip]

theorem os2ip_append (xs ys : List ℕ) :
    os2ip (xs ++ ys) = os2ip xs * 256 ^ ys.length + os2ip ys := by
  rw [os2ip, List.foldl_append]
  exact foldl_scale ys (os2ip xs)

theorem os2ip_lt (xs : List ℕ) (h : Octets xs) : os2ip xs < 256 ^ xs.length := by
  induction xs with
  | nil => simp [os2ip]
  | cons a xs ih =>
    have ha : a < 256 := h a (List.mem_cons_self ..)
    have hxs : Octets xs := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [os2ip_cons, List.length_cons, pow_succ]
    have h1 : a * 256 ^ xs.length ≤ 255 * 256 ^ xs.length :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 := ih hxs
    have hpos : 0 < 256 ^ xs.length := pow_pos (by norm_num) _
    nlinarith

/-- `OS2IP` of a range-mapped list, as the big-endian weighted sum. -/
theorem os2ip_range_map (f : ℕ → ℕ) (n : ℕ) :
    os2ip ((List.range n).map f) = ∑ i ∈ Finset.range n, f i * 256 ^ (n - 1 - i) := by
  induction n with
  | zero => simp [os2ip]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, os2ip_append_singleton, ih,
      Finset.sum_range_succ, Finset.sum_mul]
    have hterm : ∀ i ∈ Finset.range n,
        f i * 256 ^ (n - 1 - i) * 256 = f i * 256 ^ (n + 1 - 1 - i) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [show n + 1 - 1 - i = (n - 1 - i) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm]
    rw [show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]

/-! ### `I2OSP` of a digit string -/

theorem range_succ_eq_map (n : ℕ) :
    List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
  rw [show n + 1 = 1 + n by omega, List.range_add, List.range_one]
  simp only [List.singleton_append]
  congr 1
  exact List.map_congr_left fun a _ => by omega

/-- The big-endian digit string of `a * 256 ^ m + X` is `a` followed by `X`'s digits. -/
theorem i2osp_cons (a X m : ℕ) (ha : a < 256) (hX : X < 256 ^ m) :
    (List.range (m + 1)).map (fun i => (a * 256 ^ m + X) / 256 ^ (m - i) % 256)
      = a :: (List.range m).map (fun i => X / 256 ^ (m - 1 - i) % 256) := by
  rw [range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · have h0 : (a * 256 ^ m + X) / 256 ^ m = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (pow_pos (by norm_num) m),
        Nat.div_eq_of_lt hX, Nat.zero_add]
    rw [Nat.sub_zero, h0, Nat.mod_eq_of_lt ha]
  · refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    rw [Function.comp_apply, show m - (j + 1) = m - 1 - j by omega]
    have hk : m = (j + 1) + (m - 1 - j) := by omega
    have hnum : a * 256 ^ m + X
        = X + (a * 256 ^ (j + 1)) * 256 ^ (m - 1 - j) := by
      conv_lhs => rw [hk, pow_add]
      ring
    rw [hnum, Nat.add_mul_div_right _ _ (pow_pos (by norm_num) _)]
    rw [show a * 256 ^ (j + 1) = 256 * (a * 256 ^ j) from by ring,
      Nat.add_mul_mod_self_left]

/-- The digit string `I2OSP x len` denotes `x` (when it exists). -/
theorem i2osp_digits (xs : List ℕ) (h : Octets xs) :
    (List.range xs.length).map
        (fun i => os2ip xs / 256 ^ (xs.length - 1 - i) % 256) = xs := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have ha : a < 256 := h a (List.mem_cons_self ..)
    have hrest : Octets rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hs : rest.length + 1 - 1 = rest.length := by omega
    rw [List.length_cons, os2ip_cons, hs,
      i2osp_cons a (os2ip rest) rest.length ha (os2ip_lt rest hrest), ih hrest]

theorem i2osp_os2ip (xs : List ℕ) (h : Octets xs) :
    i2osp (os2ip xs) xs.length = some xs := by
  rw [i2osp, if_pos (os2ip_lt xs h), i2osp_digits xs h]

theorem octets_append {xs ys : List ℕ} (hx : Octets xs) (hy : Octets ys) :
    Octets (xs ++ ys) := by
  intro x h
  rw [List.mem_append] at h
  rcases h with h | h
  · exact hx x h
  · exact hy x h

end Rfc8017

/-! ### The circuit's byte strings -/

/-- The modulus's public bytes. -/
def modulusBytes (σ : ℕ → F) : List ℕ := (List.range 256).map fun i => (σ i).val

/-- The signature's bytes (private inputs). -/
def sigBytesList (σ : ℕ → F) : List ℕ := (List.range 256).map fun i => (σ (256 + i)).val

/-- The digest's public bytes. -/
def digestList (σ : ℕ → F) : List ℕ := (List.range 32).map fun k => (σ (512 + k)).val

/-- Every signature byte is at most `255`. -/
theorem sigByte_lt (σ : ℕ → F) (h : Sat circuit σ) (i : ℕ) (hi : i < 256) :
    ((σ (256 + i)).val : ℤ) ≤ 255 := by
  rw [sigBits_eq σ h i hi]
  have hb : ∀ t < 8, sigBits σ (8 * (255 - i) + t) ≤ 1 := by
    intro t ht
    unfold sigBits
    have h1 : (8 * (255 - i) + t) / 8 = 255 - i := by omega
    have h2 : (8 * (255 - i) + t) % 8 = t := by omega
    rw [h1, h2, show 255 - (255 - i) = i by omega]
    exact_mod_cast hbit σ h (256 + i) t (by omega) ht
  have hle : (∑ t ∈ Finset.range 8, sigBits σ (8 * (255 - i) + t) * 2 ^ t)
      ≤ ∑ t ∈ Finset.range 8, (1 : ℤ) * 2 ^ t := by
    refine Finset.sum_le_sum fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hb t (Finset.mem_range.mp ht)) (by positivity)
  have h255 : (∑ t ∈ Finset.range 8, (1 : ℤ) * 2 ^ t) = 255 := by
    norm_num [Finset.sum_range_succ]
  rw [h255] at hle
  exact hle

theorem octets_modulusBytes (σ : ℕ → F) (h : Sat circuit σ) : Rfc8017.Octets (modulusBytes σ) := by
  intro x hx
  simp only [modulusBytes, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have := nByte_lt σ h i hi
  omega

theorem octets_sigBytesList (σ : ℕ → F) (h : Sat circuit σ) : Rfc8017.Octets (sigBytesList σ) := by
  intro x hx
  simp only [sigBytesList, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have := sigByte_lt σ h i hi
  omega

theorem octets_digestList (σ : ℕ → F) (h : Sat circuit σ) : Rfc8017.Octets (digestList σ) := by
  intro x hx
  simp only [digestList, List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have := digestByte_lt σ h k hk
  omega

/-! ### The byte strings as integers -/

theorem os2ip_modulusBytes (σ : ℕ → F) :
    ((Rfc8017.os2ip (modulusBytes σ) : ℕ) : ℤ) = nBytes σ := by
  rw [modulusBytes, Rfc8017.os2ip_range_map, nBytes, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [show 256 - 1 - i = 255 - i by omega]

theorem os2ip_sigBytesList (σ : ℕ → F) :
    ((Rfc8017.os2ip (sigBytesList σ) : ℕ) : ℤ) = sigBytes σ := by
  rw [sigBytesList, Rfc8017.os2ip_range_map, sigBytes, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [show 256 - 1 - i = 255 - i by omega]

theorem os2ip_digestList (σ : ℕ → F) :
    ((Rfc8017.os2ip (digestList σ) : ℕ) : ℤ) = digestBytes σ := by
  rw [digestList, Rfc8017.os2ip_range_map, digestBytes, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  rw [show 32 - 1 - k = 31 - k by omega]

/-- The EMSA prefix (2 + 202 + 1 + 19 octets) shifted to the digest's position is
`EM_PREFIX`. -/
theorem os2ip_emsa_prefix :
    (Rfc8017.os2ip ([0, 1] ++ List.replicate 202 255 ++ [0] ++ Rfc8017.sha256DigestInfoPrefix) : ℤ)
        * 256 ^ 32 = Xark.Rsa.Em.EM_PREFIX := by
  decide +kernel

/-- `OS2IP` of the encoded message is the EM value the chain carries. -/
theorem os2ip_emsa (σ : ℕ → F) (_h : Sat circuit σ) :
    ((Rfc8017.os2ip (Rfc8017.emsaPkcs1v15Encode (digestList σ)) : ℕ) : ℤ)
      = Xark.Rsa.Em.EM_PREFIX + digestBytes σ := by
  rw [Rfc8017.emsaPkcs1v15Encode, Rfc8017.os2ip_append,
    show (digestList σ).length = 32 by simp [digestList]]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, os2ip_emsa_prefix,
    os2ip_digestList]

/-- The encoded message is 256 octets. -/
theorem octets_emsa_prefix :
    Rfc8017.Octets
      ([0, 1] ++ List.replicate 202 255 ++ [0] ++ Rfc8017.sha256DigestInfoPrefix) := by
  have h : ([0, 1] ++ List.replicate 202 255 ++ [0] ++
      Rfc8017.sha256DigestInfoPrefix).all (fun x => x < 256) = true := by decide
  intro x hx
  exact of_decide_eq_true (List.all_eq_true.mp h x hx)

theorem octets_emsa (σ : ℕ → F) (h : Sat circuit σ) :
    Rfc8017.Octets (Rfc8017.emsaPkcs1v15Encode (digestList σ)) := by
  unfold Rfc8017.emsaPkcs1v15Encode
  exact Rfc8017.octets_append octets_emsa_prefix (octets_digestList σ h)

theorem length_emsa (σ : ℕ → F) :
    (Rfc8017.emsaPkcs1v15Encode (digestList σ)).length = 256 := by
  simp [Rfc8017.emsaPkcs1v15Encode, Rfc8017.sha256DigestInfoPrefix, digestList]

/-! ### The bridge -/

/-- **`verify_wide_spec` entails RFC 8017's `RSASSA-PKCS1-v1_5-VERIFY`.** For every
assignment satisfying the exported rows, the verifier that zk.golf's
`RSASSAPKCS1v15` challenge specifies returns `true` on the public bytes (and the
private signature). -/
theorem verifySignature_true (σ : ℕ → F) (h : Sat circuit σ) :
    Rfc8017.verifySignature (modulusBytes σ) (digestList σ) (sigBytesList σ) = true := by
  have hsig : Rfc8017.os2ip (sigBytesList σ) < Rfc8017.os2ip (modulusBytes σ) := by
    have hs := sigBytes_lt_nBytes σ h
    rw [← os2ip_sigBytesList σ, ← os2ip_modulusBytes σ] at hs
    exact_mod_cast hs
  have hmod : (Rfc8017.os2ip (sigBytesList σ)) ^ 65537 % Rfc8017.os2ip (modulusBytes σ)
      = Rfc8017.os2ip (Rfc8017.emsaPkcs1v15Encode (digestList σ)) := by
    have hZ : (((Rfc8017.os2ip (sigBytesList σ)) ^ 65537
          % Rfc8017.os2ip (modulusBytes σ) : ℕ) : ℤ)
        = ((Rfc8017.os2ip (Rfc8017.emsaPkcs1v15Encode (digestList σ)) : ℕ) : ℤ) := by
      rw [Int.natCast_emod, Nat.cast_pow, os2ip_sigBytesList, os2ip_modulusBytes,
        os2ip_emsa σ h]
      exact rsa_verify_equation σ h
    exact Int.natCast_inj.mp hZ
  rw [Rfc8017.verifySignature, Rfc8017.rsavp1, if_pos hsig, hmod]
  dsimp only
  rw [show (256 : ℕ) = (Rfc8017.emsaPkcs1v15Encode (digestList σ)).length
      from (length_emsa σ).symm,
    Rfc8017.i2osp_os2ip _ (octets_emsa σ h)]
  simp

/-- **The `Assumptions` zk.golf's interface states**: the three byte strings are octet
strings and the modulus has exactly 2048 bits. -/
theorem rfc8017_assumptions (σ : ℕ → F) (h : Sat circuit σ) :
    Rfc8017.Octets (modulusBytes σ) ∧ Rfc8017.Octets (digestList σ) ∧
      Rfc8017.Octets (sigBytesList σ) ∧
      Rfc8017.HasBitSize (Rfc8017.os2ip (modulusBytes σ)) 2048 := by
  refine ⟨octets_modulusBytes σ h, octets_digestList σ h, octets_sigBytesList σ h, ?_⟩
  unfold Rfc8017.HasBitSize
  have hc := os2ip_modulusBytes σ
  have hb := nBytes_bits σ h
  rw [← hc] at hb
  exact_mod_cast hb

end Xark.Circuits.Rsa2048
