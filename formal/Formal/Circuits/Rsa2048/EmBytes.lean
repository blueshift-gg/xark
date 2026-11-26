/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.ByteBits

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The encoded message's digest bytes

The digest is the 32 public bytes `512..543`, packed big-endian. This file proves each
is the sum of its `digestBits`, and `bytes_of_bits_n` turns them into
`EM_PREFIX + Σ_k digestByte_k·256^(31-k)`.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

theorem byte_add_mod_n (n t i : ℕ) (ht : t < 8) : (8 * (n - 1 - i) + t) % 8 = t := by
  rw [Nat.add_comm (8 * (n - 1 - i)) t, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

theorem byte_inj_n {n : ℕ} {i i' t t' : ℕ} (hi : i < n) (hi' : i' < n)
    (ht : t < 8) (ht' : t' < 8) (h : 8 * (n - 1 - i) + t = 8 * (n - 1 - i') + t') :
    i = i' ∧ t = t' := by
  have hmod : t % 8 = t' % 8 := by
    rw [← byte_add_mod_n n t i ht, ← byte_add_mod_n n t' i' ht', h]
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at hmod
  constructor
  · have hd : 8 * (n - 1 - i) = 8 * (n - 1 - i') := by omega
    omega
  · exact hmod

set_option maxRecDepth 100000 in
theorem bytes_of_bits_n (n : ℕ) (_hn : 0 < n) (bits bytes : ℕ → ℤ)
    (hbyte : ∀ i < n, bytes i =
      ∑ t ∈ Finset.range 8, bits (8 * (n - 1 - i) + t) * 2 ^ t) :
    ∑ i ∈ Finset.range n, bytes i * 256 ^ (n - 1 - i)
      = ∑ j ∈ Finset.range (8 * n), bits j * 2 ^ j := by
  have hstep : ∀ i < n, bytes i * 256 ^ (n - 1 - i) =
      ∑ t ∈ Finset.range 8, bits (8 * (n - 1 - i) + t) * 2 ^ (8 * (n - 1 - i) + t) := by
    intro i hi
    rw [hbyte i hi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show (256 : ℤ) = 2 ^ 8 by norm_num, ← pow_mul, mul_assoc, ← pow_add, Nat.add_comm]
  calc ∑ i ∈ Finset.range n, bytes i * 256 ^ (n - 1 - i)
      = ∑ i ∈ Finset.range n, ∑ t ∈ Finset.range 8,
          bits (8 * (n - 1 - i) + t) * 2 ^ (8 * (n - 1 - i) + t) :=
        Finset.sum_congr rfl fun i hi => hstep i (Finset.mem_range.mp hi)
    _ = ∑ p ∈ Finset.range n ×ˢ Finset.range 8,
          bits (8 * (n - 1 - p.1) + p.2) * 2 ^ (8 * (n - 1 - p.1) + p.2) := by
        rw [Finset.sum_product]
    _ = ∑ j ∈ Finset.range (8 * n), bits j * 2 ^ j := by
        refine Finset.sum_bij (fun p _ => 8 * (n - 1 - p.1) + p.2) ?_ ?_ ?_ ?_
        · intro p hp
          obtain ⟨hpi, hpt⟩ := Finset.mem_product.mp hp
          have hi := Finset.mem_range.mp hpi
          have ht := Finset.mem_range.mp hpt
          exact Finset.mem_range.mpr (by omega)
        · intro p hp p' hp' h
          obtain ⟨hpi, hpt⟩ := Finset.mem_product.mp hp
          obtain ⟨hpi', hpt'⟩ := Finset.mem_product.mp hp'
          have h1 := byte_inj_n (Finset.mem_range.mp hpi) (Finset.mem_range.mp hpi')
            (Finset.mem_range.mp hpt) (Finset.mem_range.mp hpt') h
          exact Prod.ext h1.1 h1.2
        · intro j hj
          have hj' := Finset.mem_range.mp hj
          have hi : n - 1 - j / 8 < n := by omega
          have ht : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
          refine ⟨(n - 1 - j / 8, j % 8), ?_, ?_⟩
          · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr ht⟩
          · change 8 * (n - 1 - (n - 1 - j / 8)) + j % 8 = j
            have h : n - 1 - (n - 1 - j / 8) = j / 8 := by omega
            rw [h, Nat.div_add_mod]
        · intro p _
          rfl

theorem dbyte_0 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 512).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 0) + t) * 2 ^ t := by
  have hs : (callAt 512).t.Sat ((callAt 512).lift σ) :=
    call_sat_of h 512 (callAt 512) (by rfl) (by decide)
  have hb0 : (callAt 512).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 512).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 512).plugs = [(Xark.R1cs.LC.var (512 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 512).base = bitBase 512 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 512).lift σ)).getD 0 0) = σ 512 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 512).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 512 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 512).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 512 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 512).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 512).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 512).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 0) + t) = (Xark.Template.bitOf (σ 512) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 0) + t) / 8 = 31 - 0 := by omega
    have h2 : (8 * (31 - 0) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 512) t).val = (if (σ 512).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 512).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_1 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 513).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 1) + t) * 2 ^ t := by
  have hs : (callAt 513).t.Sat ((callAt 513).lift σ) :=
    call_sat_of h 513 (callAt 513) (by rfl) (by decide)
  have hb0 : (callAt 513).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 513).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 513).plugs = [(Xark.R1cs.LC.var (513 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 513).base = bitBase 513 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 513).lift σ)).getD 0 0) = σ 513 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 513).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 513 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 513).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 513 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 513).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 513).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 513).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 1) + t) = (Xark.Template.bitOf (σ 513) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 1) + t) / 8 = 31 - 1 := by omega
    have h2 : (8 * (31 - 1) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 513) t).val = (if (σ 513).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 513).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_2 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 514).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 2) + t) * 2 ^ t := by
  have hs : (callAt 514).t.Sat ((callAt 514).lift σ) :=
    call_sat_of h 514 (callAt 514) (by rfl) (by decide)
  have hb0 : (callAt 514).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 514).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 514).plugs = [(Xark.R1cs.LC.var (514 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 514).base = bitBase 514 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 514).lift σ)).getD 0 0) = σ 514 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 514).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 514 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 514).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 514 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 514).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 514).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 514).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 2) + t) = (Xark.Template.bitOf (σ 514) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 2) + t) / 8 = 31 - 2 := by omega
    have h2 : (8 * (31 - 2) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 514) t).val = (if (σ 514).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 514).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_3 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 515).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 3) + t) * 2 ^ t := by
  have hs : (callAt 515).t.Sat ((callAt 515).lift σ) :=
    call_sat_of h 515 (callAt 515) (by rfl) (by decide)
  have hb0 : (callAt 515).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 515).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 515).plugs = [(Xark.R1cs.LC.var (515 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 515).base = bitBase 515 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 515).lift σ)).getD 0 0) = σ 515 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 515).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 515 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 515).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 515 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 515).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 515).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 515).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 3) + t) = (Xark.Template.bitOf (σ 515) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 3) + t) / 8 = 31 - 3 := by omega
    have h2 : (8 * (31 - 3) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 515) t).val = (if (σ 515).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 515).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_4 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 516).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 4) + t) * 2 ^ t := by
  have hs : (callAt 516).t.Sat ((callAt 516).lift σ) :=
    call_sat_of h 516 (callAt 516) (by rfl) (by decide)
  have hb0 : (callAt 516).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 516).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 516).plugs = [(Xark.R1cs.LC.var (516 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 516).base = bitBase 516 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 516).lift σ)).getD 0 0) = σ 516 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 516).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 516 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 516).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 516 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 516).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 516).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 516).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 4) + t) = (Xark.Template.bitOf (σ 516) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 4) + t) / 8 = 31 - 4 := by omega
    have h2 : (8 * (31 - 4) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 516) t).val = (if (σ 516).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 516).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_5 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 517).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 5) + t) * 2 ^ t := by
  have hs : (callAt 517).t.Sat ((callAt 517).lift σ) :=
    call_sat_of h 517 (callAt 517) (by rfl) (by decide)
  have hb0 : (callAt 517).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 517).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 517).plugs = [(Xark.R1cs.LC.var (517 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 517).base = bitBase 517 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 517).lift σ)).getD 0 0) = σ 517 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 517).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 517 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 517).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 517 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 517).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 517).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 517).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 5) + t) = (Xark.Template.bitOf (σ 517) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 5) + t) / 8 = 31 - 5 := by omega
    have h2 : (8 * (31 - 5) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 517) t).val = (if (σ 517).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 517).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_6 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 518).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 6) + t) * 2 ^ t := by
  have hs : (callAt 518).t.Sat ((callAt 518).lift σ) :=
    call_sat_of h 518 (callAt 518) (by rfl) (by decide)
  have hb0 : (callAt 518).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 518).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 518).plugs = [(Xark.R1cs.LC.var (518 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 518).base = bitBase 518 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 518).lift σ)).getD 0 0) = σ 518 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 518).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 518 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 518).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 518 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 518).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 518).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 518).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 6) + t) = (Xark.Template.bitOf (σ 518) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 6) + t) / 8 = 31 - 6 := by omega
    have h2 : (8 * (31 - 6) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 518) t).val = (if (σ 518).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 518).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_7 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 519).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 7) + t) * 2 ^ t := by
  have hs : (callAt 519).t.Sat ((callAt 519).lift σ) :=
    call_sat_of h 519 (callAt 519) (by rfl) (by decide)
  have hb0 : (callAt 519).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 519).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 519).plugs = [(Xark.R1cs.LC.var (519 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 519).base = bitBase 519 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 519).lift σ)).getD 0 0) = σ 519 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 519).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 519 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 519).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 519 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 519).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 519).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 519).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 7) + t) = (Xark.Template.bitOf (σ 519) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 7) + t) / 8 = 31 - 7 := by omega
    have h2 : (8 * (31 - 7) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 519) t).val = (if (σ 519).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 519).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_8 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 520).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 8) + t) * 2 ^ t := by
  have hs : (callAt 520).t.Sat ((callAt 520).lift σ) :=
    call_sat_of h 520 (callAt 520) (by rfl) (by decide)
  have hb0 : (callAt 520).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 520).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 520).plugs = [(Xark.R1cs.LC.var (520 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 520).base = bitBase 520 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 520).lift σ)).getD 0 0) = σ 520 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 520).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 520 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 520).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 520 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 520).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 520).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 520).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 8) + t) = (Xark.Template.bitOf (σ 520) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 8) + t) / 8 = 31 - 8 := by omega
    have h2 : (8 * (31 - 8) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 520) t).val = (if (σ 520).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 520).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_9 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 521).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 9) + t) * 2 ^ t := by
  have hs : (callAt 521).t.Sat ((callAt 521).lift σ) :=
    call_sat_of h 521 (callAt 521) (by rfl) (by decide)
  have hb0 : (callAt 521).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 521).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 521).plugs = [(Xark.R1cs.LC.var (521 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 521).base = bitBase 521 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 521).lift σ)).getD 0 0) = σ 521 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 521).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 521 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 521).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 521 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 521).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 521).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 521).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 9) + t) = (Xark.Template.bitOf (σ 521) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 9) + t) / 8 = 31 - 9 := by omega
    have h2 : (8 * (31 - 9) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 521) t).val = (if (σ 521).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 521).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_10 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 522).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 10) + t) * 2 ^ t := by
  have hs : (callAt 522).t.Sat ((callAt 522).lift σ) :=
    call_sat_of h 522 (callAt 522) (by rfl) (by decide)
  have hb0 : (callAt 522).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 522).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 522).plugs = [(Xark.R1cs.LC.var (522 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 522).base = bitBase 522 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 522).lift σ)).getD 0 0) = σ 522 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 522).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 522 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 522).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 522 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 522).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 522).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 522).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 10) + t) = (Xark.Template.bitOf (σ 522) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 10) + t) / 8 = 31 - 10 := by omega
    have h2 : (8 * (31 - 10) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 522) t).val = (if (σ 522).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 522).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_11 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 523).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 11) + t) * 2 ^ t := by
  have hs : (callAt 523).t.Sat ((callAt 523).lift σ) :=
    call_sat_of h 523 (callAt 523) (by rfl) (by decide)
  have hb0 : (callAt 523).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 523).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 523).plugs = [(Xark.R1cs.LC.var (523 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 523).base = bitBase 523 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 523).lift σ)).getD 0 0) = σ 523 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 523).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 523 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 523).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 523 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 523).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 523).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 523).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 11) + t) = (Xark.Template.bitOf (σ 523) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 11) + t) / 8 = 31 - 11 := by omega
    have h2 : (8 * (31 - 11) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 523) t).val = (if (σ 523).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 523).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_12 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 524).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 12) + t) * 2 ^ t := by
  have hs : (callAt 524).t.Sat ((callAt 524).lift σ) :=
    call_sat_of h 524 (callAt 524) (by rfl) (by decide)
  have hb0 : (callAt 524).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 524).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 524).plugs = [(Xark.R1cs.LC.var (524 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 524).base = bitBase 524 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 524).lift σ)).getD 0 0) = σ 524 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 524).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 524 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 524).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 524 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 524).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 524).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 524).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 12) + t) = (Xark.Template.bitOf (σ 524) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 12) + t) / 8 = 31 - 12 := by omega
    have h2 : (8 * (31 - 12) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 524) t).val = (if (σ 524).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 524).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_13 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 525).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 13) + t) * 2 ^ t := by
  have hs : (callAt 525).t.Sat ((callAt 525).lift σ) :=
    call_sat_of h 525 (callAt 525) (by rfl) (by decide)
  have hb0 : (callAt 525).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 525).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 525).plugs = [(Xark.R1cs.LC.var (525 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 525).base = bitBase 525 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 525).lift σ)).getD 0 0) = σ 525 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 525).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 525 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 525).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 525 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 525).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 525).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 525).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 13) + t) = (Xark.Template.bitOf (σ 525) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 13) + t) / 8 = 31 - 13 := by omega
    have h2 : (8 * (31 - 13) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 525) t).val = (if (σ 525).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 525).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_14 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 526).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 14) + t) * 2 ^ t := by
  have hs : (callAt 526).t.Sat ((callAt 526).lift σ) :=
    call_sat_of h 526 (callAt 526) (by rfl) (by decide)
  have hb0 : (callAt 526).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 526).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 526).plugs = [(Xark.R1cs.LC.var (526 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 526).base = bitBase 526 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 526).lift σ)).getD 0 0) = σ 526 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 526).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 526 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 526).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 526 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 526).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 526).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 526).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 14) + t) = (Xark.Template.bitOf (σ 526) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 14) + t) / 8 = 31 - 14 := by omega
    have h2 : (8 * (31 - 14) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 526) t).val = (if (σ 526).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 526).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_15 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 527).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 15) + t) * 2 ^ t := by
  have hs : (callAt 527).t.Sat ((callAt 527).lift σ) :=
    call_sat_of h 527 (callAt 527) (by rfl) (by decide)
  have hb0 : (callAt 527).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 527).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 527).plugs = [(Xark.R1cs.LC.var (527 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 527).base = bitBase 527 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 527).lift σ)).getD 0 0) = σ 527 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 527).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 527 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 527).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 527 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 527).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 527).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 527).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 15) + t) = (Xark.Template.bitOf (σ 527) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 15) + t) / 8 = 31 - 15 := by omega
    have h2 : (8 * (31 - 15) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 527) t).val = (if (σ 527).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 527).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_16 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 528).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 16) + t) * 2 ^ t := by
  have hs : (callAt 528).t.Sat ((callAt 528).lift σ) :=
    call_sat_of h 528 (callAt 528) (by rfl) (by decide)
  have hb0 : (callAt 528).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 528).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 528).plugs = [(Xark.R1cs.LC.var (528 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 528).base = bitBase 528 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 528).lift σ)).getD 0 0) = σ 528 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 528).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 528 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 528).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 528 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 528).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 528).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 528).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 16) + t) = (Xark.Template.bitOf (σ 528) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 16) + t) / 8 = 31 - 16 := by omega
    have h2 : (8 * (31 - 16) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 528) t).val = (if (σ 528).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 528).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_17 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 529).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 17) + t) * 2 ^ t := by
  have hs : (callAt 529).t.Sat ((callAt 529).lift σ) :=
    call_sat_of h 529 (callAt 529) (by rfl) (by decide)
  have hb0 : (callAt 529).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 529).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 529).plugs = [(Xark.R1cs.LC.var (529 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 529).base = bitBase 529 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 529).lift σ)).getD 0 0) = σ 529 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 529).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 529 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 529).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 529 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 529).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 529).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 529).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 17) + t) = (Xark.Template.bitOf (σ 529) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 17) + t) / 8 = 31 - 17 := by omega
    have h2 : (8 * (31 - 17) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 529) t).val = (if (σ 529).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 529).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_18 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 530).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 18) + t) * 2 ^ t := by
  have hs : (callAt 530).t.Sat ((callAt 530).lift σ) :=
    call_sat_of h 530 (callAt 530) (by rfl) (by decide)
  have hb0 : (callAt 530).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 530).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 530).plugs = [(Xark.R1cs.LC.var (530 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 530).base = bitBase 530 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 530).lift σ)).getD 0 0) = σ 530 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 530).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 530 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 530).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 530 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 530).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 530).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 530).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 18) + t) = (Xark.Template.bitOf (σ 530) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 18) + t) / 8 = 31 - 18 := by omega
    have h2 : (8 * (31 - 18) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 530) t).val = (if (σ 530).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 530).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_19 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 531).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 19) + t) * 2 ^ t := by
  have hs : (callAt 531).t.Sat ((callAt 531).lift σ) :=
    call_sat_of h 531 (callAt 531) (by rfl) (by decide)
  have hb0 : (callAt 531).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 531).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 531).plugs = [(Xark.R1cs.LC.var (531 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 531).base = bitBase 531 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 531).lift σ)).getD 0 0) = σ 531 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 531).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 531 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 531).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 531 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 531).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 531).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 531).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 19) + t) = (Xark.Template.bitOf (σ 531) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 19) + t) / 8 = 31 - 19 := by omega
    have h2 : (8 * (31 - 19) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 531) t).val = (if (σ 531).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 531).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_20 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 532).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 20) + t) * 2 ^ t := by
  have hs : (callAt 532).t.Sat ((callAt 532).lift σ) :=
    call_sat_of h 532 (callAt 532) (by rfl) (by decide)
  have hb0 : (callAt 532).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 532).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 532).plugs = [(Xark.R1cs.LC.var (532 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 532).base = bitBase 532 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 532).lift σ)).getD 0 0) = σ 532 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 532).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 532 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 532).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 532 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 532).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 532).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 532).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 20) + t) = (Xark.Template.bitOf (σ 532) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 20) + t) / 8 = 31 - 20 := by omega
    have h2 : (8 * (31 - 20) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 532) t).val = (if (σ 532).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 532).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_21 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 533).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 21) + t) * 2 ^ t := by
  have hs : (callAt 533).t.Sat ((callAt 533).lift σ) :=
    call_sat_of h 533 (callAt 533) (by rfl) (by decide)
  have hb0 : (callAt 533).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 533).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 533).plugs = [(Xark.R1cs.LC.var (533 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 533).base = bitBase 533 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 533).lift σ)).getD 0 0) = σ 533 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 533).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 533 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 533).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 533 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 533).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 533).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 533).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 21) + t) = (Xark.Template.bitOf (σ 533) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 21) + t) / 8 = 31 - 21 := by omega
    have h2 : (8 * (31 - 21) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 533) t).val = (if (σ 533).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 533).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_22 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 534).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 22) + t) * 2 ^ t := by
  have hs : (callAt 534).t.Sat ((callAt 534).lift σ) :=
    call_sat_of h 534 (callAt 534) (by rfl) (by decide)
  have hb0 : (callAt 534).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 534).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 534).plugs = [(Xark.R1cs.LC.var (534 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 534).base = bitBase 534 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 534).lift σ)).getD 0 0) = σ 534 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 534).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 534 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 534).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 534 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 534).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 534).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 534).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 22) + t) = (Xark.Template.bitOf (σ 534) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 22) + t) / 8 = 31 - 22 := by omega
    have h2 : (8 * (31 - 22) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 534) t).val = (if (σ 534).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 534).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_23 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 535).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 23) + t) * 2 ^ t := by
  have hs : (callAt 535).t.Sat ((callAt 535).lift σ) :=
    call_sat_of h 535 (callAt 535) (by rfl) (by decide)
  have hb0 : (callAt 535).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 535).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 535).plugs = [(Xark.R1cs.LC.var (535 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 535).base = bitBase 535 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 535).lift σ)).getD 0 0) = σ 535 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 535).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 535 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 535).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 535 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 535).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 535).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 535).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 23) + t) = (Xark.Template.bitOf (σ 535) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 23) + t) / 8 = 31 - 23 := by omega
    have h2 : (8 * (31 - 23) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 535) t).val = (if (σ 535).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 535).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_24 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 536).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 24) + t) * 2 ^ t := by
  have hs : (callAt 536).t.Sat ((callAt 536).lift σ) :=
    call_sat_of h 536 (callAt 536) (by rfl) (by decide)
  have hb0 : (callAt 536).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 536).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 536).plugs = [(Xark.R1cs.LC.var (536 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 536).base = bitBase 536 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 536).lift σ)).getD 0 0) = σ 536 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 536).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 536 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 536).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 536 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 536).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 536).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 536).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 24) + t) = (Xark.Template.bitOf (σ 536) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 24) + t) / 8 = 31 - 24 := by omega
    have h2 : (8 * (31 - 24) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 536) t).val = (if (σ 536).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 536).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_25 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 537).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 25) + t) * 2 ^ t := by
  have hs : (callAt 537).t.Sat ((callAt 537).lift σ) :=
    call_sat_of h 537 (callAt 537) (by rfl) (by decide)
  have hb0 : (callAt 537).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 537).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 537).plugs = [(Xark.R1cs.LC.var (537 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 537).base = bitBase 537 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 537).lift σ)).getD 0 0) = σ 537 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 537).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 537 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 537).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 537 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 537).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 537).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 537).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 25) + t) = (Xark.Template.bitOf (σ 537) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 25) + t) / 8 = 31 - 25 := by omega
    have h2 : (8 * (31 - 25) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 537) t).val = (if (σ 537).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 537).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_26 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 538).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 26) + t) * 2 ^ t := by
  have hs : (callAt 538).t.Sat ((callAt 538).lift σ) :=
    call_sat_of h 538 (callAt 538) (by rfl) (by decide)
  have hb0 : (callAt 538).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 538).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 538).plugs = [(Xark.R1cs.LC.var (538 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 538).base = bitBase 538 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 538).lift σ)).getD 0 0) = σ 538 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 538).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 538 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 538).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 538 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 538).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 538).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 538).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 26) + t) = (Xark.Template.bitOf (σ 538) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 26) + t) / 8 = 31 - 26 := by omega
    have h2 : (8 * (31 - 26) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 538) t).val = (if (σ 538).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 538).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_27 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 539).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 27) + t) * 2 ^ t := by
  have hs : (callAt 539).t.Sat ((callAt 539).lift σ) :=
    call_sat_of h 539 (callAt 539) (by rfl) (by decide)
  have hb0 : (callAt 539).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 539).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 539).plugs = [(Xark.R1cs.LC.var (539 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 539).base = bitBase 539 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 539).lift σ)).getD 0 0) = σ 539 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 539).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 539 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 539).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 539 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 539).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 539).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 539).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 27) + t) = (Xark.Template.bitOf (σ 539) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 27) + t) / 8 = 31 - 27 := by omega
    have h2 : (8 * (31 - 27) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 539) t).val = (if (σ 539).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 539).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_28 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 540).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 28) + t) * 2 ^ t := by
  have hs : (callAt 540).t.Sat ((callAt 540).lift σ) :=
    call_sat_of h 540 (callAt 540) (by rfl) (by decide)
  have hb0 : (callAt 540).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 540).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 540).plugs = [(Xark.R1cs.LC.var (540 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 540).base = bitBase 540 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 540).lift σ)).getD 0 0) = σ 540 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 540).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 540 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 540).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 540 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 540).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 540).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 540).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 28) + t) = (Xark.Template.bitOf (σ 540) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 28) + t) / 8 = 31 - 28 := by omega
    have h2 : (8 * (31 - 28) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 540) t).val = (if (σ 540).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 540).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_29 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 541).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 29) + t) * 2 ^ t := by
  have hs : (callAt 541).t.Sat ((callAt 541).lift σ) :=
    call_sat_of h 541 (callAt 541) (by rfl) (by decide)
  have hb0 : (callAt 541).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 541).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 541).plugs = [(Xark.R1cs.LC.var (541 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 541).base = bitBase 541 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 541).lift σ)).getD 0 0) = σ 541 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 541).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 541 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 541).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 541 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 541).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 541).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 541).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 29) + t) = (Xark.Template.bitOf (σ 541) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 29) + t) / 8 = 31 - 29 := by omega
    have h2 : (8 * (31 - 29) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 541) t).val = (if (σ 541).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 541).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_30 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 542).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 30) + t) * 2 ^ t := by
  have hs : (callAt 542).t.Sat ((callAt 542).lift σ) :=
    call_sat_of h 542 (callAt 542) (by rfl) (by decide)
  have hb0 : (callAt 542).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 542).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 542).plugs = [(Xark.R1cs.LC.var (542 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 542).base = bitBase 542 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 542).lift σ)).getD 0 0) = σ 542 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 542).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 542 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 542).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 542 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 542).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 542).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 542).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 30) + t) = (Xark.Template.bitOf (σ 542) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 30) + t) / 8 = 31 - 30 := by omega
    have h2 : (8 * (31 - 30) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 542) t).val = (if (σ 542).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 542).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem dbyte_31 (σ : ℕ → F) (h : Sat circuit σ) :
    ((σ 543).val : ℤ) = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - 31) + t) * 2 ^ t := by
  have hs : (callAt 543).t.Sat ((callAt 543).lift σ) :=
    call_sat_of h 543 (callAt 543) (by rfl) (by decide)
  have hb0 : (callAt 543).t = Xark.Templates.ToBits.template := by rfl
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 543).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hplugs : (callAt 543).plugs = [(Xark.R1cs.LC.var (543 : ℕ) : Xark.Circuit.ZLC)] := by rfl
  have hbase : (callAt 543).base = bitBase 543 := by rfl
  have hins : ((Xark.Templates.ToBits.template.ins ((callAt 543).lift σ)).getD 0 0) = σ 543 := by
    simp [Xark.Template.Template.ins, Xark.Templates.ToBits.template, Call.lift, Call.env, hplugs,
      ZLC.toF, LC.eval, LC.var, LC.cst, zero_add, one_mul]
  have hlt : (σ 543).val < 2 ^ 8 := by
    rw [hins] at hspec
    exact hspec.1
  have hbit : ∀ t < 8, (bitGLC 543 t).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 543).lift σ)).getD t 0 := by
    intro t ht
    rw [bitGLC_eq_bitOut 543 t ht hplugs hbase hb0, bitOut_eval, hb0]
  have hspec_t : ∀ t < 8, (Xark.Templates.ToBits.template.outs ((callAt 543).lift σ)).getD t 0
      = Xark.Template.bitOf ((Xark.Templates.ToBits.template.ins ((callAt 543).lift σ)).getD 0 0) t := by
    intro t ht
    have := congrArg (fun l => l.getD t 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht] using this
  have hword := Xark.Templates.Add32.word_testBit (σ 543).val 8 hlt
  rw [← hword, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht8 := Finset.mem_range.mp ht
  have hnb : digestBits σ (8 * (31 - 31) + t) = (Xark.Template.bitOf (σ 543) t).val := by
    unfold digestBits
    have h1 : (8 * (31 - 31) + t) / 8 = 31 - 31 := by omega
    have h2 : (8 * (31 - 31) + t) % 8 = t := by omega
    rw [h1, h2, hbit t ht8, hspec_t t ht8, hins]
  rw [hnb]
  have hbitval : (Xark.Template.bitOf (σ 543) t).val = (if (σ 543).val.testBit t then 1 else 0) := by
    by_cases htc : (σ 543).val.testBit t
    · simp [Xark.Template.bitOf, htc, ZMod.val_one]
    · simp [Xark.Template.bitOf, htc, ZMod.val_zero]
  rw [hbitval]
  push_cast
  ring

theorem digestBits_eq (σ : ℕ → F) (h : Sat circuit σ) (k : ℕ) (hk : k < 32) :
    ((σ (512 + k)).val : ℤ)
      = ∑ t ∈ Finset.range 8, digestBits σ (8 * (31 - k) + t) * 2 ^ t := by
  interval_cases k
  · exact dbyte_0 σ h
  · exact dbyte_1 σ h
  · exact dbyte_2 σ h
  · exact dbyte_3 σ h
  · exact dbyte_4 σ h
  · exact dbyte_5 σ h
  · exact dbyte_6 σ h
  · exact dbyte_7 σ h
  · exact dbyte_8 σ h
  · exact dbyte_9 σ h
  · exact dbyte_10 σ h
  · exact dbyte_11 σ h
  · exact dbyte_12 σ h
  · exact dbyte_13 σ h
  · exact dbyte_14 σ h
  · exact dbyte_15 σ h
  · exact dbyte_16 σ h
  · exact dbyte_17 σ h
  · exact dbyte_18 σ h
  · exact dbyte_19 σ h
  · exact dbyte_20 σ h
  · exact dbyte_21 σ h
  · exact dbyte_22 σ h
  · exact dbyte_23 σ h
  · exact dbyte_24 σ h
  · exact dbyte_25 σ h
  · exact dbyte_26 σ h
  · exact dbyte_27 σ h
  · exact dbyte_28 σ h
  · exact dbyte_29 σ h
  · exact dbyte_30 σ h
  · exact dbyte_31 σ h


theorem byte_add_mod_32 (t i : ℕ) (ht : t < 8) : (8 * (31 - i) + t) % 8 = t := by
  rw [Nat.add_comm (8 * (31 - i)) t, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

theorem byte_inj_32 {i i' t t' : ℕ} (hi : i < 32) (hi' : i' < 32)
    (ht : t < 8) (ht' : t' < 8) (h : 8 * (31 - i) + t = 8 * (31 - i') + t') :
    i = i' ∧ t = t' := by
  have hmod : t % 8 = t' % 8 := by
    rw [← byte_add_mod_32 t i ht, ← byte_add_mod_32 t' i' ht', h]
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at hmod
  constructor
  · have hd : 8 * (31 - i) = 8 * (31 - i') := by omega
    omega
  · exact hmod

set_option maxRecDepth 100000 in
theorem bytes_of_bits_32 (bits bytes : ℕ → ℤ)
    (hbyte : ∀ i < 32, bytes i = ∑ t ∈ Finset.range 8, bits (8 * (31 - i) + t) * 2 ^ t) :
    ∑ i ∈ Finset.range 32, bytes i * 256 ^ (31 - i)
      = ∑ j ∈ Finset.range 256, bits j * 2 ^ j := by
  have hstep : ∀ i < 32, bytes i * 256 ^ (31 - i) =
      ∑ t ∈ Finset.range 8, bits (8 * (31 - i) + t) * 2 ^ (8 * (31 - i) + t) := by
    intro i hi
    rw [hbyte i hi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show (256 : ℤ) = 2 ^ 8 by norm_num, ← pow_mul, mul_assoc, ← pow_add, Nat.add_comm]
  calc ∑ i ∈ Finset.range 32, bytes i * 256 ^ (31 - i)
      = ∑ i ∈ Finset.range 32, ∑ t ∈ Finset.range 8,
          bits (8 * (31 - i) + t) * 2 ^ (8 * (31 - i) + t) :=
        Finset.sum_congr rfl fun i hi => hstep i (Finset.mem_range.mp hi)
    _ = ∑ p ∈ Finset.range 32 ×ˢ Finset.range 8,
          bits (8 * (31 - p.1) + p.2) * 2 ^ (8 * (31 - p.1) + p.2) := by
        rw [Finset.sum_product]
    _ = ∑ j ∈ Finset.range 256, bits j * 2 ^ j := by
        refine Finset.sum_bij (fun p _ => 8 * (31 - p.1) + p.2) ?_ ?_ ?_ ?_
        · intro p hp
          obtain ⟨hpi, hpt⟩ := Finset.mem_product.mp hp
          have hi := Finset.mem_range.mp hpi
          have ht := Finset.mem_range.mp hpt
          exact Finset.mem_range.mpr (by omega)
        · intro p hp p' hp' h
          obtain ⟨hpi, hpt⟩ := Finset.mem_product.mp hp
          obtain ⟨hpi', hpt'⟩ := Finset.mem_product.mp hp'
          have h1 := byte_inj_32 (Finset.mem_range.mp hpi) (Finset.mem_range.mp hpi')
            (Finset.mem_range.mp hpt) (Finset.mem_range.mp hpt') h
          exact Prod.ext h1.1 h1.2
        · intro j hj
          have hj' := Finset.mem_range.mp hj
          have hi : 31 - j / 8 < 32 := by omega
          have ht : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
          refine ⟨(31 - j / 8, j % 8), ?_, ?_⟩
          · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr ht⟩
          · change 8 * (31 - (31 - j / 8)) + j % 8 = j
            have h : 31 - (31 - j / 8) = j / 8 := by omega
            rw [h, Nat.div_add_mod]
        · intro p _
          rfl

theorem chainEm_bytes_32 (σ : ℕ → F) (h : Sat circuit σ) :
    Xark.Rsa.Em.EM_PREFIX + ∑ j ∈ Finset.range 256, digestBits σ j * 2 ^ j
      = Xark.Rsa.Em.EM_PREFIX
        + ∑ k ∈ Finset.range 32, ((σ (512 + k)).val : ℤ) * 256 ^ (31 - k) := by
  exact congrArg (fun x => Xark.Rsa.Em.EM_PREFIX + x)
    ((bytes_of_bits_32 (digestBits σ) (fun k => ((σ (512 + k)).val : ℤ))
      (digestBits_eq σ h)).symm)

/-- **The full public-byte RSA-2048 statement.** `n` and `sig` are the big-endian
256-byte integers, `em` is the RFC 8017 prefix plus the 32-byte digest, all read from
the circuit's public variables; `em ≡ sig^65537 (mod n)` on every satisfying
assignment. -/
theorem chain_congruence_public (σ : ℕ → F) (h : Sat circuit σ) :
    Xark.Rsa.Em.EM_PREFIX
        + ∑ k ∈ Finset.range 32, ((σ (512 + k)).val : ℤ) * 256 ^ (31 - k)
      ≡ (∑ i ∈ Finset.range 256, ((σ (256 + i)).val : ℤ) * 256 ^ (255 - i)) ^ (2 ^ 16 + 1)
        [ZMOD ∑ i ∈ Finset.range 256, ((σ i).val : ℤ) * 256 ^ (255 - i)] := by
  rw [← chainEm_bytes_32 σ h]
  exact chain_congruence_bytes σ h

end Xark.Circuits.Rsa2048
