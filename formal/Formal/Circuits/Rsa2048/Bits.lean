/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.PackBoundW

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The `to_bits` calls' outputs are bits

Each of the 544 `to_bits::<8>` calls (segments `s0 .. s543`) proves its eight outputs
are the bits of its byte. `bits{b}` reads that contract for byte `b`; `hbit` is the
single fact the packed limbs' bounds need.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template

theorem bits0 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 0 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 0).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 0).plugs = [(Xark.R1cs.LC.var (0 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 0).base = bitBase 0 := by rfl
  have glc : (bitGLC 0 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 0).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 0 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 0).t.Sat ((callAt 0).lift σ) :=
    call_sat_of h 0 (callAt 0) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 0).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 0).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 0).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits1 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 1 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 1).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 1).plugs = [(Xark.R1cs.LC.var (1 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 1).base = bitBase 1 := by rfl
  have glc : (bitGLC 1 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 1).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 1 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 1).t.Sat ((callAt 1).lift σ) :=
    call_sat_of h 1 (callAt 1) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 1).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 1).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 1).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits2 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 2 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 2).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 2).plugs = [(Xark.R1cs.LC.var (2 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 2).base = bitBase 2 := by rfl
  have glc : (bitGLC 2 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 2).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 2 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 2).t.Sat ((callAt 2).lift σ) :=
    call_sat_of h 2 (callAt 2) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 2).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 2).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 2).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits3 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 3 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 3).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 3).plugs = [(Xark.R1cs.LC.var (3 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 3).base = bitBase 3 := by rfl
  have glc : (bitGLC 3 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 3).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 3 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 3).t.Sat ((callAt 3).lift σ) :=
    call_sat_of h 3 (callAt 3) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 3).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 3).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 3).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits4 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 4 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 4).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 4).plugs = [(Xark.R1cs.LC.var (4 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 4).base = bitBase 4 := by rfl
  have glc : (bitGLC 4 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 4).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 4 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 4).t.Sat ((callAt 4).lift σ) :=
    call_sat_of h 4 (callAt 4) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 4).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 4).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 4).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits5 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 5 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 5).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 5).plugs = [(Xark.R1cs.LC.var (5 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 5).base = bitBase 5 := by rfl
  have glc : (bitGLC 5 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 5).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 5 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 5).t.Sat ((callAt 5).lift σ) :=
    call_sat_of h 5 (callAt 5) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 5).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 5).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 5).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits6 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 6 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 6).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 6).plugs = [(Xark.R1cs.LC.var (6 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 6).base = bitBase 6 := by rfl
  have glc : (bitGLC 6 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 6).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 6 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 6).t.Sat ((callAt 6).lift σ) :=
    call_sat_of h 6 (callAt 6) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 6).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 6).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 6).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits7 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 7 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 7).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 7).plugs = [(Xark.R1cs.LC.var (7 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 7).base = bitBase 7 := by rfl
  have glc : (bitGLC 7 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 7).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 7 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 7).t.Sat ((callAt 7).lift σ) :=
    call_sat_of h 7 (callAt 7) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 7).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 7).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 7).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits8 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 8 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 8).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 8).plugs = [(Xark.R1cs.LC.var (8 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 8).base = bitBase 8 := by rfl
  have glc : (bitGLC 8 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 8).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 8 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 8).t.Sat ((callAt 8).lift σ) :=
    call_sat_of h 8 (callAt 8) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 8).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 8).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 8).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits9 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 9 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 9).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 9).plugs = [(Xark.R1cs.LC.var (9 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 9).base = bitBase 9 := by rfl
  have glc : (bitGLC 9 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 9).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 9 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 9).t.Sat ((callAt 9).lift σ) :=
    call_sat_of h 9 (callAt 9) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 9).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 9).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 9).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits10 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 10 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 10).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 10).plugs = [(Xark.R1cs.LC.var (10 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 10).base = bitBase 10 := by rfl
  have glc : (bitGLC 10 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 10).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 10 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 10).t.Sat ((callAt 10).lift σ) :=
    call_sat_of h 10 (callAt 10) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 10).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 10).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 10).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits11 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 11 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 11).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 11).plugs = [(Xark.R1cs.LC.var (11 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 11).base = bitBase 11 := by rfl
  have glc : (bitGLC 11 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 11).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 11 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 11).t.Sat ((callAt 11).lift σ) :=
    call_sat_of h 11 (callAt 11) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 11).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 11).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 11).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits12 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 12 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 12).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 12).plugs = [(Xark.R1cs.LC.var (12 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 12).base = bitBase 12 := by rfl
  have glc : (bitGLC 12 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 12).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 12 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 12).t.Sat ((callAt 12).lift σ) :=
    call_sat_of h 12 (callAt 12) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 12).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 12).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 12).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits13 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 13 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 13).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 13).plugs = [(Xark.R1cs.LC.var (13 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 13).base = bitBase 13 := by rfl
  have glc : (bitGLC 13 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 13).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 13 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 13).t.Sat ((callAt 13).lift σ) :=
    call_sat_of h 13 (callAt 13) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 13).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 13).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 13).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits14 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 14 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 14).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 14).plugs = [(Xark.R1cs.LC.var (14 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 14).base = bitBase 14 := by rfl
  have glc : (bitGLC 14 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 14).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 14 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 14).t.Sat ((callAt 14).lift σ) :=
    call_sat_of h 14 (callAt 14) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 14).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 14).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 14).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits15 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 15 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 15).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 15).plugs = [(Xark.R1cs.LC.var (15 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 15).base = bitBase 15 := by rfl
  have glc : (bitGLC 15 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 15).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 15 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 15).t.Sat ((callAt 15).lift σ) :=
    call_sat_of h 15 (callAt 15) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 15).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 15).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 15).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits16 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 16 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 16).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 16).plugs = [(Xark.R1cs.LC.var (16 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 16).base = bitBase 16 := by rfl
  have glc : (bitGLC 16 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 16).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 16 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 16).t.Sat ((callAt 16).lift σ) :=
    call_sat_of h 16 (callAt 16) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 16).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 16).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 16).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits17 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 17 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 17).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 17).plugs = [(Xark.R1cs.LC.var (17 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 17).base = bitBase 17 := by rfl
  have glc : (bitGLC 17 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 17).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 17 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 17).t.Sat ((callAt 17).lift σ) :=
    call_sat_of h 17 (callAt 17) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 17).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 17).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 17).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits18 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 18 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 18).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 18).plugs = [(Xark.R1cs.LC.var (18 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 18).base = bitBase 18 := by rfl
  have glc : (bitGLC 18 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 18).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 18 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 18).t.Sat ((callAt 18).lift σ) :=
    call_sat_of h 18 (callAt 18) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 18).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 18).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 18).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits19 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 19 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 19).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 19).plugs = [(Xark.R1cs.LC.var (19 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 19).base = bitBase 19 := by rfl
  have glc : (bitGLC 19 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 19).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 19 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 19).t.Sat ((callAt 19).lift σ) :=
    call_sat_of h 19 (callAt 19) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 19).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 19).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 19).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits20 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 20 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 20).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 20).plugs = [(Xark.R1cs.LC.var (20 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 20).base = bitBase 20 := by rfl
  have glc : (bitGLC 20 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 20).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 20 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 20).t.Sat ((callAt 20).lift σ) :=
    call_sat_of h 20 (callAt 20) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 20).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 20).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 20).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits21 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 21 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 21).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 21).plugs = [(Xark.R1cs.LC.var (21 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 21).base = bitBase 21 := by rfl
  have glc : (bitGLC 21 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 21).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 21 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 21).t.Sat ((callAt 21).lift σ) :=
    call_sat_of h 21 (callAt 21) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 21).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 21).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 21).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits22 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 22 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 22).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 22).plugs = [(Xark.R1cs.LC.var (22 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 22).base = bitBase 22 := by rfl
  have glc : (bitGLC 22 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 22).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 22 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 22).t.Sat ((callAt 22).lift σ) :=
    call_sat_of h 22 (callAt 22) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 22).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 22).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 22).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits23 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 23 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 23).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 23).plugs = [(Xark.R1cs.LC.var (23 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 23).base = bitBase 23 := by rfl
  have glc : (bitGLC 23 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 23).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 23 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 23).t.Sat ((callAt 23).lift σ) :=
    call_sat_of h 23 (callAt 23) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 23).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 23).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 23).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits24 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 24 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 24).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 24).plugs = [(Xark.R1cs.LC.var (24 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 24).base = bitBase 24 := by rfl
  have glc : (bitGLC 24 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 24).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 24 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 24).t.Sat ((callAt 24).lift σ) :=
    call_sat_of h 24 (callAt 24) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 24).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 24).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 24).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits25 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 25 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 25).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 25).plugs = [(Xark.R1cs.LC.var (25 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 25).base = bitBase 25 := by rfl
  have glc : (bitGLC 25 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 25).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 25 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 25).t.Sat ((callAt 25).lift σ) :=
    call_sat_of h 25 (callAt 25) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 25).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 25).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 25).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits26 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 26 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 26).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 26).plugs = [(Xark.R1cs.LC.var (26 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 26).base = bitBase 26 := by rfl
  have glc : (bitGLC 26 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 26).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 26 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 26).t.Sat ((callAt 26).lift σ) :=
    call_sat_of h 26 (callAt 26) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 26).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 26).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 26).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits27 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 27 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 27).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 27).plugs = [(Xark.R1cs.LC.var (27 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 27).base = bitBase 27 := by rfl
  have glc : (bitGLC 27 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 27).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 27 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 27).t.Sat ((callAt 27).lift σ) :=
    call_sat_of h 27 (callAt 27) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 27).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 27).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 27).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits28 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 28 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 28).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 28).plugs = [(Xark.R1cs.LC.var (28 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 28).base = bitBase 28 := by rfl
  have glc : (bitGLC 28 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 28).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 28 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 28).t.Sat ((callAt 28).lift σ) :=
    call_sat_of h 28 (callAt 28) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 28).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 28).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 28).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits29 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 29 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 29).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 29).plugs = [(Xark.R1cs.LC.var (29 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 29).base = bitBase 29 := by rfl
  have glc : (bitGLC 29 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 29).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 29 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 29).t.Sat ((callAt 29).lift σ) :=
    call_sat_of h 29 (callAt 29) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 29).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 29).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 29).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits30 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 30 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 30).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 30).plugs = [(Xark.R1cs.LC.var (30 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 30).base = bitBase 30 := by rfl
  have glc : (bitGLC 30 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 30).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 30 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 30).t.Sat ((callAt 30).lift σ) :=
    call_sat_of h 30 (callAt 30) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 30).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 30).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 30).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits31 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 31 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 31).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 31).plugs = [(Xark.R1cs.LC.var (31 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 31).base = bitBase 31 := by rfl
  have glc : (bitGLC 31 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 31).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 31 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 31).t.Sat ((callAt 31).lift σ) :=
    call_sat_of h 31 (callAt 31) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 31).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 31).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 31).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits32 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 32 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 32).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 32).plugs = [(Xark.R1cs.LC.var (32 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 32).base = bitBase 32 := by rfl
  have glc : (bitGLC 32 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 32).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 32 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 32).t.Sat ((callAt 32).lift σ) :=
    call_sat_of h 32 (callAt 32) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 32).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 32).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 32).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits33 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 33 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 33).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 33).plugs = [(Xark.R1cs.LC.var (33 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 33).base = bitBase 33 := by rfl
  have glc : (bitGLC 33 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 33).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 33 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 33).t.Sat ((callAt 33).lift σ) :=
    call_sat_of h 33 (callAt 33) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 33).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 33).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 33).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits34 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 34 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 34).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 34).plugs = [(Xark.R1cs.LC.var (34 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 34).base = bitBase 34 := by rfl
  have glc : (bitGLC 34 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 34).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 34 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 34).t.Sat ((callAt 34).lift σ) :=
    call_sat_of h 34 (callAt 34) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 34).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 34).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 34).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits35 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 35 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 35).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 35).plugs = [(Xark.R1cs.LC.var (35 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 35).base = bitBase 35 := by rfl
  have glc : (bitGLC 35 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 35).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 35 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 35).t.Sat ((callAt 35).lift σ) :=
    call_sat_of h 35 (callAt 35) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 35).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 35).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 35).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits36 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 36 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 36).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 36).plugs = [(Xark.R1cs.LC.var (36 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 36).base = bitBase 36 := by rfl
  have glc : (bitGLC 36 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 36).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 36 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 36).t.Sat ((callAt 36).lift σ) :=
    call_sat_of h 36 (callAt 36) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 36).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 36).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 36).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits37 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 37 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 37).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 37).plugs = [(Xark.R1cs.LC.var (37 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 37).base = bitBase 37 := by rfl
  have glc : (bitGLC 37 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 37).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 37 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 37).t.Sat ((callAt 37).lift σ) :=
    call_sat_of h 37 (callAt 37) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 37).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 37).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 37).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits38 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 38 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 38).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 38).plugs = [(Xark.R1cs.LC.var (38 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 38).base = bitBase 38 := by rfl
  have glc : (bitGLC 38 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 38).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 38 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 38).t.Sat ((callAt 38).lift σ) :=
    call_sat_of h 38 (callAt 38) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 38).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 38).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 38).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits39 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 39 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 39).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 39).plugs = [(Xark.R1cs.LC.var (39 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 39).base = bitBase 39 := by rfl
  have glc : (bitGLC 39 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 39).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 39 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 39).t.Sat ((callAt 39).lift σ) :=
    call_sat_of h 39 (callAt 39) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 39).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 39).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 39).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits40 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 40 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 40).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 40).plugs = [(Xark.R1cs.LC.var (40 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 40).base = bitBase 40 := by rfl
  have glc : (bitGLC 40 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 40).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 40 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 40).t.Sat ((callAt 40).lift σ) :=
    call_sat_of h 40 (callAt 40) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 40).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 40).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 40).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits41 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 41 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 41).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 41).plugs = [(Xark.R1cs.LC.var (41 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 41).base = bitBase 41 := by rfl
  have glc : (bitGLC 41 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 41).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 41 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 41).t.Sat ((callAt 41).lift σ) :=
    call_sat_of h 41 (callAt 41) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 41).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 41).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 41).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits42 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 42 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 42).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 42).plugs = [(Xark.R1cs.LC.var (42 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 42).base = bitBase 42 := by rfl
  have glc : (bitGLC 42 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 42).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 42 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 42).t.Sat ((callAt 42).lift σ) :=
    call_sat_of h 42 (callAt 42) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 42).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 42).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 42).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits43 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 43 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 43).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 43).plugs = [(Xark.R1cs.LC.var (43 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 43).base = bitBase 43 := by rfl
  have glc : (bitGLC 43 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 43).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 43 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 43).t.Sat ((callAt 43).lift σ) :=
    call_sat_of h 43 (callAt 43) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 43).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 43).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 43).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits44 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 44 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 44).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 44).plugs = [(Xark.R1cs.LC.var (44 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 44).base = bitBase 44 := by rfl
  have glc : (bitGLC 44 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 44).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 44 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 44).t.Sat ((callAt 44).lift σ) :=
    call_sat_of h 44 (callAt 44) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 44).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 44).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 44).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits45 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 45 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 45).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 45).plugs = [(Xark.R1cs.LC.var (45 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 45).base = bitBase 45 := by rfl
  have glc : (bitGLC 45 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 45).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 45 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 45).t.Sat ((callAt 45).lift σ) :=
    call_sat_of h 45 (callAt 45) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 45).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 45).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 45).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits46 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 46 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 46).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 46).plugs = [(Xark.R1cs.LC.var (46 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 46).base = bitBase 46 := by rfl
  have glc : (bitGLC 46 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 46).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 46 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 46).t.Sat ((callAt 46).lift σ) :=
    call_sat_of h 46 (callAt 46) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 46).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 46).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 46).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits47 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 47 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 47).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 47).plugs = [(Xark.R1cs.LC.var (47 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 47).base = bitBase 47 := by rfl
  have glc : (bitGLC 47 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 47).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 47 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 47).t.Sat ((callAt 47).lift σ) :=
    call_sat_of h 47 (callAt 47) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 47).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 47).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 47).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits48 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 48 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 48).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 48).plugs = [(Xark.R1cs.LC.var (48 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 48).base = bitBase 48 := by rfl
  have glc : (bitGLC 48 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 48).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 48 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 48).t.Sat ((callAt 48).lift σ) :=
    call_sat_of h 48 (callAt 48) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 48).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 48).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 48).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits49 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 49 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 49).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 49).plugs = [(Xark.R1cs.LC.var (49 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 49).base = bitBase 49 := by rfl
  have glc : (bitGLC 49 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 49).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 49 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 49).t.Sat ((callAt 49).lift σ) :=
    call_sat_of h 49 (callAt 49) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 49).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 49).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 49).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits50 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 50 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 50).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 50).plugs = [(Xark.R1cs.LC.var (50 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 50).base = bitBase 50 := by rfl
  have glc : (bitGLC 50 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 50).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 50 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 50).t.Sat ((callAt 50).lift σ) :=
    call_sat_of h 50 (callAt 50) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 50).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 50).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 50).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits51 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 51 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 51).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 51).plugs = [(Xark.R1cs.LC.var (51 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 51).base = bitBase 51 := by rfl
  have glc : (bitGLC 51 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 51).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 51 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 51).t.Sat ((callAt 51).lift σ) :=
    call_sat_of h 51 (callAt 51) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 51).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 51).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 51).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits52 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 52 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 52).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 52).plugs = [(Xark.R1cs.LC.var (52 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 52).base = bitBase 52 := by rfl
  have glc : (bitGLC 52 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 52).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 52 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 52).t.Sat ((callAt 52).lift σ) :=
    call_sat_of h 52 (callAt 52) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 52).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 52).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 52).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits53 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 53 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 53).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 53).plugs = [(Xark.R1cs.LC.var (53 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 53).base = bitBase 53 := by rfl
  have glc : (bitGLC 53 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 53).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 53 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 53).t.Sat ((callAt 53).lift σ) :=
    call_sat_of h 53 (callAt 53) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 53).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 53).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 53).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits54 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 54 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 54).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 54).plugs = [(Xark.R1cs.LC.var (54 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 54).base = bitBase 54 := by rfl
  have glc : (bitGLC 54 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 54).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 54 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 54).t.Sat ((callAt 54).lift σ) :=
    call_sat_of h 54 (callAt 54) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 54).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 54).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 54).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits55 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 55 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 55).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 55).plugs = [(Xark.R1cs.LC.var (55 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 55).base = bitBase 55 := by rfl
  have glc : (bitGLC 55 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 55).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 55 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 55).t.Sat ((callAt 55).lift σ) :=
    call_sat_of h 55 (callAt 55) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 55).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 55).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 55).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits56 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 56 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 56).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 56).plugs = [(Xark.R1cs.LC.var (56 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 56).base = bitBase 56 := by rfl
  have glc : (bitGLC 56 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 56).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 56 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 56).t.Sat ((callAt 56).lift σ) :=
    call_sat_of h 56 (callAt 56) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 56).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 56).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 56).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits57 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 57 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 57).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 57).plugs = [(Xark.R1cs.LC.var (57 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 57).base = bitBase 57 := by rfl
  have glc : (bitGLC 57 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 57).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 57 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 57).t.Sat ((callAt 57).lift σ) :=
    call_sat_of h 57 (callAt 57) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 57).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 57).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 57).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits58 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 58 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 58).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 58).plugs = [(Xark.R1cs.LC.var (58 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 58).base = bitBase 58 := by rfl
  have glc : (bitGLC 58 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 58).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 58 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 58).t.Sat ((callAt 58).lift σ) :=
    call_sat_of h 58 (callAt 58) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 58).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 58).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 58).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits59 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 59 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 59).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 59).plugs = [(Xark.R1cs.LC.var (59 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 59).base = bitBase 59 := by rfl
  have glc : (bitGLC 59 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 59).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 59 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 59).t.Sat ((callAt 59).lift σ) :=
    call_sat_of h 59 (callAt 59) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 59).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 59).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 59).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits60 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 60 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 60).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 60).plugs = [(Xark.R1cs.LC.var (60 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 60).base = bitBase 60 := by rfl
  have glc : (bitGLC 60 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 60).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 60 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 60).t.Sat ((callAt 60).lift σ) :=
    call_sat_of h 60 (callAt 60) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 60).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 60).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 60).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits61 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 61 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 61).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 61).plugs = [(Xark.R1cs.LC.var (61 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 61).base = bitBase 61 := by rfl
  have glc : (bitGLC 61 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 61).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 61 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 61).t.Sat ((callAt 61).lift σ) :=
    call_sat_of h 61 (callAt 61) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 61).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 61).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 61).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits62 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 62 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 62).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 62).plugs = [(Xark.R1cs.LC.var (62 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 62).base = bitBase 62 := by rfl
  have glc : (bitGLC 62 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 62).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 62 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 62).t.Sat ((callAt 62).lift σ) :=
    call_sat_of h 62 (callAt 62) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 62).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 62).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 62).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits63 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 63 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 63).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 63).plugs = [(Xark.R1cs.LC.var (63 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 63).base = bitBase 63 := by rfl
  have glc : (bitGLC 63 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 63).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 63 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 63).t.Sat ((callAt 63).lift σ) :=
    call_sat_of h 63 (callAt 63) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 63).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 63).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 63).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits64 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 64 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 64).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 64).plugs = [(Xark.R1cs.LC.var (64 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 64).base = bitBase 64 := by rfl
  have glc : (bitGLC 64 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 64).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 64 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 64).t.Sat ((callAt 64).lift σ) :=
    call_sat_of h 64 (callAt 64) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 64).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 64).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 64).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits65 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 65 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 65).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 65).plugs = [(Xark.R1cs.LC.var (65 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 65).base = bitBase 65 := by rfl
  have glc : (bitGLC 65 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 65).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 65 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 65).t.Sat ((callAt 65).lift σ) :=
    call_sat_of h 65 (callAt 65) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 65).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 65).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 65).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits66 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 66 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 66).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 66).plugs = [(Xark.R1cs.LC.var (66 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 66).base = bitBase 66 := by rfl
  have glc : (bitGLC 66 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 66).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 66 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 66).t.Sat ((callAt 66).lift σ) :=
    call_sat_of h 66 (callAt 66) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 66).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 66).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 66).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits67 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 67 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 67).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 67).plugs = [(Xark.R1cs.LC.var (67 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 67).base = bitBase 67 := by rfl
  have glc : (bitGLC 67 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 67).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 67 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 67).t.Sat ((callAt 67).lift σ) :=
    call_sat_of h 67 (callAt 67) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 67).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 67).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 67).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits68 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 68 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 68).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 68).plugs = [(Xark.R1cs.LC.var (68 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 68).base = bitBase 68 := by rfl
  have glc : (bitGLC 68 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 68).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 68 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 68).t.Sat ((callAt 68).lift σ) :=
    call_sat_of h 68 (callAt 68) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 68).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 68).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 68).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits69 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 69 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 69).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 69).plugs = [(Xark.R1cs.LC.var (69 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 69).base = bitBase 69 := by rfl
  have glc : (bitGLC 69 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 69).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 69 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 69).t.Sat ((callAt 69).lift σ) :=
    call_sat_of h 69 (callAt 69) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 69).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 69).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 69).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits70 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 70 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 70).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 70).plugs = [(Xark.R1cs.LC.var (70 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 70).base = bitBase 70 := by rfl
  have glc : (bitGLC 70 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 70).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 70 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 70).t.Sat ((callAt 70).lift σ) :=
    call_sat_of h 70 (callAt 70) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 70).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 70).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 70).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits71 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 71 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 71).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 71).plugs = [(Xark.R1cs.LC.var (71 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 71).base = bitBase 71 := by rfl
  have glc : (bitGLC 71 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 71).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 71 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 71).t.Sat ((callAt 71).lift σ) :=
    call_sat_of h 71 (callAt 71) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 71).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 71).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 71).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits72 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 72 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 72).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 72).plugs = [(Xark.R1cs.LC.var (72 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 72).base = bitBase 72 := by rfl
  have glc : (bitGLC 72 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 72).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 72 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 72).t.Sat ((callAt 72).lift σ) :=
    call_sat_of h 72 (callAt 72) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 72).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 72).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 72).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits73 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 73 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 73).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 73).plugs = [(Xark.R1cs.LC.var (73 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 73).base = bitBase 73 := by rfl
  have glc : (bitGLC 73 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 73).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 73 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 73).t.Sat ((callAt 73).lift σ) :=
    call_sat_of h 73 (callAt 73) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 73).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 73).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 73).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits74 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 74 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 74).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 74).plugs = [(Xark.R1cs.LC.var (74 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 74).base = bitBase 74 := by rfl
  have glc : (bitGLC 74 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 74).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 74 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 74).t.Sat ((callAt 74).lift σ) :=
    call_sat_of h 74 (callAt 74) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 74).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 74).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 74).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits75 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 75 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 75).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 75).plugs = [(Xark.R1cs.LC.var (75 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 75).base = bitBase 75 := by rfl
  have glc : (bitGLC 75 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 75).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 75 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 75).t.Sat ((callAt 75).lift σ) :=
    call_sat_of h 75 (callAt 75) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 75).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 75).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 75).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits76 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 76 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 76).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 76).plugs = [(Xark.R1cs.LC.var (76 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 76).base = bitBase 76 := by rfl
  have glc : (bitGLC 76 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 76).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 76 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 76).t.Sat ((callAt 76).lift σ) :=
    call_sat_of h 76 (callAt 76) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 76).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 76).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 76).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits77 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 77 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 77).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 77).plugs = [(Xark.R1cs.LC.var (77 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 77).base = bitBase 77 := by rfl
  have glc : (bitGLC 77 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 77).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 77 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 77).t.Sat ((callAt 77).lift σ) :=
    call_sat_of h 77 (callAt 77) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 77).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 77).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 77).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits78 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 78 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 78).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 78).plugs = [(Xark.R1cs.LC.var (78 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 78).base = bitBase 78 := by rfl
  have glc : (bitGLC 78 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 78).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 78 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 78).t.Sat ((callAt 78).lift σ) :=
    call_sat_of h 78 (callAt 78) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 78).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 78).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 78).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits79 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 79 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 79).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 79).plugs = [(Xark.R1cs.LC.var (79 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 79).base = bitBase 79 := by rfl
  have glc : (bitGLC 79 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 79).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 79 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 79).t.Sat ((callAt 79).lift σ) :=
    call_sat_of h 79 (callAt 79) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 79).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 79).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 79).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits80 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 80 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 80).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 80).plugs = [(Xark.R1cs.LC.var (80 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 80).base = bitBase 80 := by rfl
  have glc : (bitGLC 80 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 80).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 80 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 80).t.Sat ((callAt 80).lift σ) :=
    call_sat_of h 80 (callAt 80) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 80).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 80).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 80).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits81 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 81 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 81).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 81).plugs = [(Xark.R1cs.LC.var (81 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 81).base = bitBase 81 := by rfl
  have glc : (bitGLC 81 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 81).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 81 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 81).t.Sat ((callAt 81).lift σ) :=
    call_sat_of h 81 (callAt 81) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 81).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 81).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 81).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits82 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 82 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 82).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 82).plugs = [(Xark.R1cs.LC.var (82 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 82).base = bitBase 82 := by rfl
  have glc : (bitGLC 82 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 82).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 82 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 82).t.Sat ((callAt 82).lift σ) :=
    call_sat_of h 82 (callAt 82) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 82).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 82).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 82).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits83 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 83 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 83).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 83).plugs = [(Xark.R1cs.LC.var (83 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 83).base = bitBase 83 := by rfl
  have glc : (bitGLC 83 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 83).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 83 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 83).t.Sat ((callAt 83).lift σ) :=
    call_sat_of h 83 (callAt 83) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 83).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 83).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 83).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits84 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 84 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 84).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 84).plugs = [(Xark.R1cs.LC.var (84 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 84).base = bitBase 84 := by rfl
  have glc : (bitGLC 84 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 84).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 84 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 84).t.Sat ((callAt 84).lift σ) :=
    call_sat_of h 84 (callAt 84) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 84).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 84).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 84).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits85 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 85 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 85).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 85).plugs = [(Xark.R1cs.LC.var (85 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 85).base = bitBase 85 := by rfl
  have glc : (bitGLC 85 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 85).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 85 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 85).t.Sat ((callAt 85).lift σ) :=
    call_sat_of h 85 (callAt 85) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 85).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 85).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 85).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits86 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 86 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 86).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 86).plugs = [(Xark.R1cs.LC.var (86 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 86).base = bitBase 86 := by rfl
  have glc : (bitGLC 86 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 86).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 86 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 86).t.Sat ((callAt 86).lift σ) :=
    call_sat_of h 86 (callAt 86) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 86).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 86).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 86).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits87 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 87 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 87).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 87).plugs = [(Xark.R1cs.LC.var (87 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 87).base = bitBase 87 := by rfl
  have glc : (bitGLC 87 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 87).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 87 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 87).t.Sat ((callAt 87).lift σ) :=
    call_sat_of h 87 (callAt 87) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 87).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 87).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 87).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits88 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 88 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 88).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 88).plugs = [(Xark.R1cs.LC.var (88 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 88).base = bitBase 88 := by rfl
  have glc : (bitGLC 88 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 88).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 88 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 88).t.Sat ((callAt 88).lift σ) :=
    call_sat_of h 88 (callAt 88) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 88).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 88).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 88).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits89 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 89 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 89).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 89).plugs = [(Xark.R1cs.LC.var (89 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 89).base = bitBase 89 := by rfl
  have glc : (bitGLC 89 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 89).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 89 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 89).t.Sat ((callAt 89).lift σ) :=
    call_sat_of h 89 (callAt 89) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 89).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 89).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 89).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits90 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 90 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 90).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 90).plugs = [(Xark.R1cs.LC.var (90 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 90).base = bitBase 90 := by rfl
  have glc : (bitGLC 90 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 90).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 90 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 90).t.Sat ((callAt 90).lift σ) :=
    call_sat_of h 90 (callAt 90) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 90).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 90).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 90).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits91 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 91 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 91).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 91).plugs = [(Xark.R1cs.LC.var (91 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 91).base = bitBase 91 := by rfl
  have glc : (bitGLC 91 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 91).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 91 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 91).t.Sat ((callAt 91).lift σ) :=
    call_sat_of h 91 (callAt 91) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 91).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 91).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 91).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits92 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 92 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 92).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 92).plugs = [(Xark.R1cs.LC.var (92 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 92).base = bitBase 92 := by rfl
  have glc : (bitGLC 92 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 92).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 92 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 92).t.Sat ((callAt 92).lift σ) :=
    call_sat_of h 92 (callAt 92) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 92).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 92).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 92).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits93 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 93 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 93).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 93).plugs = [(Xark.R1cs.LC.var (93 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 93).base = bitBase 93 := by rfl
  have glc : (bitGLC 93 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 93).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 93 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 93).t.Sat ((callAt 93).lift σ) :=
    call_sat_of h 93 (callAt 93) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 93).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 93).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 93).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits94 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 94 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 94).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 94).plugs = [(Xark.R1cs.LC.var (94 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 94).base = bitBase 94 := by rfl
  have glc : (bitGLC 94 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 94).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 94 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 94).t.Sat ((callAt 94).lift σ) :=
    call_sat_of h 94 (callAt 94) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 94).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 94).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 94).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits95 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 95 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 95).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 95).plugs = [(Xark.R1cs.LC.var (95 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 95).base = bitBase 95 := by rfl
  have glc : (bitGLC 95 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 95).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 95 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 95).t.Sat ((callAt 95).lift σ) :=
    call_sat_of h 95 (callAt 95) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 95).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 95).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 95).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits96 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 96 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 96).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 96).plugs = [(Xark.R1cs.LC.var (96 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 96).base = bitBase 96 := by rfl
  have glc : (bitGLC 96 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 96).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 96 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 96).t.Sat ((callAt 96).lift σ) :=
    call_sat_of h 96 (callAt 96) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 96).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 96).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 96).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits97 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 97 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 97).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 97).plugs = [(Xark.R1cs.LC.var (97 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 97).base = bitBase 97 := by rfl
  have glc : (bitGLC 97 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 97).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 97 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 97).t.Sat ((callAt 97).lift σ) :=
    call_sat_of h 97 (callAt 97) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 97).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 97).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 97).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits98 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 98 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 98).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 98).plugs = [(Xark.R1cs.LC.var (98 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 98).base = bitBase 98 := by rfl
  have glc : (bitGLC 98 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 98).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 98 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 98).t.Sat ((callAt 98).lift σ) :=
    call_sat_of h 98 (callAt 98) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 98).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 98).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 98).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits99 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 99 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 99).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 99).plugs = [(Xark.R1cs.LC.var (99 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 99).base = bitBase 99 := by rfl
  have glc : (bitGLC 99 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 99).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 99 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 99).t.Sat ((callAt 99).lift σ) :=
    call_sat_of h 99 (callAt 99) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 99).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 99).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 99).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits100 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 100 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 100).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 100).plugs = [(Xark.R1cs.LC.var (100 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 100).base = bitBase 100 := by rfl
  have glc : (bitGLC 100 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 100).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 100 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 100).t.Sat ((callAt 100).lift σ) :=
    call_sat_of h 100 (callAt 100) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 100).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 100).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 100).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits101 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 101 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 101).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 101).plugs = [(Xark.R1cs.LC.var (101 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 101).base = bitBase 101 := by rfl
  have glc : (bitGLC 101 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 101).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 101 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 101).t.Sat ((callAt 101).lift σ) :=
    call_sat_of h 101 (callAt 101) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 101).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 101).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 101).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits102 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 102 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 102).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 102).plugs = [(Xark.R1cs.LC.var (102 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 102).base = bitBase 102 := by rfl
  have glc : (bitGLC 102 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 102).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 102 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 102).t.Sat ((callAt 102).lift σ) :=
    call_sat_of h 102 (callAt 102) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 102).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 102).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 102).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits103 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 103 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 103).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 103).plugs = [(Xark.R1cs.LC.var (103 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 103).base = bitBase 103 := by rfl
  have glc : (bitGLC 103 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 103).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 103 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 103).t.Sat ((callAt 103).lift σ) :=
    call_sat_of h 103 (callAt 103) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 103).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 103).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 103).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits104 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 104 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 104).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 104).plugs = [(Xark.R1cs.LC.var (104 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 104).base = bitBase 104 := by rfl
  have glc : (bitGLC 104 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 104).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 104 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 104).t.Sat ((callAt 104).lift σ) :=
    call_sat_of h 104 (callAt 104) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 104).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 104).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 104).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits105 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 105 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 105).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 105).plugs = [(Xark.R1cs.LC.var (105 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 105).base = bitBase 105 := by rfl
  have glc : (bitGLC 105 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 105).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 105 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 105).t.Sat ((callAt 105).lift σ) :=
    call_sat_of h 105 (callAt 105) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 105).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 105).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 105).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits106 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 106 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 106).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 106).plugs = [(Xark.R1cs.LC.var (106 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 106).base = bitBase 106 := by rfl
  have glc : (bitGLC 106 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 106).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 106 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 106).t.Sat ((callAt 106).lift σ) :=
    call_sat_of h 106 (callAt 106) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 106).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 106).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 106).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits107 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 107 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 107).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 107).plugs = [(Xark.R1cs.LC.var (107 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 107).base = bitBase 107 := by rfl
  have glc : (bitGLC 107 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 107).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 107 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 107).t.Sat ((callAt 107).lift σ) :=
    call_sat_of h 107 (callAt 107) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 107).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 107).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 107).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits108 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 108 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 108).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 108).plugs = [(Xark.R1cs.LC.var (108 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 108).base = bitBase 108 := by rfl
  have glc : (bitGLC 108 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 108).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 108 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 108).t.Sat ((callAt 108).lift σ) :=
    call_sat_of h 108 (callAt 108) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 108).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 108).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 108).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits109 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 109 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 109).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 109).plugs = [(Xark.R1cs.LC.var (109 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 109).base = bitBase 109 := by rfl
  have glc : (bitGLC 109 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 109).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 109 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 109).t.Sat ((callAt 109).lift σ) :=
    call_sat_of h 109 (callAt 109) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 109).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 109).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 109).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits110 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 110 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 110).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 110).plugs = [(Xark.R1cs.LC.var (110 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 110).base = bitBase 110 := by rfl
  have glc : (bitGLC 110 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 110).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 110 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 110).t.Sat ((callAt 110).lift σ) :=
    call_sat_of h 110 (callAt 110) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 110).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 110).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 110).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits111 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 111 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 111).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 111).plugs = [(Xark.R1cs.LC.var (111 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 111).base = bitBase 111 := by rfl
  have glc : (bitGLC 111 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 111).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 111 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 111).t.Sat ((callAt 111).lift σ) :=
    call_sat_of h 111 (callAt 111) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 111).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 111).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 111).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits112 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 112 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 112).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 112).plugs = [(Xark.R1cs.LC.var (112 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 112).base = bitBase 112 := by rfl
  have glc : (bitGLC 112 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 112).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 112 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 112).t.Sat ((callAt 112).lift σ) :=
    call_sat_of h 112 (callAt 112) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 112).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 112).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 112).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits113 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 113 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 113).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 113).plugs = [(Xark.R1cs.LC.var (113 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 113).base = bitBase 113 := by rfl
  have glc : (bitGLC 113 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 113).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 113 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 113).t.Sat ((callAt 113).lift σ) :=
    call_sat_of h 113 (callAt 113) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 113).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 113).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 113).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits114 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 114 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 114).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 114).plugs = [(Xark.R1cs.LC.var (114 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 114).base = bitBase 114 := by rfl
  have glc : (bitGLC 114 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 114).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 114 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 114).t.Sat ((callAt 114).lift σ) :=
    call_sat_of h 114 (callAt 114) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 114).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 114).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 114).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits115 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 115 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 115).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 115).plugs = [(Xark.R1cs.LC.var (115 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 115).base = bitBase 115 := by rfl
  have glc : (bitGLC 115 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 115).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 115 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 115).t.Sat ((callAt 115).lift σ) :=
    call_sat_of h 115 (callAt 115) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 115).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 115).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 115).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits116 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 116 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 116).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 116).plugs = [(Xark.R1cs.LC.var (116 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 116).base = bitBase 116 := by rfl
  have glc : (bitGLC 116 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 116).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 116 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 116).t.Sat ((callAt 116).lift σ) :=
    call_sat_of h 116 (callAt 116) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 116).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 116).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 116).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits117 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 117 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 117).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 117).plugs = [(Xark.R1cs.LC.var (117 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 117).base = bitBase 117 := by rfl
  have glc : (bitGLC 117 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 117).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 117 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 117).t.Sat ((callAt 117).lift σ) :=
    call_sat_of h 117 (callAt 117) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 117).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 117).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 117).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits118 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 118 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 118).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 118).plugs = [(Xark.R1cs.LC.var (118 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 118).base = bitBase 118 := by rfl
  have glc : (bitGLC 118 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 118).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 118 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 118).t.Sat ((callAt 118).lift σ) :=
    call_sat_of h 118 (callAt 118) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 118).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 118).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 118).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits119 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 119 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 119).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 119).plugs = [(Xark.R1cs.LC.var (119 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 119).base = bitBase 119 := by rfl
  have glc : (bitGLC 119 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 119).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 119 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 119).t.Sat ((callAt 119).lift σ) :=
    call_sat_of h 119 (callAt 119) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 119).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 119).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 119).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits120 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 120 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 120).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 120).plugs = [(Xark.R1cs.LC.var (120 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 120).base = bitBase 120 := by rfl
  have glc : (bitGLC 120 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 120).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 120 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 120).t.Sat ((callAt 120).lift σ) :=
    call_sat_of h 120 (callAt 120) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 120).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 120).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 120).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits121 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 121 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 121).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 121).plugs = [(Xark.R1cs.LC.var (121 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 121).base = bitBase 121 := by rfl
  have glc : (bitGLC 121 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 121).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 121 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 121).t.Sat ((callAt 121).lift σ) :=
    call_sat_of h 121 (callAt 121) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 121).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 121).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 121).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits122 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 122 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 122).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 122).plugs = [(Xark.R1cs.LC.var (122 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 122).base = bitBase 122 := by rfl
  have glc : (bitGLC 122 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 122).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 122 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 122).t.Sat ((callAt 122).lift σ) :=
    call_sat_of h 122 (callAt 122) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 122).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 122).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 122).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits123 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 123 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 123).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 123).plugs = [(Xark.R1cs.LC.var (123 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 123).base = bitBase 123 := by rfl
  have glc : (bitGLC 123 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 123).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 123 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 123).t.Sat ((callAt 123).lift σ) :=
    call_sat_of h 123 (callAt 123) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 123).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 123).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 123).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits124 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 124 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 124).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 124).plugs = [(Xark.R1cs.LC.var (124 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 124).base = bitBase 124 := by rfl
  have glc : (bitGLC 124 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 124).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 124 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 124).t.Sat ((callAt 124).lift σ) :=
    call_sat_of h 124 (callAt 124) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 124).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 124).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 124).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits125 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 125 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 125).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 125).plugs = [(Xark.R1cs.LC.var (125 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 125).base = bitBase 125 := by rfl
  have glc : (bitGLC 125 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 125).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 125 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 125).t.Sat ((callAt 125).lift σ) :=
    call_sat_of h 125 (callAt 125) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 125).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 125).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 125).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits126 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 126 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 126).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 126).plugs = [(Xark.R1cs.LC.var (126 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 126).base = bitBase 126 := by rfl
  have glc : (bitGLC 126 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 126).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 126 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 126).t.Sat ((callAt 126).lift σ) :=
    call_sat_of h 126 (callAt 126) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 126).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 126).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 126).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits127 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 127 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 127).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 127).plugs = [(Xark.R1cs.LC.var (127 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 127).base = bitBase 127 := by rfl
  have glc : (bitGLC 127 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 127).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 127 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 127).t.Sat ((callAt 127).lift σ) :=
    call_sat_of h 127 (callAt 127) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 127).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 127).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 127).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits128 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 128 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 128).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 128).plugs = [(Xark.R1cs.LC.var (128 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 128).base = bitBase 128 := by rfl
  have glc : (bitGLC 128 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 128).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 128 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 128).t.Sat ((callAt 128).lift σ) :=
    call_sat_of h 128 (callAt 128) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 128).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 128).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 128).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits129 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 129 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 129).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 129).plugs = [(Xark.R1cs.LC.var (129 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 129).base = bitBase 129 := by rfl
  have glc : (bitGLC 129 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 129).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 129 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 129).t.Sat ((callAt 129).lift σ) :=
    call_sat_of h 129 (callAt 129) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 129).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 129).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 129).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits130 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 130 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 130).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 130).plugs = [(Xark.R1cs.LC.var (130 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 130).base = bitBase 130 := by rfl
  have glc : (bitGLC 130 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 130).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 130 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 130).t.Sat ((callAt 130).lift σ) :=
    call_sat_of h 130 (callAt 130) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 130).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 130).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 130).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits131 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 131 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 131).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 131).plugs = [(Xark.R1cs.LC.var (131 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 131).base = bitBase 131 := by rfl
  have glc : (bitGLC 131 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 131).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 131 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 131).t.Sat ((callAt 131).lift σ) :=
    call_sat_of h 131 (callAt 131) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 131).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 131).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 131).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits132 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 132 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 132).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 132).plugs = [(Xark.R1cs.LC.var (132 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 132).base = bitBase 132 := by rfl
  have glc : (bitGLC 132 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 132).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 132 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 132).t.Sat ((callAt 132).lift σ) :=
    call_sat_of h 132 (callAt 132) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 132).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 132).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 132).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits133 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 133 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 133).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 133).plugs = [(Xark.R1cs.LC.var (133 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 133).base = bitBase 133 := by rfl
  have glc : (bitGLC 133 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 133).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 133 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 133).t.Sat ((callAt 133).lift σ) :=
    call_sat_of h 133 (callAt 133) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 133).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 133).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 133).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits134 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 134 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 134).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 134).plugs = [(Xark.R1cs.LC.var (134 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 134).base = bitBase 134 := by rfl
  have glc : (bitGLC 134 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 134).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 134 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 134).t.Sat ((callAt 134).lift σ) :=
    call_sat_of h 134 (callAt 134) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 134).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 134).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 134).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits135 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 135 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 135).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 135).plugs = [(Xark.R1cs.LC.var (135 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 135).base = bitBase 135 := by rfl
  have glc : (bitGLC 135 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 135).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 135 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 135).t.Sat ((callAt 135).lift σ) :=
    call_sat_of h 135 (callAt 135) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 135).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 135).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 135).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits136 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 136 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 136).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 136).plugs = [(Xark.R1cs.LC.var (136 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 136).base = bitBase 136 := by rfl
  have glc : (bitGLC 136 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 136).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 136 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 136).t.Sat ((callAt 136).lift σ) :=
    call_sat_of h 136 (callAt 136) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 136).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 136).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 136).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits137 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 137 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 137).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 137).plugs = [(Xark.R1cs.LC.var (137 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 137).base = bitBase 137 := by rfl
  have glc : (bitGLC 137 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 137).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 137 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 137).t.Sat ((callAt 137).lift σ) :=
    call_sat_of h 137 (callAt 137) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 137).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 137).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 137).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits138 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 138 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 138).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 138).plugs = [(Xark.R1cs.LC.var (138 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 138).base = bitBase 138 := by rfl
  have glc : (bitGLC 138 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 138).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 138 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 138).t.Sat ((callAt 138).lift σ) :=
    call_sat_of h 138 (callAt 138) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 138).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 138).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 138).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits139 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 139 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 139).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 139).plugs = [(Xark.R1cs.LC.var (139 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 139).base = bitBase 139 := by rfl
  have glc : (bitGLC 139 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 139).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 139 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 139).t.Sat ((callAt 139).lift σ) :=
    call_sat_of h 139 (callAt 139) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 139).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 139).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 139).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits140 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 140 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 140).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 140).plugs = [(Xark.R1cs.LC.var (140 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 140).base = bitBase 140 := by rfl
  have glc : (bitGLC 140 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 140).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 140 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 140).t.Sat ((callAt 140).lift σ) :=
    call_sat_of h 140 (callAt 140) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 140).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 140).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 140).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits141 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 141 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 141).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 141).plugs = [(Xark.R1cs.LC.var (141 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 141).base = bitBase 141 := by rfl
  have glc : (bitGLC 141 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 141).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 141 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 141).t.Sat ((callAt 141).lift σ) :=
    call_sat_of h 141 (callAt 141) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 141).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 141).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 141).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits142 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 142 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 142).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 142).plugs = [(Xark.R1cs.LC.var (142 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 142).base = bitBase 142 := by rfl
  have glc : (bitGLC 142 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 142).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 142 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 142).t.Sat ((callAt 142).lift σ) :=
    call_sat_of h 142 (callAt 142) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 142).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 142).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 142).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits143 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 143 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 143).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 143).plugs = [(Xark.R1cs.LC.var (143 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 143).base = bitBase 143 := by rfl
  have glc : (bitGLC 143 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 143).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 143 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 143).t.Sat ((callAt 143).lift σ) :=
    call_sat_of h 143 (callAt 143) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 143).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 143).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 143).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits144 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 144 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 144).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 144).plugs = [(Xark.R1cs.LC.var (144 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 144).base = bitBase 144 := by rfl
  have glc : (bitGLC 144 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 144).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 144 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 144).t.Sat ((callAt 144).lift σ) :=
    call_sat_of h 144 (callAt 144) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 144).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 144).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 144).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits145 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 145 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 145).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 145).plugs = [(Xark.R1cs.LC.var (145 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 145).base = bitBase 145 := by rfl
  have glc : (bitGLC 145 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 145).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 145 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 145).t.Sat ((callAt 145).lift σ) :=
    call_sat_of h 145 (callAt 145) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 145).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 145).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 145).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits146 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 146 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 146).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 146).plugs = [(Xark.R1cs.LC.var (146 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 146).base = bitBase 146 := by rfl
  have glc : (bitGLC 146 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 146).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 146 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 146).t.Sat ((callAt 146).lift σ) :=
    call_sat_of h 146 (callAt 146) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 146).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 146).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 146).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits147 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 147 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 147).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 147).plugs = [(Xark.R1cs.LC.var (147 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 147).base = bitBase 147 := by rfl
  have glc : (bitGLC 147 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 147).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 147 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 147).t.Sat ((callAt 147).lift σ) :=
    call_sat_of h 147 (callAt 147) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 147).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 147).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 147).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits148 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 148 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 148).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 148).plugs = [(Xark.R1cs.LC.var (148 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 148).base = bitBase 148 := by rfl
  have glc : (bitGLC 148 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 148).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 148 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 148).t.Sat ((callAt 148).lift σ) :=
    call_sat_of h 148 (callAt 148) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 148).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 148).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 148).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits149 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 149 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 149).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 149).plugs = [(Xark.R1cs.LC.var (149 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 149).base = bitBase 149 := by rfl
  have glc : (bitGLC 149 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 149).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 149 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 149).t.Sat ((callAt 149).lift σ) :=
    call_sat_of h 149 (callAt 149) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 149).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 149).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 149).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits150 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 150 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 150).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 150).plugs = [(Xark.R1cs.LC.var (150 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 150).base = bitBase 150 := by rfl
  have glc : (bitGLC 150 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 150).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 150 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 150).t.Sat ((callAt 150).lift σ) :=
    call_sat_of h 150 (callAt 150) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 150).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 150).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 150).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits151 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 151 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 151).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 151).plugs = [(Xark.R1cs.LC.var (151 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 151).base = bitBase 151 := by rfl
  have glc : (bitGLC 151 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 151).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 151 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 151).t.Sat ((callAt 151).lift σ) :=
    call_sat_of h 151 (callAt 151) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 151).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 151).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 151).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits152 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 152 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 152).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 152).plugs = [(Xark.R1cs.LC.var (152 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 152).base = bitBase 152 := by rfl
  have glc : (bitGLC 152 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 152).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 152 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 152).t.Sat ((callAt 152).lift σ) :=
    call_sat_of h 152 (callAt 152) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 152).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 152).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 152).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits153 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 153 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 153).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 153).plugs = [(Xark.R1cs.LC.var (153 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 153).base = bitBase 153 := by rfl
  have glc : (bitGLC 153 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 153).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 153 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 153).t.Sat ((callAt 153).lift σ) :=
    call_sat_of h 153 (callAt 153) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 153).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 153).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 153).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits154 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 154 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 154).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 154).plugs = [(Xark.R1cs.LC.var (154 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 154).base = bitBase 154 := by rfl
  have glc : (bitGLC 154 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 154).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 154 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 154).t.Sat ((callAt 154).lift σ) :=
    call_sat_of h 154 (callAt 154) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 154).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 154).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 154).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits155 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 155 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 155).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 155).plugs = [(Xark.R1cs.LC.var (155 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 155).base = bitBase 155 := by rfl
  have glc : (bitGLC 155 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 155).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 155 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 155).t.Sat ((callAt 155).lift σ) :=
    call_sat_of h 155 (callAt 155) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 155).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 155).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 155).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits156 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 156 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 156).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 156).plugs = [(Xark.R1cs.LC.var (156 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 156).base = bitBase 156 := by rfl
  have glc : (bitGLC 156 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 156).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 156 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 156).t.Sat ((callAt 156).lift σ) :=
    call_sat_of h 156 (callAt 156) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 156).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 156).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 156).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits157 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 157 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 157).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 157).plugs = [(Xark.R1cs.LC.var (157 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 157).base = bitBase 157 := by rfl
  have glc : (bitGLC 157 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 157).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 157 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 157).t.Sat ((callAt 157).lift σ) :=
    call_sat_of h 157 (callAt 157) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 157).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 157).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 157).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits158 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 158 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 158).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 158).plugs = [(Xark.R1cs.LC.var (158 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 158).base = bitBase 158 := by rfl
  have glc : (bitGLC 158 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 158).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 158 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 158).t.Sat ((callAt 158).lift σ) :=
    call_sat_of h 158 (callAt 158) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 158).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 158).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 158).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits159 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 159 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 159).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 159).plugs = [(Xark.R1cs.LC.var (159 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 159).base = bitBase 159 := by rfl
  have glc : (bitGLC 159 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 159).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 159 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 159).t.Sat ((callAt 159).lift σ) :=
    call_sat_of h 159 (callAt 159) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 159).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 159).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 159).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits160 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 160 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 160).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 160).plugs = [(Xark.R1cs.LC.var (160 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 160).base = bitBase 160 := by rfl
  have glc : (bitGLC 160 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 160).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 160 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 160).t.Sat ((callAt 160).lift σ) :=
    call_sat_of h 160 (callAt 160) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 160).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 160).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 160).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits161 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 161 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 161).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 161).plugs = [(Xark.R1cs.LC.var (161 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 161).base = bitBase 161 := by rfl
  have glc : (bitGLC 161 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 161).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 161 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 161).t.Sat ((callAt 161).lift σ) :=
    call_sat_of h 161 (callAt 161) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 161).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 161).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 161).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits162 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 162 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 162).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 162).plugs = [(Xark.R1cs.LC.var (162 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 162).base = bitBase 162 := by rfl
  have glc : (bitGLC 162 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 162).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 162 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 162).t.Sat ((callAt 162).lift σ) :=
    call_sat_of h 162 (callAt 162) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 162).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 162).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 162).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits163 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 163 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 163).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 163).plugs = [(Xark.R1cs.LC.var (163 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 163).base = bitBase 163 := by rfl
  have glc : (bitGLC 163 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 163).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 163 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 163).t.Sat ((callAt 163).lift σ) :=
    call_sat_of h 163 (callAt 163) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 163).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 163).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 163).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits164 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 164 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 164).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 164).plugs = [(Xark.R1cs.LC.var (164 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 164).base = bitBase 164 := by rfl
  have glc : (bitGLC 164 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 164).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 164 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 164).t.Sat ((callAt 164).lift σ) :=
    call_sat_of h 164 (callAt 164) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 164).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 164).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 164).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits165 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 165 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 165).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 165).plugs = [(Xark.R1cs.LC.var (165 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 165).base = bitBase 165 := by rfl
  have glc : (bitGLC 165 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 165).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 165 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 165).t.Sat ((callAt 165).lift σ) :=
    call_sat_of h 165 (callAt 165) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 165).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 165).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 165).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits166 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 166 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 166).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 166).plugs = [(Xark.R1cs.LC.var (166 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 166).base = bitBase 166 := by rfl
  have glc : (bitGLC 166 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 166).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 166 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 166).t.Sat ((callAt 166).lift σ) :=
    call_sat_of h 166 (callAt 166) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 166).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 166).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 166).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits167 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 167 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 167).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 167).plugs = [(Xark.R1cs.LC.var (167 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 167).base = bitBase 167 := by rfl
  have glc : (bitGLC 167 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 167).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 167 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 167).t.Sat ((callAt 167).lift σ) :=
    call_sat_of h 167 (callAt 167) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 167).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 167).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 167).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits168 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 168 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 168).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 168).plugs = [(Xark.R1cs.LC.var (168 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 168).base = bitBase 168 := by rfl
  have glc : (bitGLC 168 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 168).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 168 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 168).t.Sat ((callAt 168).lift σ) :=
    call_sat_of h 168 (callAt 168) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 168).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 168).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 168).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits169 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 169 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 169).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 169).plugs = [(Xark.R1cs.LC.var (169 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 169).base = bitBase 169 := by rfl
  have glc : (bitGLC 169 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 169).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 169 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 169).t.Sat ((callAt 169).lift σ) :=
    call_sat_of h 169 (callAt 169) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 169).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 169).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 169).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits170 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 170 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 170).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 170).plugs = [(Xark.R1cs.LC.var (170 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 170).base = bitBase 170 := by rfl
  have glc : (bitGLC 170 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 170).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 170 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 170).t.Sat ((callAt 170).lift σ) :=
    call_sat_of h 170 (callAt 170) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 170).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 170).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 170).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits171 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 171 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 171).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 171).plugs = [(Xark.R1cs.LC.var (171 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 171).base = bitBase 171 := by rfl
  have glc : (bitGLC 171 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 171).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 171 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 171).t.Sat ((callAt 171).lift σ) :=
    call_sat_of h 171 (callAt 171) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 171).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 171).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 171).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits172 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 172 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 172).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 172).plugs = [(Xark.R1cs.LC.var (172 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 172).base = bitBase 172 := by rfl
  have glc : (bitGLC 172 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 172).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 172 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 172).t.Sat ((callAt 172).lift σ) :=
    call_sat_of h 172 (callAt 172) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 172).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 172).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 172).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits173 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 173 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 173).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 173).plugs = [(Xark.R1cs.LC.var (173 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 173).base = bitBase 173 := by rfl
  have glc : (bitGLC 173 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 173).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 173 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 173).t.Sat ((callAt 173).lift σ) :=
    call_sat_of h 173 (callAt 173) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 173).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 173).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 173).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits174 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 174 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 174).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 174).plugs = [(Xark.R1cs.LC.var (174 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 174).base = bitBase 174 := by rfl
  have glc : (bitGLC 174 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 174).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 174 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 174).t.Sat ((callAt 174).lift σ) :=
    call_sat_of h 174 (callAt 174) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 174).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 174).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 174).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits175 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 175 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 175).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 175).plugs = [(Xark.R1cs.LC.var (175 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 175).base = bitBase 175 := by rfl
  have glc : (bitGLC 175 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 175).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 175 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 175).t.Sat ((callAt 175).lift σ) :=
    call_sat_of h 175 (callAt 175) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 175).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 175).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 175).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits176 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 176 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 176).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 176).plugs = [(Xark.R1cs.LC.var (176 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 176).base = bitBase 176 := by rfl
  have glc : (bitGLC 176 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 176).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 176 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 176).t.Sat ((callAt 176).lift σ) :=
    call_sat_of h 176 (callAt 176) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 176).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 176).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 176).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits177 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 177 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 177).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 177).plugs = [(Xark.R1cs.LC.var (177 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 177).base = bitBase 177 := by rfl
  have glc : (bitGLC 177 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 177).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 177 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 177).t.Sat ((callAt 177).lift σ) :=
    call_sat_of h 177 (callAt 177) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 177).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 177).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 177).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits178 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 178 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 178).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 178).plugs = [(Xark.R1cs.LC.var (178 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 178).base = bitBase 178 := by rfl
  have glc : (bitGLC 178 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 178).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 178 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 178).t.Sat ((callAt 178).lift σ) :=
    call_sat_of h 178 (callAt 178) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 178).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 178).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 178).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits179 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 179 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 179).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 179).plugs = [(Xark.R1cs.LC.var (179 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 179).base = bitBase 179 := by rfl
  have glc : (bitGLC 179 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 179).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 179 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 179).t.Sat ((callAt 179).lift σ) :=
    call_sat_of h 179 (callAt 179) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 179).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 179).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 179).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits180 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 180 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 180).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 180).plugs = [(Xark.R1cs.LC.var (180 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 180).base = bitBase 180 := by rfl
  have glc : (bitGLC 180 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 180).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 180 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 180).t.Sat ((callAt 180).lift σ) :=
    call_sat_of h 180 (callAt 180) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 180).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 180).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 180).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits181 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 181 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 181).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 181).plugs = [(Xark.R1cs.LC.var (181 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 181).base = bitBase 181 := by rfl
  have glc : (bitGLC 181 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 181).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 181 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 181).t.Sat ((callAt 181).lift σ) :=
    call_sat_of h 181 (callAt 181) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 181).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 181).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 181).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits182 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 182 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 182).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 182).plugs = [(Xark.R1cs.LC.var (182 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 182).base = bitBase 182 := by rfl
  have glc : (bitGLC 182 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 182).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 182 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 182).t.Sat ((callAt 182).lift σ) :=
    call_sat_of h 182 (callAt 182) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 182).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 182).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 182).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits183 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 183 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 183).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 183).plugs = [(Xark.R1cs.LC.var (183 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 183).base = bitBase 183 := by rfl
  have glc : (bitGLC 183 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 183).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 183 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 183).t.Sat ((callAt 183).lift σ) :=
    call_sat_of h 183 (callAt 183) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 183).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 183).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 183).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits184 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 184 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 184).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 184).plugs = [(Xark.R1cs.LC.var (184 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 184).base = bitBase 184 := by rfl
  have glc : (bitGLC 184 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 184).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 184 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 184).t.Sat ((callAt 184).lift σ) :=
    call_sat_of h 184 (callAt 184) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 184).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 184).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 184).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits185 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 185 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 185).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 185).plugs = [(Xark.R1cs.LC.var (185 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 185).base = bitBase 185 := by rfl
  have glc : (bitGLC 185 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 185).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 185 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 185).t.Sat ((callAt 185).lift σ) :=
    call_sat_of h 185 (callAt 185) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 185).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 185).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 185).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits186 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 186 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 186).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 186).plugs = [(Xark.R1cs.LC.var (186 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 186).base = bitBase 186 := by rfl
  have glc : (bitGLC 186 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 186).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 186 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 186).t.Sat ((callAt 186).lift σ) :=
    call_sat_of h 186 (callAt 186) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 186).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 186).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 186).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits187 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 187 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 187).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 187).plugs = [(Xark.R1cs.LC.var (187 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 187).base = bitBase 187 := by rfl
  have glc : (bitGLC 187 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 187).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 187 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 187).t.Sat ((callAt 187).lift σ) :=
    call_sat_of h 187 (callAt 187) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 187).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 187).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 187).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits188 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 188 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 188).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 188).plugs = [(Xark.R1cs.LC.var (188 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 188).base = bitBase 188 := by rfl
  have glc : (bitGLC 188 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 188).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 188 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 188).t.Sat ((callAt 188).lift σ) :=
    call_sat_of h 188 (callAt 188) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 188).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 188).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 188).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits189 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 189 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 189).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 189).plugs = [(Xark.R1cs.LC.var (189 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 189).base = bitBase 189 := by rfl
  have glc : (bitGLC 189 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 189).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 189 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 189).t.Sat ((callAt 189).lift σ) :=
    call_sat_of h 189 (callAt 189) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 189).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 189).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 189).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits190 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 190 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 190).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 190).plugs = [(Xark.R1cs.LC.var (190 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 190).base = bitBase 190 := by rfl
  have glc : (bitGLC 190 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 190).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 190 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 190).t.Sat ((callAt 190).lift σ) :=
    call_sat_of h 190 (callAt 190) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 190).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 190).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 190).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits191 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 191 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 191).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 191).plugs = [(Xark.R1cs.LC.var (191 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 191).base = bitBase 191 := by rfl
  have glc : (bitGLC 191 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 191).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 191 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 191).t.Sat ((callAt 191).lift σ) :=
    call_sat_of h 191 (callAt 191) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 191).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 191).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 191).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits192 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 192 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 192).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 192).plugs = [(Xark.R1cs.LC.var (192 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 192).base = bitBase 192 := by rfl
  have glc : (bitGLC 192 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 192).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 192 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 192).t.Sat ((callAt 192).lift σ) :=
    call_sat_of h 192 (callAt 192) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 192).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 192).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 192).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits193 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 193 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 193).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 193).plugs = [(Xark.R1cs.LC.var (193 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 193).base = bitBase 193 := by rfl
  have glc : (bitGLC 193 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 193).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 193 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 193).t.Sat ((callAt 193).lift σ) :=
    call_sat_of h 193 (callAt 193) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 193).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 193).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 193).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits194 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 194 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 194).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 194).plugs = [(Xark.R1cs.LC.var (194 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 194).base = bitBase 194 := by rfl
  have glc : (bitGLC 194 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 194).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 194 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 194).t.Sat ((callAt 194).lift σ) :=
    call_sat_of h 194 (callAt 194) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 194).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 194).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 194).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits195 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 195 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 195).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 195).plugs = [(Xark.R1cs.LC.var (195 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 195).base = bitBase 195 := by rfl
  have glc : (bitGLC 195 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 195).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 195 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 195).t.Sat ((callAt 195).lift σ) :=
    call_sat_of h 195 (callAt 195) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 195).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 195).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 195).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits196 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 196 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 196).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 196).plugs = [(Xark.R1cs.LC.var (196 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 196).base = bitBase 196 := by rfl
  have glc : (bitGLC 196 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 196).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 196 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 196).t.Sat ((callAt 196).lift σ) :=
    call_sat_of h 196 (callAt 196) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 196).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 196).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 196).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits197 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 197 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 197).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 197).plugs = [(Xark.R1cs.LC.var (197 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 197).base = bitBase 197 := by rfl
  have glc : (bitGLC 197 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 197).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 197 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 197).t.Sat ((callAt 197).lift σ) :=
    call_sat_of h 197 (callAt 197) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 197).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 197).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 197).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits198 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 198 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 198).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 198).plugs = [(Xark.R1cs.LC.var (198 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 198).base = bitBase 198 := by rfl
  have glc : (bitGLC 198 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 198).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 198 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 198).t.Sat ((callAt 198).lift σ) :=
    call_sat_of h 198 (callAt 198) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 198).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 198).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 198).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits199 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 199 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 199).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 199).plugs = [(Xark.R1cs.LC.var (199 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 199).base = bitBase 199 := by rfl
  have glc : (bitGLC 199 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 199).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 199 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 199).t.Sat ((callAt 199).lift σ) :=
    call_sat_of h 199 (callAt 199) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 199).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 199).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 199).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits200 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 200 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 200).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 200).plugs = [(Xark.R1cs.LC.var (200 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 200).base = bitBase 200 := by rfl
  have glc : (bitGLC 200 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 200).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 200 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 200).t.Sat ((callAt 200).lift σ) :=
    call_sat_of h 200 (callAt 200) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 200).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 200).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 200).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits201 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 201 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 201).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 201).plugs = [(Xark.R1cs.LC.var (201 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 201).base = bitBase 201 := by rfl
  have glc : (bitGLC 201 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 201).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 201 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 201).t.Sat ((callAt 201).lift σ) :=
    call_sat_of h 201 (callAt 201) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 201).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 201).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 201).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits202 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 202 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 202).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 202).plugs = [(Xark.R1cs.LC.var (202 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 202).base = bitBase 202 := by rfl
  have glc : (bitGLC 202 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 202).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 202 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 202).t.Sat ((callAt 202).lift σ) :=
    call_sat_of h 202 (callAt 202) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 202).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 202).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 202).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits203 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 203 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 203).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 203).plugs = [(Xark.R1cs.LC.var (203 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 203).base = bitBase 203 := by rfl
  have glc : (bitGLC 203 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 203).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 203 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 203).t.Sat ((callAt 203).lift σ) :=
    call_sat_of h 203 (callAt 203) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 203).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 203).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 203).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits204 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 204 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 204).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 204).plugs = [(Xark.R1cs.LC.var (204 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 204).base = bitBase 204 := by rfl
  have glc : (bitGLC 204 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 204).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 204 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 204).t.Sat ((callAt 204).lift σ) :=
    call_sat_of h 204 (callAt 204) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 204).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 204).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 204).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits205 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 205 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 205).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 205).plugs = [(Xark.R1cs.LC.var (205 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 205).base = bitBase 205 := by rfl
  have glc : (bitGLC 205 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 205).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 205 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 205).t.Sat ((callAt 205).lift σ) :=
    call_sat_of h 205 (callAt 205) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 205).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 205).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 205).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits206 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 206 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 206).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 206).plugs = [(Xark.R1cs.LC.var (206 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 206).base = bitBase 206 := by rfl
  have glc : (bitGLC 206 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 206).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 206 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 206).t.Sat ((callAt 206).lift σ) :=
    call_sat_of h 206 (callAt 206) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 206).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 206).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 206).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits207 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 207 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 207).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 207).plugs = [(Xark.R1cs.LC.var (207 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 207).base = bitBase 207 := by rfl
  have glc : (bitGLC 207 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 207).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 207 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 207).t.Sat ((callAt 207).lift σ) :=
    call_sat_of h 207 (callAt 207) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 207).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 207).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 207).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits208 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 208 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 208).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 208).plugs = [(Xark.R1cs.LC.var (208 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 208).base = bitBase 208 := by rfl
  have glc : (bitGLC 208 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 208).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 208 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 208).t.Sat ((callAt 208).lift σ) :=
    call_sat_of h 208 (callAt 208) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 208).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 208).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 208).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits209 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 209 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 209).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 209).plugs = [(Xark.R1cs.LC.var (209 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 209).base = bitBase 209 := by rfl
  have glc : (bitGLC 209 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 209).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 209 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 209).t.Sat ((callAt 209).lift σ) :=
    call_sat_of h 209 (callAt 209) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 209).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 209).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 209).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits210 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 210 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 210).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 210).plugs = [(Xark.R1cs.LC.var (210 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 210).base = bitBase 210 := by rfl
  have glc : (bitGLC 210 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 210).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 210 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 210).t.Sat ((callAt 210).lift σ) :=
    call_sat_of h 210 (callAt 210) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 210).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 210).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 210).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits211 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 211 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 211).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 211).plugs = [(Xark.R1cs.LC.var (211 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 211).base = bitBase 211 := by rfl
  have glc : (bitGLC 211 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 211).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 211 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 211).t.Sat ((callAt 211).lift σ) :=
    call_sat_of h 211 (callAt 211) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 211).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 211).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 211).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits212 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 212 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 212).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 212).plugs = [(Xark.R1cs.LC.var (212 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 212).base = bitBase 212 := by rfl
  have glc : (bitGLC 212 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 212).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 212 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 212).t.Sat ((callAt 212).lift σ) :=
    call_sat_of h 212 (callAt 212) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 212).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 212).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 212).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits213 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 213 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 213).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 213).plugs = [(Xark.R1cs.LC.var (213 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 213).base = bitBase 213 := by rfl
  have glc : (bitGLC 213 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 213).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 213 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 213).t.Sat ((callAt 213).lift σ) :=
    call_sat_of h 213 (callAt 213) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 213).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 213).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 213).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits214 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 214 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 214).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 214).plugs = [(Xark.R1cs.LC.var (214 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 214).base = bitBase 214 := by rfl
  have glc : (bitGLC 214 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 214).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 214 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 214).t.Sat ((callAt 214).lift σ) :=
    call_sat_of h 214 (callAt 214) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 214).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 214).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 214).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits215 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 215 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 215).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 215).plugs = [(Xark.R1cs.LC.var (215 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 215).base = bitBase 215 := by rfl
  have glc : (bitGLC 215 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 215).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 215 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 215).t.Sat ((callAt 215).lift σ) :=
    call_sat_of h 215 (callAt 215) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 215).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 215).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 215).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits216 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 216 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 216).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 216).plugs = [(Xark.R1cs.LC.var (216 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 216).base = bitBase 216 := by rfl
  have glc : (bitGLC 216 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 216).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 216 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 216).t.Sat ((callAt 216).lift σ) :=
    call_sat_of h 216 (callAt 216) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 216).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 216).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 216).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits217 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 217 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 217).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 217).plugs = [(Xark.R1cs.LC.var (217 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 217).base = bitBase 217 := by rfl
  have glc : (bitGLC 217 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 217).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 217 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 217).t.Sat ((callAt 217).lift σ) :=
    call_sat_of h 217 (callAt 217) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 217).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 217).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 217).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits218 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 218 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 218).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 218).plugs = [(Xark.R1cs.LC.var (218 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 218).base = bitBase 218 := by rfl
  have glc : (bitGLC 218 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 218).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 218 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 218).t.Sat ((callAt 218).lift σ) :=
    call_sat_of h 218 (callAt 218) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 218).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 218).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 218).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits219 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 219 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 219).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 219).plugs = [(Xark.R1cs.LC.var (219 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 219).base = bitBase 219 := by rfl
  have glc : (bitGLC 219 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 219).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 219 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 219).t.Sat ((callAt 219).lift σ) :=
    call_sat_of h 219 (callAt 219) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 219).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 219).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 219).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits220 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 220 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 220).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 220).plugs = [(Xark.R1cs.LC.var (220 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 220).base = bitBase 220 := by rfl
  have glc : (bitGLC 220 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 220).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 220 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 220).t.Sat ((callAt 220).lift σ) :=
    call_sat_of h 220 (callAt 220) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 220).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 220).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 220).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits221 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 221 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 221).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 221).plugs = [(Xark.R1cs.LC.var (221 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 221).base = bitBase 221 := by rfl
  have glc : (bitGLC 221 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 221).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 221 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 221).t.Sat ((callAt 221).lift σ) :=
    call_sat_of h 221 (callAt 221) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 221).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 221).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 221).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits222 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 222 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 222).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 222).plugs = [(Xark.R1cs.LC.var (222 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 222).base = bitBase 222 := by rfl
  have glc : (bitGLC 222 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 222).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 222 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 222).t.Sat ((callAt 222).lift σ) :=
    call_sat_of h 222 (callAt 222) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 222).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 222).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 222).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits223 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 223 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 223).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 223).plugs = [(Xark.R1cs.LC.var (223 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 223).base = bitBase 223 := by rfl
  have glc : (bitGLC 223 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 223).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 223 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 223).t.Sat ((callAt 223).lift σ) :=
    call_sat_of h 223 (callAt 223) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 223).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 223).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 223).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits224 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 224 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 224).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 224).plugs = [(Xark.R1cs.LC.var (224 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 224).base = bitBase 224 := by rfl
  have glc : (bitGLC 224 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 224).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 224 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 224).t.Sat ((callAt 224).lift σ) :=
    call_sat_of h 224 (callAt 224) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 224).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 224).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 224).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits225 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 225 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 225).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 225).plugs = [(Xark.R1cs.LC.var (225 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 225).base = bitBase 225 := by rfl
  have glc : (bitGLC 225 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 225).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 225 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 225).t.Sat ((callAt 225).lift σ) :=
    call_sat_of h 225 (callAt 225) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 225).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 225).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 225).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits226 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 226 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 226).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 226).plugs = [(Xark.R1cs.LC.var (226 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 226).base = bitBase 226 := by rfl
  have glc : (bitGLC 226 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 226).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 226 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 226).t.Sat ((callAt 226).lift σ) :=
    call_sat_of h 226 (callAt 226) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 226).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 226).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 226).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits227 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 227 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 227).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 227).plugs = [(Xark.R1cs.LC.var (227 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 227).base = bitBase 227 := by rfl
  have glc : (bitGLC 227 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 227).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 227 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 227).t.Sat ((callAt 227).lift σ) :=
    call_sat_of h 227 (callAt 227) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 227).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 227).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 227).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits228 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 228 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 228).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 228).plugs = [(Xark.R1cs.LC.var (228 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 228).base = bitBase 228 := by rfl
  have glc : (bitGLC 228 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 228).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 228 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 228).t.Sat ((callAt 228).lift σ) :=
    call_sat_of h 228 (callAt 228) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 228).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 228).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 228).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits229 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 229 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 229).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 229).plugs = [(Xark.R1cs.LC.var (229 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 229).base = bitBase 229 := by rfl
  have glc : (bitGLC 229 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 229).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 229 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 229).t.Sat ((callAt 229).lift σ) :=
    call_sat_of h 229 (callAt 229) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 229).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 229).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 229).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits230 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 230 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 230).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 230).plugs = [(Xark.R1cs.LC.var (230 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 230).base = bitBase 230 := by rfl
  have glc : (bitGLC 230 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 230).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 230 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 230).t.Sat ((callAt 230).lift σ) :=
    call_sat_of h 230 (callAt 230) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 230).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 230).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 230).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits231 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 231 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 231).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 231).plugs = [(Xark.R1cs.LC.var (231 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 231).base = bitBase 231 := by rfl
  have glc : (bitGLC 231 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 231).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 231 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 231).t.Sat ((callAt 231).lift σ) :=
    call_sat_of h 231 (callAt 231) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 231).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 231).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 231).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits232 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 232 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 232).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 232).plugs = [(Xark.R1cs.LC.var (232 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 232).base = bitBase 232 := by rfl
  have glc : (bitGLC 232 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 232).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 232 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 232).t.Sat ((callAt 232).lift σ) :=
    call_sat_of h 232 (callAt 232) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 232).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 232).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 232).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits233 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 233 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 233).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 233).plugs = [(Xark.R1cs.LC.var (233 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 233).base = bitBase 233 := by rfl
  have glc : (bitGLC 233 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 233).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 233 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 233).t.Sat ((callAt 233).lift σ) :=
    call_sat_of h 233 (callAt 233) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 233).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 233).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 233).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits234 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 234 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 234).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 234).plugs = [(Xark.R1cs.LC.var (234 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 234).base = bitBase 234 := by rfl
  have glc : (bitGLC 234 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 234).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 234 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 234).t.Sat ((callAt 234).lift σ) :=
    call_sat_of h 234 (callAt 234) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 234).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 234).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 234).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits235 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 235 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 235).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 235).plugs = [(Xark.R1cs.LC.var (235 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 235).base = bitBase 235 := by rfl
  have glc : (bitGLC 235 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 235).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 235 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 235).t.Sat ((callAt 235).lift σ) :=
    call_sat_of h 235 (callAt 235) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 235).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 235).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 235).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits236 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 236 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 236).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 236).plugs = [(Xark.R1cs.LC.var (236 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 236).base = bitBase 236 := by rfl
  have glc : (bitGLC 236 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 236).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 236 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 236).t.Sat ((callAt 236).lift σ) :=
    call_sat_of h 236 (callAt 236) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 236).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 236).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 236).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits237 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 237 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 237).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 237).plugs = [(Xark.R1cs.LC.var (237 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 237).base = bitBase 237 := by rfl
  have glc : (bitGLC 237 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 237).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 237 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 237).t.Sat ((callAt 237).lift σ) :=
    call_sat_of h 237 (callAt 237) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 237).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 237).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 237).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits238 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 238 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 238).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 238).plugs = [(Xark.R1cs.LC.var (238 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 238).base = bitBase 238 := by rfl
  have glc : (bitGLC 238 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 238).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 238 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 238).t.Sat ((callAt 238).lift σ) :=
    call_sat_of h 238 (callAt 238) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 238).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 238).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 238).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits239 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 239 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 239).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 239).plugs = [(Xark.R1cs.LC.var (239 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 239).base = bitBase 239 := by rfl
  have glc : (bitGLC 239 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 239).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 239 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 239).t.Sat ((callAt 239).lift σ) :=
    call_sat_of h 239 (callAt 239) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 239).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 239).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 239).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits240 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 240 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 240).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 240).plugs = [(Xark.R1cs.LC.var (240 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 240).base = bitBase 240 := by rfl
  have glc : (bitGLC 240 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 240).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 240 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 240).t.Sat ((callAt 240).lift σ) :=
    call_sat_of h 240 (callAt 240) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 240).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 240).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 240).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits241 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 241 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 241).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 241).plugs = [(Xark.R1cs.LC.var (241 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 241).base = bitBase 241 := by rfl
  have glc : (bitGLC 241 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 241).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 241 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 241).t.Sat ((callAt 241).lift σ) :=
    call_sat_of h 241 (callAt 241) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 241).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 241).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 241).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits242 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 242 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 242).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 242).plugs = [(Xark.R1cs.LC.var (242 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 242).base = bitBase 242 := by rfl
  have glc : (bitGLC 242 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 242).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 242 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 242).t.Sat ((callAt 242).lift σ) :=
    call_sat_of h 242 (callAt 242) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 242).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 242).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 242).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits243 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 243 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 243).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 243).plugs = [(Xark.R1cs.LC.var (243 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 243).base = bitBase 243 := by rfl
  have glc : (bitGLC 243 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 243).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 243 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 243).t.Sat ((callAt 243).lift σ) :=
    call_sat_of h 243 (callAt 243) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 243).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 243).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 243).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits244 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 244 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 244).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 244).plugs = [(Xark.R1cs.LC.var (244 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 244).base = bitBase 244 := by rfl
  have glc : (bitGLC 244 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 244).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 244 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 244).t.Sat ((callAt 244).lift σ) :=
    call_sat_of h 244 (callAt 244) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 244).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 244).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 244).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits245 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 245 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 245).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 245).plugs = [(Xark.R1cs.LC.var (245 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 245).base = bitBase 245 := by rfl
  have glc : (bitGLC 245 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 245).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 245 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 245).t.Sat ((callAt 245).lift σ) :=
    call_sat_of h 245 (callAt 245) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 245).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 245).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 245).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits246 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 246 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 246).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 246).plugs = [(Xark.R1cs.LC.var (246 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 246).base = bitBase 246 := by rfl
  have glc : (bitGLC 246 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 246).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 246 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 246).t.Sat ((callAt 246).lift σ) :=
    call_sat_of h 246 (callAt 246) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 246).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 246).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 246).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits247 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 247 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 247).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 247).plugs = [(Xark.R1cs.LC.var (247 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 247).base = bitBase 247 := by rfl
  have glc : (bitGLC 247 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 247).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 247 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 247).t.Sat ((callAt 247).lift σ) :=
    call_sat_of h 247 (callAt 247) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 247).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 247).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 247).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits248 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 248 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 248).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 248).plugs = [(Xark.R1cs.LC.var (248 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 248).base = bitBase 248 := by rfl
  have glc : (bitGLC 248 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 248).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 248 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 248).t.Sat ((callAt 248).lift σ) :=
    call_sat_of h 248 (callAt 248) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 248).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 248).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 248).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits249 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 249 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 249).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 249).plugs = [(Xark.R1cs.LC.var (249 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 249).base = bitBase 249 := by rfl
  have glc : (bitGLC 249 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 249).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 249 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 249).t.Sat ((callAt 249).lift σ) :=
    call_sat_of h 249 (callAt 249) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 249).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 249).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 249).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits250 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 250 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 250).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 250).plugs = [(Xark.R1cs.LC.var (250 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 250).base = bitBase 250 := by rfl
  have glc : (bitGLC 250 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 250).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 250 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 250).t.Sat ((callAt 250).lift σ) :=
    call_sat_of h 250 (callAt 250) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 250).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 250).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 250).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits251 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 251 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 251).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 251).plugs = [(Xark.R1cs.LC.var (251 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 251).base = bitBase 251 := by rfl
  have glc : (bitGLC 251 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 251).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 251 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 251).t.Sat ((callAt 251).lift σ) :=
    call_sat_of h 251 (callAt 251) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 251).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 251).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 251).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits252 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 252 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 252).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 252).plugs = [(Xark.R1cs.LC.var (252 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 252).base = bitBase 252 := by rfl
  have glc : (bitGLC 252 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 252).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 252 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 252).t.Sat ((callAt 252).lift σ) :=
    call_sat_of h 252 (callAt 252) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 252).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 252).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 252).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits253 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 253 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 253).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 253).plugs = [(Xark.R1cs.LC.var (253 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 253).base = bitBase 253 := by rfl
  have glc : (bitGLC 253 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 253).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 253 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 253).t.Sat ((callAt 253).lift σ) :=
    call_sat_of h 253 (callAt 253) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 253).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 253).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 253).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits254 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 254 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 254).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 254).plugs = [(Xark.R1cs.LC.var (254 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 254).base = bitBase 254 := by rfl
  have glc : (bitGLC 254 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 254).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 254 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 254).t.Sat ((callAt 254).lift σ) :=
    call_sat_of h 254 (callAt 254) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 254).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 254).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 254).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits255 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 255 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 255).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 255).plugs = [(Xark.R1cs.LC.var (255 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 255).base = bitBase 255 := by rfl
  have glc : (bitGLC 255 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 255).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 255 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 255).t.Sat ((callAt 255).lift σ) :=
    call_sat_of h 255 (callAt 255) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 255).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 255).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 255).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits256 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 256 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 256).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 256).plugs = [(Xark.R1cs.LC.var (256 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 256).base = bitBase 256 := by rfl
  have glc : (bitGLC 256 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 256).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 256 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 256).t.Sat ((callAt 256).lift σ) :=
    call_sat_of h 256 (callAt 256) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 256).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 256).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 256).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits257 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 257 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 257).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 257).plugs = [(Xark.R1cs.LC.var (257 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 257).base = bitBase 257 := by rfl
  have glc : (bitGLC 257 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 257).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 257 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 257).t.Sat ((callAt 257).lift σ) :=
    call_sat_of h 257 (callAt 257) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 257).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 257).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 257).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits258 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 258 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 258).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 258).plugs = [(Xark.R1cs.LC.var (258 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 258).base = bitBase 258 := by rfl
  have glc : (bitGLC 258 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 258).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 258 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 258).t.Sat ((callAt 258).lift σ) :=
    call_sat_of h 258 (callAt 258) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 258).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 258).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 258).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits259 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 259 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 259).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 259).plugs = [(Xark.R1cs.LC.var (259 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 259).base = bitBase 259 := by rfl
  have glc : (bitGLC 259 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 259).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 259 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 259).t.Sat ((callAt 259).lift σ) :=
    call_sat_of h 259 (callAt 259) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 259).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 259).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 259).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits260 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 260 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 260).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 260).plugs = [(Xark.R1cs.LC.var (260 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 260).base = bitBase 260 := by rfl
  have glc : (bitGLC 260 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 260).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 260 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 260).t.Sat ((callAt 260).lift σ) :=
    call_sat_of h 260 (callAt 260) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 260).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 260).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 260).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits261 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 261 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 261).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 261).plugs = [(Xark.R1cs.LC.var (261 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 261).base = bitBase 261 := by rfl
  have glc : (bitGLC 261 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 261).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 261 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 261).t.Sat ((callAt 261).lift σ) :=
    call_sat_of h 261 (callAt 261) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 261).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 261).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 261).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits262 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 262 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 262).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 262).plugs = [(Xark.R1cs.LC.var (262 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 262).base = bitBase 262 := by rfl
  have glc : (bitGLC 262 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 262).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 262 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 262).t.Sat ((callAt 262).lift σ) :=
    call_sat_of h 262 (callAt 262) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 262).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 262).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 262).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits263 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 263 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 263).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 263).plugs = [(Xark.R1cs.LC.var (263 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 263).base = bitBase 263 := by rfl
  have glc : (bitGLC 263 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 263).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 263 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 263).t.Sat ((callAt 263).lift σ) :=
    call_sat_of h 263 (callAt 263) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 263).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 263).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 263).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits264 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 264 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 264).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 264).plugs = [(Xark.R1cs.LC.var (264 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 264).base = bitBase 264 := by rfl
  have glc : (bitGLC 264 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 264).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 264 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 264).t.Sat ((callAt 264).lift σ) :=
    call_sat_of h 264 (callAt 264) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 264).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 264).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 264).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits265 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 265 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 265).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 265).plugs = [(Xark.R1cs.LC.var (265 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 265).base = bitBase 265 := by rfl
  have glc : (bitGLC 265 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 265).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 265 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 265).t.Sat ((callAt 265).lift σ) :=
    call_sat_of h 265 (callAt 265) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 265).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 265).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 265).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits266 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 266 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 266).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 266).plugs = [(Xark.R1cs.LC.var (266 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 266).base = bitBase 266 := by rfl
  have glc : (bitGLC 266 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 266).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 266 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 266).t.Sat ((callAt 266).lift σ) :=
    call_sat_of h 266 (callAt 266) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 266).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 266).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 266).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits267 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 267 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 267).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 267).plugs = [(Xark.R1cs.LC.var (267 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 267).base = bitBase 267 := by rfl
  have glc : (bitGLC 267 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 267).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 267 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 267).t.Sat ((callAt 267).lift σ) :=
    call_sat_of h 267 (callAt 267) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 267).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 267).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 267).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits268 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 268 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 268).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 268).plugs = [(Xark.R1cs.LC.var (268 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 268).base = bitBase 268 := by rfl
  have glc : (bitGLC 268 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 268).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 268 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 268).t.Sat ((callAt 268).lift σ) :=
    call_sat_of h 268 (callAt 268) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 268).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 268).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 268).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits269 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 269 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 269).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 269).plugs = [(Xark.R1cs.LC.var (269 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 269).base = bitBase 269 := by rfl
  have glc : (bitGLC 269 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 269).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 269 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 269).t.Sat ((callAt 269).lift σ) :=
    call_sat_of h 269 (callAt 269) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 269).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 269).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 269).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits270 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 270 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 270).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 270).plugs = [(Xark.R1cs.LC.var (270 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 270).base = bitBase 270 := by rfl
  have glc : (bitGLC 270 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 270).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 270 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 270).t.Sat ((callAt 270).lift σ) :=
    call_sat_of h 270 (callAt 270) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 270).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 270).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 270).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits271 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 271 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 271).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 271).plugs = [(Xark.R1cs.LC.var (271 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 271).base = bitBase 271 := by rfl
  have glc : (bitGLC 271 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 271).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 271 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 271).t.Sat ((callAt 271).lift σ) :=
    call_sat_of h 271 (callAt 271) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 271).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 271).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 271).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits272 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 272 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 272).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 272).plugs = [(Xark.R1cs.LC.var (272 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 272).base = bitBase 272 := by rfl
  have glc : (bitGLC 272 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 272).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 272 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 272).t.Sat ((callAt 272).lift σ) :=
    call_sat_of h 272 (callAt 272) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 272).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 272).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 272).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits273 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 273 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 273).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 273).plugs = [(Xark.R1cs.LC.var (273 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 273).base = bitBase 273 := by rfl
  have glc : (bitGLC 273 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 273).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 273 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 273).t.Sat ((callAt 273).lift σ) :=
    call_sat_of h 273 (callAt 273) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 273).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 273).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 273).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits274 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 274 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 274).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 274).plugs = [(Xark.R1cs.LC.var (274 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 274).base = bitBase 274 := by rfl
  have glc : (bitGLC 274 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 274).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 274 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 274).t.Sat ((callAt 274).lift σ) :=
    call_sat_of h 274 (callAt 274) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 274).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 274).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 274).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits275 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 275 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 275).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 275).plugs = [(Xark.R1cs.LC.var (275 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 275).base = bitBase 275 := by rfl
  have glc : (bitGLC 275 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 275).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 275 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 275).t.Sat ((callAt 275).lift σ) :=
    call_sat_of h 275 (callAt 275) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 275).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 275).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 275).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits276 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 276 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 276).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 276).plugs = [(Xark.R1cs.LC.var (276 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 276).base = bitBase 276 := by rfl
  have glc : (bitGLC 276 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 276).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 276 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 276).t.Sat ((callAt 276).lift σ) :=
    call_sat_of h 276 (callAt 276) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 276).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 276).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 276).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits277 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 277 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 277).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 277).plugs = [(Xark.R1cs.LC.var (277 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 277).base = bitBase 277 := by rfl
  have glc : (bitGLC 277 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 277).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 277 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 277).t.Sat ((callAt 277).lift σ) :=
    call_sat_of h 277 (callAt 277) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 277).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 277).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 277).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits278 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 278 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 278).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 278).plugs = [(Xark.R1cs.LC.var (278 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 278).base = bitBase 278 := by rfl
  have glc : (bitGLC 278 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 278).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 278 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 278).t.Sat ((callAt 278).lift σ) :=
    call_sat_of h 278 (callAt 278) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 278).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 278).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 278).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits279 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 279 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 279).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 279).plugs = [(Xark.R1cs.LC.var (279 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 279).base = bitBase 279 := by rfl
  have glc : (bitGLC 279 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 279).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 279 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 279).t.Sat ((callAt 279).lift σ) :=
    call_sat_of h 279 (callAt 279) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 279).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 279).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 279).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits280 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 280 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 280).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 280).plugs = [(Xark.R1cs.LC.var (280 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 280).base = bitBase 280 := by rfl
  have glc : (bitGLC 280 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 280).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 280 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 280).t.Sat ((callAt 280).lift σ) :=
    call_sat_of h 280 (callAt 280) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 280).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 280).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 280).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits281 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 281 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 281).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 281).plugs = [(Xark.R1cs.LC.var (281 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 281).base = bitBase 281 := by rfl
  have glc : (bitGLC 281 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 281).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 281 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 281).t.Sat ((callAt 281).lift σ) :=
    call_sat_of h 281 (callAt 281) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 281).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 281).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 281).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits282 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 282 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 282).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 282).plugs = [(Xark.R1cs.LC.var (282 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 282).base = bitBase 282 := by rfl
  have glc : (bitGLC 282 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 282).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 282 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 282).t.Sat ((callAt 282).lift σ) :=
    call_sat_of h 282 (callAt 282) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 282).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 282).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 282).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits283 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 283 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 283).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 283).plugs = [(Xark.R1cs.LC.var (283 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 283).base = bitBase 283 := by rfl
  have glc : (bitGLC 283 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 283).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 283 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 283).t.Sat ((callAt 283).lift σ) :=
    call_sat_of h 283 (callAt 283) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 283).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 283).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 283).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits284 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 284 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 284).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 284).plugs = [(Xark.R1cs.LC.var (284 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 284).base = bitBase 284 := by rfl
  have glc : (bitGLC 284 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 284).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 284 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 284).t.Sat ((callAt 284).lift σ) :=
    call_sat_of h 284 (callAt 284) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 284).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 284).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 284).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits285 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 285 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 285).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 285).plugs = [(Xark.R1cs.LC.var (285 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 285).base = bitBase 285 := by rfl
  have glc : (bitGLC 285 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 285).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 285 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 285).t.Sat ((callAt 285).lift σ) :=
    call_sat_of h 285 (callAt 285) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 285).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 285).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 285).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits286 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 286 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 286).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 286).plugs = [(Xark.R1cs.LC.var (286 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 286).base = bitBase 286 := by rfl
  have glc : (bitGLC 286 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 286).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 286 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 286).t.Sat ((callAt 286).lift σ) :=
    call_sat_of h 286 (callAt 286) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 286).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 286).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 286).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits287 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 287 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 287).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 287).plugs = [(Xark.R1cs.LC.var (287 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 287).base = bitBase 287 := by rfl
  have glc : (bitGLC 287 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 287).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 287 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 287).t.Sat ((callAt 287).lift σ) :=
    call_sat_of h 287 (callAt 287) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 287).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 287).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 287).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits288 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 288 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 288).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 288).plugs = [(Xark.R1cs.LC.var (288 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 288).base = bitBase 288 := by rfl
  have glc : (bitGLC 288 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 288).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 288 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 288).t.Sat ((callAt 288).lift σ) :=
    call_sat_of h 288 (callAt 288) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 288).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 288).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 288).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits289 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 289 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 289).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 289).plugs = [(Xark.R1cs.LC.var (289 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 289).base = bitBase 289 := by rfl
  have glc : (bitGLC 289 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 289).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 289 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 289).t.Sat ((callAt 289).lift σ) :=
    call_sat_of h 289 (callAt 289) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 289).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 289).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 289).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits290 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 290 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 290).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 290).plugs = [(Xark.R1cs.LC.var (290 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 290).base = bitBase 290 := by rfl
  have glc : (bitGLC 290 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 290).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 290 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 290).t.Sat ((callAt 290).lift σ) :=
    call_sat_of h 290 (callAt 290) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 290).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 290).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 290).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits291 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 291 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 291).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 291).plugs = [(Xark.R1cs.LC.var (291 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 291).base = bitBase 291 := by rfl
  have glc : (bitGLC 291 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 291).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 291 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 291).t.Sat ((callAt 291).lift σ) :=
    call_sat_of h 291 (callAt 291) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 291).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 291).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 291).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits292 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 292 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 292).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 292).plugs = [(Xark.R1cs.LC.var (292 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 292).base = bitBase 292 := by rfl
  have glc : (bitGLC 292 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 292).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 292 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 292).t.Sat ((callAt 292).lift σ) :=
    call_sat_of h 292 (callAt 292) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 292).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 292).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 292).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits293 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 293 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 293).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 293).plugs = [(Xark.R1cs.LC.var (293 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 293).base = bitBase 293 := by rfl
  have glc : (bitGLC 293 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 293).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 293 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 293).t.Sat ((callAt 293).lift σ) :=
    call_sat_of h 293 (callAt 293) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 293).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 293).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 293).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits294 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 294 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 294).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 294).plugs = [(Xark.R1cs.LC.var (294 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 294).base = bitBase 294 := by rfl
  have glc : (bitGLC 294 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 294).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 294 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 294).t.Sat ((callAt 294).lift σ) :=
    call_sat_of h 294 (callAt 294) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 294).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 294).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 294).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits295 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 295 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 295).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 295).plugs = [(Xark.R1cs.LC.var (295 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 295).base = bitBase 295 := by rfl
  have glc : (bitGLC 295 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 295).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 295 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 295).t.Sat ((callAt 295).lift σ) :=
    call_sat_of h 295 (callAt 295) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 295).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 295).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 295).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits296 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 296 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 296).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 296).plugs = [(Xark.R1cs.LC.var (296 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 296).base = bitBase 296 := by rfl
  have glc : (bitGLC 296 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 296).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 296 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 296).t.Sat ((callAt 296).lift σ) :=
    call_sat_of h 296 (callAt 296) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 296).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 296).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 296).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits297 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 297 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 297).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 297).plugs = [(Xark.R1cs.LC.var (297 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 297).base = bitBase 297 := by rfl
  have glc : (bitGLC 297 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 297).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 297 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 297).t.Sat ((callAt 297).lift σ) :=
    call_sat_of h 297 (callAt 297) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 297).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 297).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 297).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits298 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 298 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 298).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 298).plugs = [(Xark.R1cs.LC.var (298 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 298).base = bitBase 298 := by rfl
  have glc : (bitGLC 298 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 298).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 298 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 298).t.Sat ((callAt 298).lift σ) :=
    call_sat_of h 298 (callAt 298) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 298).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 298).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 298).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits299 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 299 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 299).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 299).plugs = [(Xark.R1cs.LC.var (299 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 299).base = bitBase 299 := by rfl
  have glc : (bitGLC 299 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 299).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 299 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 299).t.Sat ((callAt 299).lift σ) :=
    call_sat_of h 299 (callAt 299) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 299).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 299).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 299).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits300 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 300 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 300).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 300).plugs = [(Xark.R1cs.LC.var (300 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 300).base = bitBase 300 := by rfl
  have glc : (bitGLC 300 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 300).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 300 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 300).t.Sat ((callAt 300).lift σ) :=
    call_sat_of h 300 (callAt 300) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 300).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 300).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 300).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits301 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 301 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 301).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 301).plugs = [(Xark.R1cs.LC.var (301 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 301).base = bitBase 301 := by rfl
  have glc : (bitGLC 301 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 301).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 301 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 301).t.Sat ((callAt 301).lift σ) :=
    call_sat_of h 301 (callAt 301) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 301).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 301).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 301).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits302 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 302 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 302).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 302).plugs = [(Xark.R1cs.LC.var (302 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 302).base = bitBase 302 := by rfl
  have glc : (bitGLC 302 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 302).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 302 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 302).t.Sat ((callAt 302).lift σ) :=
    call_sat_of h 302 (callAt 302) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 302).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 302).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 302).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits303 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 303 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 303).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 303).plugs = [(Xark.R1cs.LC.var (303 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 303).base = bitBase 303 := by rfl
  have glc : (bitGLC 303 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 303).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 303 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 303).t.Sat ((callAt 303).lift σ) :=
    call_sat_of h 303 (callAt 303) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 303).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 303).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 303).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits304 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 304 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 304).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 304).plugs = [(Xark.R1cs.LC.var (304 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 304).base = bitBase 304 := by rfl
  have glc : (bitGLC 304 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 304).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 304 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 304).t.Sat ((callAt 304).lift σ) :=
    call_sat_of h 304 (callAt 304) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 304).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 304).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 304).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits305 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 305 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 305).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 305).plugs = [(Xark.R1cs.LC.var (305 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 305).base = bitBase 305 := by rfl
  have glc : (bitGLC 305 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 305).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 305 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 305).t.Sat ((callAt 305).lift σ) :=
    call_sat_of h 305 (callAt 305) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 305).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 305).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 305).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits306 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 306 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 306).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 306).plugs = [(Xark.R1cs.LC.var (306 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 306).base = bitBase 306 := by rfl
  have glc : (bitGLC 306 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 306).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 306 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 306).t.Sat ((callAt 306).lift σ) :=
    call_sat_of h 306 (callAt 306) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 306).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 306).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 306).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits307 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 307 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 307).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 307).plugs = [(Xark.R1cs.LC.var (307 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 307).base = bitBase 307 := by rfl
  have glc : (bitGLC 307 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 307).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 307 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 307).t.Sat ((callAt 307).lift σ) :=
    call_sat_of h 307 (callAt 307) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 307).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 307).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 307).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits308 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 308 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 308).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 308).plugs = [(Xark.R1cs.LC.var (308 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 308).base = bitBase 308 := by rfl
  have glc : (bitGLC 308 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 308).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 308 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 308).t.Sat ((callAt 308).lift σ) :=
    call_sat_of h 308 (callAt 308) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 308).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 308).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 308).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits309 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 309 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 309).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 309).plugs = [(Xark.R1cs.LC.var (309 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 309).base = bitBase 309 := by rfl
  have glc : (bitGLC 309 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 309).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 309 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 309).t.Sat ((callAt 309).lift σ) :=
    call_sat_of h 309 (callAt 309) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 309).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 309).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 309).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits310 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 310 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 310).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 310).plugs = [(Xark.R1cs.LC.var (310 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 310).base = bitBase 310 := by rfl
  have glc : (bitGLC 310 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 310).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 310 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 310).t.Sat ((callAt 310).lift σ) :=
    call_sat_of h 310 (callAt 310) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 310).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 310).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 310).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits311 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 311 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 311).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 311).plugs = [(Xark.R1cs.LC.var (311 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 311).base = bitBase 311 := by rfl
  have glc : (bitGLC 311 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 311).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 311 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 311).t.Sat ((callAt 311).lift σ) :=
    call_sat_of h 311 (callAt 311) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 311).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 311).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 311).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits312 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 312 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 312).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 312).plugs = [(Xark.R1cs.LC.var (312 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 312).base = bitBase 312 := by rfl
  have glc : (bitGLC 312 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 312).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 312 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 312).t.Sat ((callAt 312).lift σ) :=
    call_sat_of h 312 (callAt 312) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 312).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 312).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 312).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits313 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 313 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 313).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 313).plugs = [(Xark.R1cs.LC.var (313 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 313).base = bitBase 313 := by rfl
  have glc : (bitGLC 313 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 313).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 313 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 313).t.Sat ((callAt 313).lift σ) :=
    call_sat_of h 313 (callAt 313) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 313).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 313).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 313).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits314 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 314 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 314).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 314).plugs = [(Xark.R1cs.LC.var (314 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 314).base = bitBase 314 := by rfl
  have glc : (bitGLC 314 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 314).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 314 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 314).t.Sat ((callAt 314).lift σ) :=
    call_sat_of h 314 (callAt 314) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 314).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 314).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 314).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits315 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 315 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 315).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 315).plugs = [(Xark.R1cs.LC.var (315 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 315).base = bitBase 315 := by rfl
  have glc : (bitGLC 315 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 315).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 315 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 315).t.Sat ((callAt 315).lift σ) :=
    call_sat_of h 315 (callAt 315) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 315).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 315).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 315).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits316 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 316 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 316).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 316).plugs = [(Xark.R1cs.LC.var (316 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 316).base = bitBase 316 := by rfl
  have glc : (bitGLC 316 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 316).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 316 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 316).t.Sat ((callAt 316).lift σ) :=
    call_sat_of h 316 (callAt 316) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 316).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 316).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 316).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits317 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 317 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 317).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 317).plugs = [(Xark.R1cs.LC.var (317 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 317).base = bitBase 317 := by rfl
  have glc : (bitGLC 317 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 317).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 317 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 317).t.Sat ((callAt 317).lift σ) :=
    call_sat_of h 317 (callAt 317) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 317).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 317).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 317).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits318 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 318 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 318).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 318).plugs = [(Xark.R1cs.LC.var (318 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 318).base = bitBase 318 := by rfl
  have glc : (bitGLC 318 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 318).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 318 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 318).t.Sat ((callAt 318).lift σ) :=
    call_sat_of h 318 (callAt 318) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 318).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 318).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 318).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits319 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 319 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 319).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 319).plugs = [(Xark.R1cs.LC.var (319 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 319).base = bitBase 319 := by rfl
  have glc : (bitGLC 319 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 319).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 319 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 319).t.Sat ((callAt 319).lift σ) :=
    call_sat_of h 319 (callAt 319) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 319).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 319).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 319).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits320 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 320 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 320).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 320).plugs = [(Xark.R1cs.LC.var (320 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 320).base = bitBase 320 := by rfl
  have glc : (bitGLC 320 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 320).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 320 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 320).t.Sat ((callAt 320).lift σ) :=
    call_sat_of h 320 (callAt 320) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 320).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 320).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 320).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits321 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 321 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 321).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 321).plugs = [(Xark.R1cs.LC.var (321 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 321).base = bitBase 321 := by rfl
  have glc : (bitGLC 321 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 321).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 321 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 321).t.Sat ((callAt 321).lift σ) :=
    call_sat_of h 321 (callAt 321) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 321).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 321).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 321).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits322 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 322 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 322).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 322).plugs = [(Xark.R1cs.LC.var (322 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 322).base = bitBase 322 := by rfl
  have glc : (bitGLC 322 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 322).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 322 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 322).t.Sat ((callAt 322).lift σ) :=
    call_sat_of h 322 (callAt 322) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 322).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 322).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 322).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits323 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 323 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 323).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 323).plugs = [(Xark.R1cs.LC.var (323 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 323).base = bitBase 323 := by rfl
  have glc : (bitGLC 323 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 323).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 323 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 323).t.Sat ((callAt 323).lift σ) :=
    call_sat_of h 323 (callAt 323) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 323).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 323).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 323).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits324 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 324 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 324).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 324).plugs = [(Xark.R1cs.LC.var (324 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 324).base = bitBase 324 := by rfl
  have glc : (bitGLC 324 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 324).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 324 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 324).t.Sat ((callAt 324).lift σ) :=
    call_sat_of h 324 (callAt 324) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 324).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 324).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 324).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits325 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 325 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 325).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 325).plugs = [(Xark.R1cs.LC.var (325 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 325).base = bitBase 325 := by rfl
  have glc : (bitGLC 325 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 325).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 325 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 325).t.Sat ((callAt 325).lift σ) :=
    call_sat_of h 325 (callAt 325) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 325).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 325).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 325).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits326 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 326 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 326).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 326).plugs = [(Xark.R1cs.LC.var (326 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 326).base = bitBase 326 := by rfl
  have glc : (bitGLC 326 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 326).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 326 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 326).t.Sat ((callAt 326).lift σ) :=
    call_sat_of h 326 (callAt 326) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 326).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 326).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 326).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits327 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 327 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 327).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 327).plugs = [(Xark.R1cs.LC.var (327 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 327).base = bitBase 327 := by rfl
  have glc : (bitGLC 327 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 327).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 327 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 327).t.Sat ((callAt 327).lift σ) :=
    call_sat_of h 327 (callAt 327) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 327).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 327).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 327).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits328 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 328 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 328).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 328).plugs = [(Xark.R1cs.LC.var (328 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 328).base = bitBase 328 := by rfl
  have glc : (bitGLC 328 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 328).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 328 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 328).t.Sat ((callAt 328).lift σ) :=
    call_sat_of h 328 (callAt 328) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 328).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 328).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 328).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits329 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 329 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 329).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 329).plugs = [(Xark.R1cs.LC.var (329 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 329).base = bitBase 329 := by rfl
  have glc : (bitGLC 329 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 329).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 329 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 329).t.Sat ((callAt 329).lift σ) :=
    call_sat_of h 329 (callAt 329) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 329).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 329).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 329).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits330 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 330 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 330).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 330).plugs = [(Xark.R1cs.LC.var (330 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 330).base = bitBase 330 := by rfl
  have glc : (bitGLC 330 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 330).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 330 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 330).t.Sat ((callAt 330).lift σ) :=
    call_sat_of h 330 (callAt 330) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 330).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 330).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 330).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits331 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 331 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 331).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 331).plugs = [(Xark.R1cs.LC.var (331 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 331).base = bitBase 331 := by rfl
  have glc : (bitGLC 331 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 331).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 331 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 331).t.Sat ((callAt 331).lift σ) :=
    call_sat_of h 331 (callAt 331) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 331).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 331).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 331).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits332 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 332 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 332).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 332).plugs = [(Xark.R1cs.LC.var (332 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 332).base = bitBase 332 := by rfl
  have glc : (bitGLC 332 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 332).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 332 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 332).t.Sat ((callAt 332).lift σ) :=
    call_sat_of h 332 (callAt 332) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 332).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 332).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 332).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits333 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 333 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 333).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 333).plugs = [(Xark.R1cs.LC.var (333 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 333).base = bitBase 333 := by rfl
  have glc : (bitGLC 333 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 333).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 333 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 333).t.Sat ((callAt 333).lift σ) :=
    call_sat_of h 333 (callAt 333) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 333).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 333).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 333).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits334 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 334 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 334).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 334).plugs = [(Xark.R1cs.LC.var (334 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 334).base = bitBase 334 := by rfl
  have glc : (bitGLC 334 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 334).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 334 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 334).t.Sat ((callAt 334).lift σ) :=
    call_sat_of h 334 (callAt 334) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 334).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 334).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 334).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits335 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 335 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 335).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 335).plugs = [(Xark.R1cs.LC.var (335 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 335).base = bitBase 335 := by rfl
  have glc : (bitGLC 335 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 335).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 335 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 335).t.Sat ((callAt 335).lift σ) :=
    call_sat_of h 335 (callAt 335) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 335).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 335).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 335).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits336 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 336 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 336).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 336).plugs = [(Xark.R1cs.LC.var (336 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 336).base = bitBase 336 := by rfl
  have glc : (bitGLC 336 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 336).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 336 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 336).t.Sat ((callAt 336).lift σ) :=
    call_sat_of h 336 (callAt 336) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 336).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 336).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 336).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits337 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 337 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 337).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 337).plugs = [(Xark.R1cs.LC.var (337 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 337).base = bitBase 337 := by rfl
  have glc : (bitGLC 337 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 337).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 337 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 337).t.Sat ((callAt 337).lift σ) :=
    call_sat_of h 337 (callAt 337) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 337).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 337).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 337).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits338 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 338 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 338).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 338).plugs = [(Xark.R1cs.LC.var (338 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 338).base = bitBase 338 := by rfl
  have glc : (bitGLC 338 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 338).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 338 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 338).t.Sat ((callAt 338).lift σ) :=
    call_sat_of h 338 (callAt 338) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 338).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 338).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 338).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits339 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 339 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 339).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 339).plugs = [(Xark.R1cs.LC.var (339 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 339).base = bitBase 339 := by rfl
  have glc : (bitGLC 339 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 339).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 339 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 339).t.Sat ((callAt 339).lift σ) :=
    call_sat_of h 339 (callAt 339) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 339).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 339).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 339).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits340 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 340 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 340).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 340).plugs = [(Xark.R1cs.LC.var (340 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 340).base = bitBase 340 := by rfl
  have glc : (bitGLC 340 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 340).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 340 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 340).t.Sat ((callAt 340).lift σ) :=
    call_sat_of h 340 (callAt 340) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 340).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 340).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 340).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits341 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 341 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 341).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 341).plugs = [(Xark.R1cs.LC.var (341 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 341).base = bitBase 341 := by rfl
  have glc : (bitGLC 341 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 341).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 341 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 341).t.Sat ((callAt 341).lift σ) :=
    call_sat_of h 341 (callAt 341) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 341).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 341).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 341).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits342 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 342 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 342).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 342).plugs = [(Xark.R1cs.LC.var (342 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 342).base = bitBase 342 := by rfl
  have glc : (bitGLC 342 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 342).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 342 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 342).t.Sat ((callAt 342).lift σ) :=
    call_sat_of h 342 (callAt 342) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 342).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 342).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 342).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits343 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 343 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 343).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 343).plugs = [(Xark.R1cs.LC.var (343 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 343).base = bitBase 343 := by rfl
  have glc : (bitGLC 343 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 343).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 343 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 343).t.Sat ((callAt 343).lift σ) :=
    call_sat_of h 343 (callAt 343) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 343).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 343).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 343).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits344 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 344 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 344).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 344).plugs = [(Xark.R1cs.LC.var (344 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 344).base = bitBase 344 := by rfl
  have glc : (bitGLC 344 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 344).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 344 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 344).t.Sat ((callAt 344).lift σ) :=
    call_sat_of h 344 (callAt 344) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 344).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 344).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 344).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits345 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 345 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 345).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 345).plugs = [(Xark.R1cs.LC.var (345 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 345).base = bitBase 345 := by rfl
  have glc : (bitGLC 345 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 345).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 345 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 345).t.Sat ((callAt 345).lift σ) :=
    call_sat_of h 345 (callAt 345) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 345).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 345).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 345).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits346 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 346 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 346).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 346).plugs = [(Xark.R1cs.LC.var (346 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 346).base = bitBase 346 := by rfl
  have glc : (bitGLC 346 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 346).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 346 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 346).t.Sat ((callAt 346).lift σ) :=
    call_sat_of h 346 (callAt 346) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 346).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 346).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 346).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits347 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 347 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 347).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 347).plugs = [(Xark.R1cs.LC.var (347 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 347).base = bitBase 347 := by rfl
  have glc : (bitGLC 347 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 347).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 347 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 347).t.Sat ((callAt 347).lift σ) :=
    call_sat_of h 347 (callAt 347) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 347).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 347).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 347).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits348 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 348 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 348).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 348).plugs = [(Xark.R1cs.LC.var (348 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 348).base = bitBase 348 := by rfl
  have glc : (bitGLC 348 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 348).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 348 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 348).t.Sat ((callAt 348).lift σ) :=
    call_sat_of h 348 (callAt 348) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 348).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 348).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 348).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits349 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 349 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 349).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 349).plugs = [(Xark.R1cs.LC.var (349 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 349).base = bitBase 349 := by rfl
  have glc : (bitGLC 349 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 349).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 349 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 349).t.Sat ((callAt 349).lift σ) :=
    call_sat_of h 349 (callAt 349) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 349).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 349).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 349).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits350 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 350 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 350).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 350).plugs = [(Xark.R1cs.LC.var (350 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 350).base = bitBase 350 := by rfl
  have glc : (bitGLC 350 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 350).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 350 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 350).t.Sat ((callAt 350).lift σ) :=
    call_sat_of h 350 (callAt 350) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 350).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 350).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 350).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits351 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 351 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 351).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 351).plugs = [(Xark.R1cs.LC.var (351 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 351).base = bitBase 351 := by rfl
  have glc : (bitGLC 351 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 351).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 351 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 351).t.Sat ((callAt 351).lift σ) :=
    call_sat_of h 351 (callAt 351) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 351).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 351).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 351).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits352 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 352 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 352).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 352).plugs = [(Xark.R1cs.LC.var (352 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 352).base = bitBase 352 := by rfl
  have glc : (bitGLC 352 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 352).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 352 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 352).t.Sat ((callAt 352).lift σ) :=
    call_sat_of h 352 (callAt 352) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 352).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 352).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 352).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits353 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 353 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 353).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 353).plugs = [(Xark.R1cs.LC.var (353 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 353).base = bitBase 353 := by rfl
  have glc : (bitGLC 353 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 353).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 353 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 353).t.Sat ((callAt 353).lift σ) :=
    call_sat_of h 353 (callAt 353) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 353).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 353).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 353).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits354 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 354 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 354).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 354).plugs = [(Xark.R1cs.LC.var (354 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 354).base = bitBase 354 := by rfl
  have glc : (bitGLC 354 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 354).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 354 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 354).t.Sat ((callAt 354).lift σ) :=
    call_sat_of h 354 (callAt 354) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 354).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 354).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 354).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits355 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 355 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 355).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 355).plugs = [(Xark.R1cs.LC.var (355 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 355).base = bitBase 355 := by rfl
  have glc : (bitGLC 355 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 355).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 355 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 355).t.Sat ((callAt 355).lift σ) :=
    call_sat_of h 355 (callAt 355) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 355).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 355).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 355).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits356 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 356 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 356).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 356).plugs = [(Xark.R1cs.LC.var (356 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 356).base = bitBase 356 := by rfl
  have glc : (bitGLC 356 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 356).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 356 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 356).t.Sat ((callAt 356).lift σ) :=
    call_sat_of h 356 (callAt 356) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 356).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 356).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 356).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits357 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 357 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 357).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 357).plugs = [(Xark.R1cs.LC.var (357 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 357).base = bitBase 357 := by rfl
  have glc : (bitGLC 357 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 357).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 357 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 357).t.Sat ((callAt 357).lift σ) :=
    call_sat_of h 357 (callAt 357) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 357).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 357).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 357).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits358 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 358 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 358).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 358).plugs = [(Xark.R1cs.LC.var (358 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 358).base = bitBase 358 := by rfl
  have glc : (bitGLC 358 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 358).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 358 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 358).t.Sat ((callAt 358).lift σ) :=
    call_sat_of h 358 (callAt 358) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 358).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 358).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 358).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits359 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 359 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 359).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 359).plugs = [(Xark.R1cs.LC.var (359 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 359).base = bitBase 359 := by rfl
  have glc : (bitGLC 359 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 359).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 359 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 359).t.Sat ((callAt 359).lift σ) :=
    call_sat_of h 359 (callAt 359) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 359).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 359).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 359).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits360 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 360 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 360).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 360).plugs = [(Xark.R1cs.LC.var (360 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 360).base = bitBase 360 := by rfl
  have glc : (bitGLC 360 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 360).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 360 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 360).t.Sat ((callAt 360).lift σ) :=
    call_sat_of h 360 (callAt 360) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 360).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 360).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 360).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits361 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 361 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 361).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 361).plugs = [(Xark.R1cs.LC.var (361 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 361).base = bitBase 361 := by rfl
  have glc : (bitGLC 361 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 361).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 361 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 361).t.Sat ((callAt 361).lift σ) :=
    call_sat_of h 361 (callAt 361) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 361).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 361).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 361).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits362 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 362 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 362).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 362).plugs = [(Xark.R1cs.LC.var (362 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 362).base = bitBase 362 := by rfl
  have glc : (bitGLC 362 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 362).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 362 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 362).t.Sat ((callAt 362).lift σ) :=
    call_sat_of h 362 (callAt 362) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 362).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 362).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 362).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits363 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 363 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 363).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 363).plugs = [(Xark.R1cs.LC.var (363 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 363).base = bitBase 363 := by rfl
  have glc : (bitGLC 363 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 363).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 363 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 363).t.Sat ((callAt 363).lift σ) :=
    call_sat_of h 363 (callAt 363) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 363).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 363).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 363).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits364 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 364 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 364).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 364).plugs = [(Xark.R1cs.LC.var (364 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 364).base = bitBase 364 := by rfl
  have glc : (bitGLC 364 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 364).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 364 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 364).t.Sat ((callAt 364).lift σ) :=
    call_sat_of h 364 (callAt 364) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 364).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 364).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 364).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits365 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 365 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 365).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 365).plugs = [(Xark.R1cs.LC.var (365 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 365).base = bitBase 365 := by rfl
  have glc : (bitGLC 365 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 365).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 365 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 365).t.Sat ((callAt 365).lift σ) :=
    call_sat_of h 365 (callAt 365) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 365).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 365).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 365).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits366 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 366 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 366).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 366).plugs = [(Xark.R1cs.LC.var (366 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 366).base = bitBase 366 := by rfl
  have glc : (bitGLC 366 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 366).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 366 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 366).t.Sat ((callAt 366).lift σ) :=
    call_sat_of h 366 (callAt 366) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 366).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 366).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 366).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits367 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 367 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 367).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 367).plugs = [(Xark.R1cs.LC.var (367 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 367).base = bitBase 367 := by rfl
  have glc : (bitGLC 367 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 367).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 367 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 367).t.Sat ((callAt 367).lift σ) :=
    call_sat_of h 367 (callAt 367) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 367).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 367).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 367).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits368 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 368 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 368).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 368).plugs = [(Xark.R1cs.LC.var (368 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 368).base = bitBase 368 := by rfl
  have glc : (bitGLC 368 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 368).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 368 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 368).t.Sat ((callAt 368).lift σ) :=
    call_sat_of h 368 (callAt 368) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 368).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 368).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 368).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits369 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 369 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 369).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 369).plugs = [(Xark.R1cs.LC.var (369 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 369).base = bitBase 369 := by rfl
  have glc : (bitGLC 369 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 369).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 369 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 369).t.Sat ((callAt 369).lift σ) :=
    call_sat_of h 369 (callAt 369) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 369).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 369).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 369).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits370 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 370 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 370).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 370).plugs = [(Xark.R1cs.LC.var (370 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 370).base = bitBase 370 := by rfl
  have glc : (bitGLC 370 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 370).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 370 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 370).t.Sat ((callAt 370).lift σ) :=
    call_sat_of h 370 (callAt 370) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 370).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 370).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 370).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits371 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 371 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 371).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 371).plugs = [(Xark.R1cs.LC.var (371 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 371).base = bitBase 371 := by rfl
  have glc : (bitGLC 371 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 371).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 371 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 371).t.Sat ((callAt 371).lift σ) :=
    call_sat_of h 371 (callAt 371) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 371).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 371).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 371).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits372 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 372 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 372).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 372).plugs = [(Xark.R1cs.LC.var (372 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 372).base = bitBase 372 := by rfl
  have glc : (bitGLC 372 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 372).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 372 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 372).t.Sat ((callAt 372).lift σ) :=
    call_sat_of h 372 (callAt 372) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 372).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 372).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 372).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits373 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 373 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 373).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 373).plugs = [(Xark.R1cs.LC.var (373 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 373).base = bitBase 373 := by rfl
  have glc : (bitGLC 373 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 373).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 373 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 373).t.Sat ((callAt 373).lift σ) :=
    call_sat_of h 373 (callAt 373) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 373).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 373).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 373).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits374 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 374 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 374).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 374).plugs = [(Xark.R1cs.LC.var (374 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 374).base = bitBase 374 := by rfl
  have glc : (bitGLC 374 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 374).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 374 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 374).t.Sat ((callAt 374).lift σ) :=
    call_sat_of h 374 (callAt 374) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 374).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 374).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 374).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits375 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 375 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 375).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 375).plugs = [(Xark.R1cs.LC.var (375 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 375).base = bitBase 375 := by rfl
  have glc : (bitGLC 375 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 375).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 375 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 375).t.Sat ((callAt 375).lift σ) :=
    call_sat_of h 375 (callAt 375) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 375).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 375).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 375).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits376 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 376 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 376).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 376).plugs = [(Xark.R1cs.LC.var (376 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 376).base = bitBase 376 := by rfl
  have glc : (bitGLC 376 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 376).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 376 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 376).t.Sat ((callAt 376).lift σ) :=
    call_sat_of h 376 (callAt 376) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 376).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 376).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 376).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits377 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 377 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 377).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 377).plugs = [(Xark.R1cs.LC.var (377 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 377).base = bitBase 377 := by rfl
  have glc : (bitGLC 377 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 377).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 377 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 377).t.Sat ((callAt 377).lift σ) :=
    call_sat_of h 377 (callAt 377) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 377).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 377).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 377).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits378 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 378 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 378).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 378).plugs = [(Xark.R1cs.LC.var (378 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 378).base = bitBase 378 := by rfl
  have glc : (bitGLC 378 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 378).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 378 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 378).t.Sat ((callAt 378).lift σ) :=
    call_sat_of h 378 (callAt 378) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 378).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 378).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 378).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits379 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 379 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 379).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 379).plugs = [(Xark.R1cs.LC.var (379 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 379).base = bitBase 379 := by rfl
  have glc : (bitGLC 379 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 379).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 379 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 379).t.Sat ((callAt 379).lift σ) :=
    call_sat_of h 379 (callAt 379) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 379).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 379).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 379).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits380 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 380 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 380).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 380).plugs = [(Xark.R1cs.LC.var (380 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 380).base = bitBase 380 := by rfl
  have glc : (bitGLC 380 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 380).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 380 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 380).t.Sat ((callAt 380).lift σ) :=
    call_sat_of h 380 (callAt 380) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 380).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 380).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 380).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits381 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 381 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 381).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 381).plugs = [(Xark.R1cs.LC.var (381 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 381).base = bitBase 381 := by rfl
  have glc : (bitGLC 381 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 381).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 381 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 381).t.Sat ((callAt 381).lift σ) :=
    call_sat_of h 381 (callAt 381) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 381).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 381).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 381).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits382 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 382 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 382).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 382).plugs = [(Xark.R1cs.LC.var (382 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 382).base = bitBase 382 := by rfl
  have glc : (bitGLC 382 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 382).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 382 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 382).t.Sat ((callAt 382).lift σ) :=
    call_sat_of h 382 (callAt 382) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 382).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 382).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 382).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits383 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 383 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 383).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 383).plugs = [(Xark.R1cs.LC.var (383 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 383).base = bitBase 383 := by rfl
  have glc : (bitGLC 383 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 383).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 383 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 383).t.Sat ((callAt 383).lift σ) :=
    call_sat_of h 383 (callAt 383) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 383).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 383).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 383).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits384 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 384 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 384).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 384).plugs = [(Xark.R1cs.LC.var (384 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 384).base = bitBase 384 := by rfl
  have glc : (bitGLC 384 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 384).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 384 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 384).t.Sat ((callAt 384).lift σ) :=
    call_sat_of h 384 (callAt 384) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 384).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 384).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 384).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits385 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 385 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 385).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 385).plugs = [(Xark.R1cs.LC.var (385 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 385).base = bitBase 385 := by rfl
  have glc : (bitGLC 385 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 385).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 385 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 385).t.Sat ((callAt 385).lift σ) :=
    call_sat_of h 385 (callAt 385) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 385).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 385).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 385).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits386 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 386 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 386).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 386).plugs = [(Xark.R1cs.LC.var (386 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 386).base = bitBase 386 := by rfl
  have glc : (bitGLC 386 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 386).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 386 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 386).t.Sat ((callAt 386).lift σ) :=
    call_sat_of h 386 (callAt 386) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 386).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 386).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 386).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits387 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 387 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 387).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 387).plugs = [(Xark.R1cs.LC.var (387 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 387).base = bitBase 387 := by rfl
  have glc : (bitGLC 387 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 387).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 387 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 387).t.Sat ((callAt 387).lift σ) :=
    call_sat_of h 387 (callAt 387) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 387).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 387).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 387).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits388 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 388 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 388).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 388).plugs = [(Xark.R1cs.LC.var (388 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 388).base = bitBase 388 := by rfl
  have glc : (bitGLC 388 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 388).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 388 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 388).t.Sat ((callAt 388).lift σ) :=
    call_sat_of h 388 (callAt 388) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 388).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 388).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 388).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits389 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 389 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 389).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 389).plugs = [(Xark.R1cs.LC.var (389 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 389).base = bitBase 389 := by rfl
  have glc : (bitGLC 389 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 389).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 389 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 389).t.Sat ((callAt 389).lift σ) :=
    call_sat_of h 389 (callAt 389) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 389).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 389).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 389).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits390 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 390 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 390).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 390).plugs = [(Xark.R1cs.LC.var (390 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 390).base = bitBase 390 := by rfl
  have glc : (bitGLC 390 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 390).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 390 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 390).t.Sat ((callAt 390).lift σ) :=
    call_sat_of h 390 (callAt 390) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 390).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 390).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 390).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits391 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 391 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 391).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 391).plugs = [(Xark.R1cs.LC.var (391 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 391).base = bitBase 391 := by rfl
  have glc : (bitGLC 391 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 391).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 391 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 391).t.Sat ((callAt 391).lift σ) :=
    call_sat_of h 391 (callAt 391) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 391).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 391).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 391).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits392 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 392 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 392).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 392).plugs = [(Xark.R1cs.LC.var (392 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 392).base = bitBase 392 := by rfl
  have glc : (bitGLC 392 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 392).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 392 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 392).t.Sat ((callAt 392).lift σ) :=
    call_sat_of h 392 (callAt 392) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 392).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 392).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 392).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits393 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 393 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 393).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 393).plugs = [(Xark.R1cs.LC.var (393 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 393).base = bitBase 393 := by rfl
  have glc : (bitGLC 393 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 393).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 393 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 393).t.Sat ((callAt 393).lift σ) :=
    call_sat_of h 393 (callAt 393) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 393).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 393).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 393).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits394 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 394 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 394).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 394).plugs = [(Xark.R1cs.LC.var (394 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 394).base = bitBase 394 := by rfl
  have glc : (bitGLC 394 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 394).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 394 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 394).t.Sat ((callAt 394).lift σ) :=
    call_sat_of h 394 (callAt 394) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 394).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 394).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 394).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits395 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 395 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 395).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 395).plugs = [(Xark.R1cs.LC.var (395 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 395).base = bitBase 395 := by rfl
  have glc : (bitGLC 395 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 395).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 395 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 395).t.Sat ((callAt 395).lift σ) :=
    call_sat_of h 395 (callAt 395) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 395).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 395).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 395).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits396 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 396 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 396).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 396).plugs = [(Xark.R1cs.LC.var (396 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 396).base = bitBase 396 := by rfl
  have glc : (bitGLC 396 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 396).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 396 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 396).t.Sat ((callAt 396).lift σ) :=
    call_sat_of h 396 (callAt 396) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 396).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 396).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 396).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits397 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 397 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 397).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 397).plugs = [(Xark.R1cs.LC.var (397 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 397).base = bitBase 397 := by rfl
  have glc : (bitGLC 397 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 397).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 397 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 397).t.Sat ((callAt 397).lift σ) :=
    call_sat_of h 397 (callAt 397) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 397).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 397).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 397).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits398 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 398 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 398).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 398).plugs = [(Xark.R1cs.LC.var (398 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 398).base = bitBase 398 := by rfl
  have glc : (bitGLC 398 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 398).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 398 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 398).t.Sat ((callAt 398).lift σ) :=
    call_sat_of h 398 (callAt 398) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 398).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 398).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 398).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits399 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 399 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 399).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 399).plugs = [(Xark.R1cs.LC.var (399 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 399).base = bitBase 399 := by rfl
  have glc : (bitGLC 399 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 399).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 399 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 399).t.Sat ((callAt 399).lift σ) :=
    call_sat_of h 399 (callAt 399) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 399).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 399).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 399).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits400 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 400 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 400).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 400).plugs = [(Xark.R1cs.LC.var (400 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 400).base = bitBase 400 := by rfl
  have glc : (bitGLC 400 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 400).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 400 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 400).t.Sat ((callAt 400).lift σ) :=
    call_sat_of h 400 (callAt 400) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 400).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 400).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 400).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits401 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 401 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 401).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 401).plugs = [(Xark.R1cs.LC.var (401 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 401).base = bitBase 401 := by rfl
  have glc : (bitGLC 401 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 401).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 401 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 401).t.Sat ((callAt 401).lift σ) :=
    call_sat_of h 401 (callAt 401) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 401).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 401).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 401).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits402 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 402 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 402).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 402).plugs = [(Xark.R1cs.LC.var (402 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 402).base = bitBase 402 := by rfl
  have glc : (bitGLC 402 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 402).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 402 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 402).t.Sat ((callAt 402).lift σ) :=
    call_sat_of h 402 (callAt 402) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 402).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 402).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 402).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits403 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 403 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 403).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 403).plugs = [(Xark.R1cs.LC.var (403 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 403).base = bitBase 403 := by rfl
  have glc : (bitGLC 403 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 403).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 403 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 403).t.Sat ((callAt 403).lift σ) :=
    call_sat_of h 403 (callAt 403) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 403).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 403).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 403).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits404 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 404 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 404).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 404).plugs = [(Xark.R1cs.LC.var (404 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 404).base = bitBase 404 := by rfl
  have glc : (bitGLC 404 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 404).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 404 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 404).t.Sat ((callAt 404).lift σ) :=
    call_sat_of h 404 (callAt 404) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 404).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 404).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 404).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits405 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 405 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 405).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 405).plugs = [(Xark.R1cs.LC.var (405 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 405).base = bitBase 405 := by rfl
  have glc : (bitGLC 405 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 405).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 405 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 405).t.Sat ((callAt 405).lift σ) :=
    call_sat_of h 405 (callAt 405) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 405).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 405).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 405).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits406 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 406 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 406).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 406).plugs = [(Xark.R1cs.LC.var (406 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 406).base = bitBase 406 := by rfl
  have glc : (bitGLC 406 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 406).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 406 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 406).t.Sat ((callAt 406).lift σ) :=
    call_sat_of h 406 (callAt 406) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 406).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 406).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 406).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits407 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 407 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 407).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 407).plugs = [(Xark.R1cs.LC.var (407 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 407).base = bitBase 407 := by rfl
  have glc : (bitGLC 407 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 407).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 407 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 407).t.Sat ((callAt 407).lift σ) :=
    call_sat_of h 407 (callAt 407) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 407).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 407).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 407).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits408 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 408 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 408).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 408).plugs = [(Xark.R1cs.LC.var (408 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 408).base = bitBase 408 := by rfl
  have glc : (bitGLC 408 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 408).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 408 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 408).t.Sat ((callAt 408).lift σ) :=
    call_sat_of h 408 (callAt 408) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 408).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 408).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 408).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits409 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 409 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 409).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 409).plugs = [(Xark.R1cs.LC.var (409 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 409).base = bitBase 409 := by rfl
  have glc : (bitGLC 409 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 409).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 409 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 409).t.Sat ((callAt 409).lift σ) :=
    call_sat_of h 409 (callAt 409) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 409).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 409).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 409).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits410 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 410 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 410).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 410).plugs = [(Xark.R1cs.LC.var (410 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 410).base = bitBase 410 := by rfl
  have glc : (bitGLC 410 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 410).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 410 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 410).t.Sat ((callAt 410).lift σ) :=
    call_sat_of h 410 (callAt 410) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 410).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 410).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 410).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits411 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 411 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 411).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 411).plugs = [(Xark.R1cs.LC.var (411 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 411).base = bitBase 411 := by rfl
  have glc : (bitGLC 411 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 411).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 411 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 411).t.Sat ((callAt 411).lift σ) :=
    call_sat_of h 411 (callAt 411) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 411).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 411).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 411).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits412 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 412 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 412).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 412).plugs = [(Xark.R1cs.LC.var (412 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 412).base = bitBase 412 := by rfl
  have glc : (bitGLC 412 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 412).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 412 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 412).t.Sat ((callAt 412).lift σ) :=
    call_sat_of h 412 (callAt 412) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 412).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 412).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 412).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits413 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 413 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 413).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 413).plugs = [(Xark.R1cs.LC.var (413 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 413).base = bitBase 413 := by rfl
  have glc : (bitGLC 413 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 413).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 413 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 413).t.Sat ((callAt 413).lift σ) :=
    call_sat_of h 413 (callAt 413) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 413).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 413).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 413).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits414 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 414 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 414).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 414).plugs = [(Xark.R1cs.LC.var (414 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 414).base = bitBase 414 := by rfl
  have glc : (bitGLC 414 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 414).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 414 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 414).t.Sat ((callAt 414).lift σ) :=
    call_sat_of h 414 (callAt 414) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 414).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 414).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 414).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits415 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 415 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 415).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 415).plugs = [(Xark.R1cs.LC.var (415 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 415).base = bitBase 415 := by rfl
  have glc : (bitGLC 415 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 415).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 415 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 415).t.Sat ((callAt 415).lift σ) :=
    call_sat_of h 415 (callAt 415) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 415).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 415).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 415).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits416 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 416 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 416).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 416).plugs = [(Xark.R1cs.LC.var (416 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 416).base = bitBase 416 := by rfl
  have glc : (bitGLC 416 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 416).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 416 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 416).t.Sat ((callAt 416).lift σ) :=
    call_sat_of h 416 (callAt 416) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 416).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 416).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 416).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits417 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 417 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 417).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 417).plugs = [(Xark.R1cs.LC.var (417 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 417).base = bitBase 417 := by rfl
  have glc : (bitGLC 417 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 417).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 417 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 417).t.Sat ((callAt 417).lift σ) :=
    call_sat_of h 417 (callAt 417) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 417).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 417).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 417).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits418 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 418 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 418).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 418).plugs = [(Xark.R1cs.LC.var (418 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 418).base = bitBase 418 := by rfl
  have glc : (bitGLC 418 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 418).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 418 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 418).t.Sat ((callAt 418).lift σ) :=
    call_sat_of h 418 (callAt 418) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 418).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 418).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 418).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits419 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 419 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 419).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 419).plugs = [(Xark.R1cs.LC.var (419 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 419).base = bitBase 419 := by rfl
  have glc : (bitGLC 419 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 419).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 419 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 419).t.Sat ((callAt 419).lift σ) :=
    call_sat_of h 419 (callAt 419) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 419).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 419).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 419).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits420 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 420 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 420).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 420).plugs = [(Xark.R1cs.LC.var (420 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 420).base = bitBase 420 := by rfl
  have glc : (bitGLC 420 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 420).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 420 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 420).t.Sat ((callAt 420).lift σ) :=
    call_sat_of h 420 (callAt 420) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 420).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 420).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 420).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits421 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 421 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 421).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 421).plugs = [(Xark.R1cs.LC.var (421 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 421).base = bitBase 421 := by rfl
  have glc : (bitGLC 421 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 421).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 421 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 421).t.Sat ((callAt 421).lift σ) :=
    call_sat_of h 421 (callAt 421) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 421).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 421).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 421).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits422 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 422 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 422).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 422).plugs = [(Xark.R1cs.LC.var (422 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 422).base = bitBase 422 := by rfl
  have glc : (bitGLC 422 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 422).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 422 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 422).t.Sat ((callAt 422).lift σ) :=
    call_sat_of h 422 (callAt 422) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 422).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 422).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 422).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits423 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 423 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 423).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 423).plugs = [(Xark.R1cs.LC.var (423 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 423).base = bitBase 423 := by rfl
  have glc : (bitGLC 423 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 423).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 423 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 423).t.Sat ((callAt 423).lift σ) :=
    call_sat_of h 423 (callAt 423) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 423).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 423).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 423).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits424 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 424 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 424).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 424).plugs = [(Xark.R1cs.LC.var (424 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 424).base = bitBase 424 := by rfl
  have glc : (bitGLC 424 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 424).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 424 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 424).t.Sat ((callAt 424).lift σ) :=
    call_sat_of h 424 (callAt 424) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 424).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 424).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 424).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits425 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 425 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 425).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 425).plugs = [(Xark.R1cs.LC.var (425 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 425).base = bitBase 425 := by rfl
  have glc : (bitGLC 425 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 425).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 425 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 425).t.Sat ((callAt 425).lift σ) :=
    call_sat_of h 425 (callAt 425) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 425).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 425).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 425).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits426 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 426 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 426).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 426).plugs = [(Xark.R1cs.LC.var (426 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 426).base = bitBase 426 := by rfl
  have glc : (bitGLC 426 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 426).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 426 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 426).t.Sat ((callAt 426).lift σ) :=
    call_sat_of h 426 (callAt 426) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 426).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 426).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 426).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits427 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 427 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 427).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 427).plugs = [(Xark.R1cs.LC.var (427 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 427).base = bitBase 427 := by rfl
  have glc : (bitGLC 427 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 427).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 427 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 427).t.Sat ((callAt 427).lift σ) :=
    call_sat_of h 427 (callAt 427) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 427).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 427).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 427).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits428 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 428 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 428).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 428).plugs = [(Xark.R1cs.LC.var (428 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 428).base = bitBase 428 := by rfl
  have glc : (bitGLC 428 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 428).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 428 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 428).t.Sat ((callAt 428).lift σ) :=
    call_sat_of h 428 (callAt 428) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 428).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 428).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 428).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits429 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 429 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 429).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 429).plugs = [(Xark.R1cs.LC.var (429 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 429).base = bitBase 429 := by rfl
  have glc : (bitGLC 429 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 429).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 429 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 429).t.Sat ((callAt 429).lift σ) :=
    call_sat_of h 429 (callAt 429) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 429).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 429).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 429).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits430 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 430 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 430).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 430).plugs = [(Xark.R1cs.LC.var (430 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 430).base = bitBase 430 := by rfl
  have glc : (bitGLC 430 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 430).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 430 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 430).t.Sat ((callAt 430).lift σ) :=
    call_sat_of h 430 (callAt 430) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 430).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 430).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 430).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits431 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 431 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 431).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 431).plugs = [(Xark.R1cs.LC.var (431 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 431).base = bitBase 431 := by rfl
  have glc : (bitGLC 431 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 431).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 431 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 431).t.Sat ((callAt 431).lift σ) :=
    call_sat_of h 431 (callAt 431) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 431).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 431).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 431).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits432 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 432 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 432).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 432).plugs = [(Xark.R1cs.LC.var (432 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 432).base = bitBase 432 := by rfl
  have glc : (bitGLC 432 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 432).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 432 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 432).t.Sat ((callAt 432).lift σ) :=
    call_sat_of h 432 (callAt 432) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 432).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 432).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 432).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits433 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 433 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 433).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 433).plugs = [(Xark.R1cs.LC.var (433 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 433).base = bitBase 433 := by rfl
  have glc : (bitGLC 433 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 433).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 433 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 433).t.Sat ((callAt 433).lift σ) :=
    call_sat_of h 433 (callAt 433) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 433).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 433).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 433).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits434 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 434 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 434).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 434).plugs = [(Xark.R1cs.LC.var (434 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 434).base = bitBase 434 := by rfl
  have glc : (bitGLC 434 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 434).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 434 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 434).t.Sat ((callAt 434).lift σ) :=
    call_sat_of h 434 (callAt 434) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 434).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 434).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 434).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits435 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 435 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 435).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 435).plugs = [(Xark.R1cs.LC.var (435 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 435).base = bitBase 435 := by rfl
  have glc : (bitGLC 435 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 435).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 435 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 435).t.Sat ((callAt 435).lift σ) :=
    call_sat_of h 435 (callAt 435) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 435).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 435).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 435).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits436 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 436 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 436).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 436).plugs = [(Xark.R1cs.LC.var (436 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 436).base = bitBase 436 := by rfl
  have glc : (bitGLC 436 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 436).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 436 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 436).t.Sat ((callAt 436).lift σ) :=
    call_sat_of h 436 (callAt 436) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 436).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 436).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 436).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits437 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 437 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 437).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 437).plugs = [(Xark.R1cs.LC.var (437 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 437).base = bitBase 437 := by rfl
  have glc : (bitGLC 437 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 437).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 437 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 437).t.Sat ((callAt 437).lift σ) :=
    call_sat_of h 437 (callAt 437) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 437).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 437).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 437).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits438 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 438 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 438).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 438).plugs = [(Xark.R1cs.LC.var (438 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 438).base = bitBase 438 := by rfl
  have glc : (bitGLC 438 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 438).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 438 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 438).t.Sat ((callAt 438).lift σ) :=
    call_sat_of h 438 (callAt 438) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 438).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 438).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 438).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits439 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 439 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 439).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 439).plugs = [(Xark.R1cs.LC.var (439 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 439).base = bitBase 439 := by rfl
  have glc : (bitGLC 439 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 439).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 439 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 439).t.Sat ((callAt 439).lift σ) :=
    call_sat_of h 439 (callAt 439) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 439).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 439).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 439).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits440 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 440 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 440).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 440).plugs = [(Xark.R1cs.LC.var (440 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 440).base = bitBase 440 := by rfl
  have glc : (bitGLC 440 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 440).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 440 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 440).t.Sat ((callAt 440).lift σ) :=
    call_sat_of h 440 (callAt 440) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 440).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 440).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 440).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits441 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 441 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 441).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 441).plugs = [(Xark.R1cs.LC.var (441 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 441).base = bitBase 441 := by rfl
  have glc : (bitGLC 441 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 441).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 441 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 441).t.Sat ((callAt 441).lift σ) :=
    call_sat_of h 441 (callAt 441) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 441).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 441).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 441).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits442 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 442 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 442).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 442).plugs = [(Xark.R1cs.LC.var (442 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 442).base = bitBase 442 := by rfl
  have glc : (bitGLC 442 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 442).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 442 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 442).t.Sat ((callAt 442).lift σ) :=
    call_sat_of h 442 (callAt 442) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 442).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 442).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 442).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits443 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 443 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 443).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 443).plugs = [(Xark.R1cs.LC.var (443 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 443).base = bitBase 443 := by rfl
  have glc : (bitGLC 443 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 443).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 443 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 443).t.Sat ((callAt 443).lift σ) :=
    call_sat_of h 443 (callAt 443) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 443).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 443).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 443).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits444 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 444 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 444).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 444).plugs = [(Xark.R1cs.LC.var (444 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 444).base = bitBase 444 := by rfl
  have glc : (bitGLC 444 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 444).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 444 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 444).t.Sat ((callAt 444).lift σ) :=
    call_sat_of h 444 (callAt 444) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 444).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 444).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 444).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits445 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 445 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 445).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 445).plugs = [(Xark.R1cs.LC.var (445 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 445).base = bitBase 445 := by rfl
  have glc : (bitGLC 445 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 445).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 445 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 445).t.Sat ((callAt 445).lift σ) :=
    call_sat_of h 445 (callAt 445) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 445).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 445).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 445).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits446 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 446 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 446).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 446).plugs = [(Xark.R1cs.LC.var (446 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 446).base = bitBase 446 := by rfl
  have glc : (bitGLC 446 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 446).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 446 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 446).t.Sat ((callAt 446).lift σ) :=
    call_sat_of h 446 (callAt 446) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 446).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 446).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 446).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits447 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 447 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 447).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 447).plugs = [(Xark.R1cs.LC.var (447 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 447).base = bitBase 447 := by rfl
  have glc : (bitGLC 447 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 447).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 447 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 447).t.Sat ((callAt 447).lift σ) :=
    call_sat_of h 447 (callAt 447) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 447).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 447).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 447).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits448 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 448 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 448).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 448).plugs = [(Xark.R1cs.LC.var (448 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 448).base = bitBase 448 := by rfl
  have glc : (bitGLC 448 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 448).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 448 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 448).t.Sat ((callAt 448).lift σ) :=
    call_sat_of h 448 (callAt 448) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 448).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 448).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 448).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits449 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 449 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 449).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 449).plugs = [(Xark.R1cs.LC.var (449 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 449).base = bitBase 449 := by rfl
  have glc : (bitGLC 449 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 449).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 449 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 449).t.Sat ((callAt 449).lift σ) :=
    call_sat_of h 449 (callAt 449) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 449).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 449).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 449).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits450 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 450 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 450).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 450).plugs = [(Xark.R1cs.LC.var (450 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 450).base = bitBase 450 := by rfl
  have glc : (bitGLC 450 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 450).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 450 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 450).t.Sat ((callAt 450).lift σ) :=
    call_sat_of h 450 (callAt 450) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 450).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 450).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 450).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits451 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 451 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 451).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 451).plugs = [(Xark.R1cs.LC.var (451 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 451).base = bitBase 451 := by rfl
  have glc : (bitGLC 451 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 451).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 451 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 451).t.Sat ((callAt 451).lift σ) :=
    call_sat_of h 451 (callAt 451) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 451).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 451).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 451).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits452 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 452 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 452).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 452).plugs = [(Xark.R1cs.LC.var (452 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 452).base = bitBase 452 := by rfl
  have glc : (bitGLC 452 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 452).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 452 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 452).t.Sat ((callAt 452).lift σ) :=
    call_sat_of h 452 (callAt 452) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 452).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 452).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 452).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits453 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 453 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 453).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 453).plugs = [(Xark.R1cs.LC.var (453 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 453).base = bitBase 453 := by rfl
  have glc : (bitGLC 453 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 453).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 453 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 453).t.Sat ((callAt 453).lift σ) :=
    call_sat_of h 453 (callAt 453) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 453).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 453).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 453).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits454 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 454 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 454).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 454).plugs = [(Xark.R1cs.LC.var (454 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 454).base = bitBase 454 := by rfl
  have glc : (bitGLC 454 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 454).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 454 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 454).t.Sat ((callAt 454).lift σ) :=
    call_sat_of h 454 (callAt 454) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 454).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 454).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 454).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits455 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 455 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 455).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 455).plugs = [(Xark.R1cs.LC.var (455 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 455).base = bitBase 455 := by rfl
  have glc : (bitGLC 455 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 455).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 455 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 455).t.Sat ((callAt 455).lift σ) :=
    call_sat_of h 455 (callAt 455) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 455).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 455).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 455).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits456 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 456 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 456).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 456).plugs = [(Xark.R1cs.LC.var (456 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 456).base = bitBase 456 := by rfl
  have glc : (bitGLC 456 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 456).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 456 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 456).t.Sat ((callAt 456).lift σ) :=
    call_sat_of h 456 (callAt 456) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 456).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 456).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 456).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits457 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 457 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 457).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 457).plugs = [(Xark.R1cs.LC.var (457 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 457).base = bitBase 457 := by rfl
  have glc : (bitGLC 457 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 457).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 457 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 457).t.Sat ((callAt 457).lift σ) :=
    call_sat_of h 457 (callAt 457) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 457).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 457).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 457).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits458 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 458 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 458).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 458).plugs = [(Xark.R1cs.LC.var (458 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 458).base = bitBase 458 := by rfl
  have glc : (bitGLC 458 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 458).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 458 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 458).t.Sat ((callAt 458).lift σ) :=
    call_sat_of h 458 (callAt 458) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 458).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 458).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 458).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits459 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 459 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 459).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 459).plugs = [(Xark.R1cs.LC.var (459 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 459).base = bitBase 459 := by rfl
  have glc : (bitGLC 459 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 459).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 459 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 459).t.Sat ((callAt 459).lift σ) :=
    call_sat_of h 459 (callAt 459) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 459).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 459).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 459).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits460 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 460 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 460).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 460).plugs = [(Xark.R1cs.LC.var (460 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 460).base = bitBase 460 := by rfl
  have glc : (bitGLC 460 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 460).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 460 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 460).t.Sat ((callAt 460).lift σ) :=
    call_sat_of h 460 (callAt 460) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 460).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 460).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 460).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits461 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 461 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 461).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 461).plugs = [(Xark.R1cs.LC.var (461 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 461).base = bitBase 461 := by rfl
  have glc : (bitGLC 461 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 461).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 461 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 461).t.Sat ((callAt 461).lift σ) :=
    call_sat_of h 461 (callAt 461) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 461).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 461).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 461).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits462 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 462 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 462).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 462).plugs = [(Xark.R1cs.LC.var (462 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 462).base = bitBase 462 := by rfl
  have glc : (bitGLC 462 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 462).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 462 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 462).t.Sat ((callAt 462).lift σ) :=
    call_sat_of h 462 (callAt 462) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 462).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 462).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 462).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits463 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 463 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 463).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 463).plugs = [(Xark.R1cs.LC.var (463 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 463).base = bitBase 463 := by rfl
  have glc : (bitGLC 463 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 463).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 463 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 463).t.Sat ((callAt 463).lift σ) :=
    call_sat_of h 463 (callAt 463) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 463).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 463).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 463).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits464 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 464 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 464).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 464).plugs = [(Xark.R1cs.LC.var (464 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 464).base = bitBase 464 := by rfl
  have glc : (bitGLC 464 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 464).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 464 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 464).t.Sat ((callAt 464).lift σ) :=
    call_sat_of h 464 (callAt 464) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 464).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 464).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 464).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits465 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 465 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 465).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 465).plugs = [(Xark.R1cs.LC.var (465 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 465).base = bitBase 465 := by rfl
  have glc : (bitGLC 465 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 465).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 465 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 465).t.Sat ((callAt 465).lift σ) :=
    call_sat_of h 465 (callAt 465) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 465).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 465).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 465).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits466 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 466 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 466).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 466).plugs = [(Xark.R1cs.LC.var (466 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 466).base = bitBase 466 := by rfl
  have glc : (bitGLC 466 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 466).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 466 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 466).t.Sat ((callAt 466).lift σ) :=
    call_sat_of h 466 (callAt 466) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 466).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 466).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 466).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits467 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 467 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 467).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 467).plugs = [(Xark.R1cs.LC.var (467 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 467).base = bitBase 467 := by rfl
  have glc : (bitGLC 467 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 467).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 467 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 467).t.Sat ((callAt 467).lift σ) :=
    call_sat_of h 467 (callAt 467) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 467).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 467).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 467).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits468 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 468 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 468).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 468).plugs = [(Xark.R1cs.LC.var (468 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 468).base = bitBase 468 := by rfl
  have glc : (bitGLC 468 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 468).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 468 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 468).t.Sat ((callAt 468).lift σ) :=
    call_sat_of h 468 (callAt 468) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 468).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 468).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 468).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits469 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 469 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 469).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 469).plugs = [(Xark.R1cs.LC.var (469 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 469).base = bitBase 469 := by rfl
  have glc : (bitGLC 469 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 469).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 469 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 469).t.Sat ((callAt 469).lift σ) :=
    call_sat_of h 469 (callAt 469) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 469).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 469).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 469).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits470 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 470 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 470).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 470).plugs = [(Xark.R1cs.LC.var (470 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 470).base = bitBase 470 := by rfl
  have glc : (bitGLC 470 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 470).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 470 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 470).t.Sat ((callAt 470).lift σ) :=
    call_sat_of h 470 (callAt 470) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 470).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 470).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 470).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits471 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 471 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 471).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 471).plugs = [(Xark.R1cs.LC.var (471 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 471).base = bitBase 471 := by rfl
  have glc : (bitGLC 471 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 471).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 471 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 471).t.Sat ((callAt 471).lift σ) :=
    call_sat_of h 471 (callAt 471) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 471).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 471).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 471).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits472 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 472 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 472).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 472).plugs = [(Xark.R1cs.LC.var (472 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 472).base = bitBase 472 := by rfl
  have glc : (bitGLC 472 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 472).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 472 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 472).t.Sat ((callAt 472).lift σ) :=
    call_sat_of h 472 (callAt 472) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 472).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 472).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 472).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits473 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 473 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 473).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 473).plugs = [(Xark.R1cs.LC.var (473 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 473).base = bitBase 473 := by rfl
  have glc : (bitGLC 473 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 473).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 473 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 473).t.Sat ((callAt 473).lift σ) :=
    call_sat_of h 473 (callAt 473) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 473).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 473).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 473).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits474 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 474 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 474).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 474).plugs = [(Xark.R1cs.LC.var (474 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 474).base = bitBase 474 := by rfl
  have glc : (bitGLC 474 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 474).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 474 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 474).t.Sat ((callAt 474).lift σ) :=
    call_sat_of h 474 (callAt 474) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 474).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 474).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 474).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits475 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 475 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 475).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 475).plugs = [(Xark.R1cs.LC.var (475 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 475).base = bitBase 475 := by rfl
  have glc : (bitGLC 475 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 475).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 475 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 475).t.Sat ((callAt 475).lift σ) :=
    call_sat_of h 475 (callAt 475) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 475).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 475).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 475).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits476 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 476 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 476).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 476).plugs = [(Xark.R1cs.LC.var (476 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 476).base = bitBase 476 := by rfl
  have glc : (bitGLC 476 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 476).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 476 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 476).t.Sat ((callAt 476).lift σ) :=
    call_sat_of h 476 (callAt 476) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 476).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 476).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 476).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits477 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 477 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 477).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 477).plugs = [(Xark.R1cs.LC.var (477 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 477).base = bitBase 477 := by rfl
  have glc : (bitGLC 477 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 477).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 477 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 477).t.Sat ((callAt 477).lift σ) :=
    call_sat_of h 477 (callAt 477) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 477).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 477).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 477).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits478 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 478 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 478).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 478).plugs = [(Xark.R1cs.LC.var (478 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 478).base = bitBase 478 := by rfl
  have glc : (bitGLC 478 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 478).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 478 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 478).t.Sat ((callAt 478).lift σ) :=
    call_sat_of h 478 (callAt 478) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 478).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 478).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 478).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits479 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 479 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 479).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 479).plugs = [(Xark.R1cs.LC.var (479 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 479).base = bitBase 479 := by rfl
  have glc : (bitGLC 479 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 479).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 479 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 479).t.Sat ((callAt 479).lift σ) :=
    call_sat_of h 479 (callAt 479) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 479).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 479).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 479).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits480 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 480 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 480).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 480).plugs = [(Xark.R1cs.LC.var (480 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 480).base = bitBase 480 := by rfl
  have glc : (bitGLC 480 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 480).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 480 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 480).t.Sat ((callAt 480).lift σ) :=
    call_sat_of h 480 (callAt 480) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 480).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 480).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 480).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits481 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 481 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 481).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 481).plugs = [(Xark.R1cs.LC.var (481 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 481).base = bitBase 481 := by rfl
  have glc : (bitGLC 481 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 481).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 481 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 481).t.Sat ((callAt 481).lift σ) :=
    call_sat_of h 481 (callAt 481) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 481).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 481).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 481).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits482 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 482 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 482).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 482).plugs = [(Xark.R1cs.LC.var (482 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 482).base = bitBase 482 := by rfl
  have glc : (bitGLC 482 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 482).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 482 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 482).t.Sat ((callAt 482).lift σ) :=
    call_sat_of h 482 (callAt 482) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 482).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 482).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 482).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits483 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 483 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 483).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 483).plugs = [(Xark.R1cs.LC.var (483 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 483).base = bitBase 483 := by rfl
  have glc : (bitGLC 483 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 483).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 483 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 483).t.Sat ((callAt 483).lift σ) :=
    call_sat_of h 483 (callAt 483) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 483).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 483).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 483).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits484 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 484 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 484).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 484).plugs = [(Xark.R1cs.LC.var (484 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 484).base = bitBase 484 := by rfl
  have glc : (bitGLC 484 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 484).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 484 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 484).t.Sat ((callAt 484).lift σ) :=
    call_sat_of h 484 (callAt 484) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 484).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 484).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 484).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits485 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 485 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 485).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 485).plugs = [(Xark.R1cs.LC.var (485 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 485).base = bitBase 485 := by rfl
  have glc : (bitGLC 485 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 485).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 485 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 485).t.Sat ((callAt 485).lift σ) :=
    call_sat_of h 485 (callAt 485) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 485).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 485).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 485).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits486 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 486 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 486).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 486).plugs = [(Xark.R1cs.LC.var (486 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 486).base = bitBase 486 := by rfl
  have glc : (bitGLC 486 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 486).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 486 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 486).t.Sat ((callAt 486).lift σ) :=
    call_sat_of h 486 (callAt 486) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 486).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 486).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 486).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits487 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 487 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 487).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 487).plugs = [(Xark.R1cs.LC.var (487 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 487).base = bitBase 487 := by rfl
  have glc : (bitGLC 487 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 487).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 487 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 487).t.Sat ((callAt 487).lift σ) :=
    call_sat_of h 487 (callAt 487) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 487).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 487).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 487).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits488 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 488 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 488).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 488).plugs = [(Xark.R1cs.LC.var (488 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 488).base = bitBase 488 := by rfl
  have glc : (bitGLC 488 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 488).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 488 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 488).t.Sat ((callAt 488).lift σ) :=
    call_sat_of h 488 (callAt 488) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 488).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 488).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 488).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits489 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 489 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 489).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 489).plugs = [(Xark.R1cs.LC.var (489 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 489).base = bitBase 489 := by rfl
  have glc : (bitGLC 489 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 489).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 489 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 489).t.Sat ((callAt 489).lift σ) :=
    call_sat_of h 489 (callAt 489) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 489).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 489).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 489).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits490 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 490 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 490).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 490).plugs = [(Xark.R1cs.LC.var (490 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 490).base = bitBase 490 := by rfl
  have glc : (bitGLC 490 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 490).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 490 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 490).t.Sat ((callAt 490).lift σ) :=
    call_sat_of h 490 (callAt 490) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 490).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 490).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 490).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits491 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 491 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 491).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 491).plugs = [(Xark.R1cs.LC.var (491 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 491).base = bitBase 491 := by rfl
  have glc : (bitGLC 491 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 491).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 491 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 491).t.Sat ((callAt 491).lift σ) :=
    call_sat_of h 491 (callAt 491) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 491).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 491).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 491).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits492 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 492 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 492).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 492).plugs = [(Xark.R1cs.LC.var (492 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 492).base = bitBase 492 := by rfl
  have glc : (bitGLC 492 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 492).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 492 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 492).t.Sat ((callAt 492).lift σ) :=
    call_sat_of h 492 (callAt 492) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 492).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 492).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 492).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits493 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 493 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 493).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 493).plugs = [(Xark.R1cs.LC.var (493 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 493).base = bitBase 493 := by rfl
  have glc : (bitGLC 493 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 493).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 493 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 493).t.Sat ((callAt 493).lift σ) :=
    call_sat_of h 493 (callAt 493) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 493).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 493).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 493).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits494 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 494 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 494).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 494).plugs = [(Xark.R1cs.LC.var (494 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 494).base = bitBase 494 := by rfl
  have glc : (bitGLC 494 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 494).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 494 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 494).t.Sat ((callAt 494).lift σ) :=
    call_sat_of h 494 (callAt 494) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 494).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 494).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 494).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits495 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 495 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 495).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 495).plugs = [(Xark.R1cs.LC.var (495 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 495).base = bitBase 495 := by rfl
  have glc : (bitGLC 495 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 495).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 495 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 495).t.Sat ((callAt 495).lift σ) :=
    call_sat_of h 495 (callAt 495) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 495).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 495).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 495).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits496 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 496 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 496).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 496).plugs = [(Xark.R1cs.LC.var (496 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 496).base = bitBase 496 := by rfl
  have glc : (bitGLC 496 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 496).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 496 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 496).t.Sat ((callAt 496).lift σ) :=
    call_sat_of h 496 (callAt 496) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 496).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 496).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 496).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits497 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 497 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 497).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 497).plugs = [(Xark.R1cs.LC.var (497 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 497).base = bitBase 497 := by rfl
  have glc : (bitGLC 497 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 497).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 497 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 497).t.Sat ((callAt 497).lift σ) :=
    call_sat_of h 497 (callAt 497) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 497).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 497).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 497).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits498 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 498 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 498).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 498).plugs = [(Xark.R1cs.LC.var (498 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 498).base = bitBase 498 := by rfl
  have glc : (bitGLC 498 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 498).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 498 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 498).t.Sat ((callAt 498).lift σ) :=
    call_sat_of h 498 (callAt 498) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 498).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 498).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 498).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits499 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 499 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 499).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 499).plugs = [(Xark.R1cs.LC.var (499 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 499).base = bitBase 499 := by rfl
  have glc : (bitGLC 499 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 499).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 499 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 499).t.Sat ((callAt 499).lift σ) :=
    call_sat_of h 499 (callAt 499) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 499).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 499).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 499).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits500 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 500 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 500).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 500).plugs = [(Xark.R1cs.LC.var (500 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 500).base = bitBase 500 := by rfl
  have glc : (bitGLC 500 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 500).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 500 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 500).t.Sat ((callAt 500).lift σ) :=
    call_sat_of h 500 (callAt 500) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 500).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 500).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 500).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits501 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 501 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 501).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 501).plugs = [(Xark.R1cs.LC.var (501 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 501).base = bitBase 501 := by rfl
  have glc : (bitGLC 501 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 501).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 501 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 501).t.Sat ((callAt 501).lift σ) :=
    call_sat_of h 501 (callAt 501) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 501).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 501).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 501).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits502 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 502 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 502).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 502).plugs = [(Xark.R1cs.LC.var (502 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 502).base = bitBase 502 := by rfl
  have glc : (bitGLC 502 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 502).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 502 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 502).t.Sat ((callAt 502).lift σ) :=
    call_sat_of h 502 (callAt 502) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 502).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 502).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 502).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits503 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 503 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 503).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 503).plugs = [(Xark.R1cs.LC.var (503 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 503).base = bitBase 503 := by rfl
  have glc : (bitGLC 503 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 503).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 503 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 503).t.Sat ((callAt 503).lift σ) :=
    call_sat_of h 503 (callAt 503) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 503).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 503).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 503).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits504 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 504 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 504).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 504).plugs = [(Xark.R1cs.LC.var (504 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 504).base = bitBase 504 := by rfl
  have glc : (bitGLC 504 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 504).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 504 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 504).t.Sat ((callAt 504).lift σ) :=
    call_sat_of h 504 (callAt 504) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 504).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 504).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 504).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits505 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 505 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 505).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 505).plugs = [(Xark.R1cs.LC.var (505 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 505).base = bitBase 505 := by rfl
  have glc : (bitGLC 505 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 505).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 505 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 505).t.Sat ((callAt 505).lift σ) :=
    call_sat_of h 505 (callAt 505) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 505).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 505).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 505).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits506 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 506 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 506).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 506).plugs = [(Xark.R1cs.LC.var (506 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 506).base = bitBase 506 := by rfl
  have glc : (bitGLC 506 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 506).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 506 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 506).t.Sat ((callAt 506).lift σ) :=
    call_sat_of h 506 (callAt 506) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 506).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 506).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 506).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits507 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 507 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 507).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 507).plugs = [(Xark.R1cs.LC.var (507 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 507).base = bitBase 507 := by rfl
  have glc : (bitGLC 507 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 507).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 507 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 507).t.Sat ((callAt 507).lift σ) :=
    call_sat_of h 507 (callAt 507) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 507).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 507).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 507).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits508 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 508 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 508).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 508).plugs = [(Xark.R1cs.LC.var (508 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 508).base = bitBase 508 := by rfl
  have glc : (bitGLC 508 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 508).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 508 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 508).t.Sat ((callAt 508).lift σ) :=
    call_sat_of h 508 (callAt 508) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 508).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 508).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 508).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits509 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 509 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 509).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 509).plugs = [(Xark.R1cs.LC.var (509 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 509).base = bitBase 509 := by rfl
  have glc : (bitGLC 509 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 509).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 509 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 509).t.Sat ((callAt 509).lift σ) :=
    call_sat_of h 509 (callAt 509) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 509).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 509).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 509).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits510 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 510 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 510).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 510).plugs = [(Xark.R1cs.LC.var (510 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 510).base = bitBase 510 := by rfl
  have glc : (bitGLC 510 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 510).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 510 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 510).t.Sat ((callAt 510).lift σ) :=
    call_sat_of h 510 (callAt 510) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 510).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 510).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 510).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits511 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 511 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 511).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 511).plugs = [(Xark.R1cs.LC.var (511 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 511).base = bitBase 511 := by rfl
  have glc : (bitGLC 511 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 511).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 511 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 511).t.Sat ((callAt 511).lift σ) :=
    call_sat_of h 511 (callAt 511) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 511).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 511).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 511).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits512 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 512 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 512).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 512).plugs = [(Xark.R1cs.LC.var (512 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 512).base = bitBase 512 := by rfl
  have glc : (bitGLC 512 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 512).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 512 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 512).t.Sat ((callAt 512).lift σ) :=
    call_sat_of h 512 (callAt 512) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 512).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 512).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 512).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits513 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 513 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 513).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 513).plugs = [(Xark.R1cs.LC.var (513 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 513).base = bitBase 513 := by rfl
  have glc : (bitGLC 513 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 513).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 513 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 513).t.Sat ((callAt 513).lift σ) :=
    call_sat_of h 513 (callAt 513) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 513).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 513).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 513).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits514 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 514 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 514).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 514).plugs = [(Xark.R1cs.LC.var (514 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 514).base = bitBase 514 := by rfl
  have glc : (bitGLC 514 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 514).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 514 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 514).t.Sat ((callAt 514).lift σ) :=
    call_sat_of h 514 (callAt 514) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 514).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 514).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 514).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits515 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 515 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 515).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 515).plugs = [(Xark.R1cs.LC.var (515 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 515).base = bitBase 515 := by rfl
  have glc : (bitGLC 515 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 515).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 515 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 515).t.Sat ((callAt 515).lift σ) :=
    call_sat_of h 515 (callAt 515) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 515).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 515).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 515).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits516 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 516 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 516).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 516).plugs = [(Xark.R1cs.LC.var (516 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 516).base = bitBase 516 := by rfl
  have glc : (bitGLC 516 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 516).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 516 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 516).t.Sat ((callAt 516).lift σ) :=
    call_sat_of h 516 (callAt 516) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 516).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 516).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 516).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits517 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 517 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 517).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 517).plugs = [(Xark.R1cs.LC.var (517 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 517).base = bitBase 517 := by rfl
  have glc : (bitGLC 517 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 517).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 517 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 517).t.Sat ((callAt 517).lift σ) :=
    call_sat_of h 517 (callAt 517) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 517).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 517).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 517).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits518 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 518 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 518).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 518).plugs = [(Xark.R1cs.LC.var (518 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 518).base = bitBase 518 := by rfl
  have glc : (bitGLC 518 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 518).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 518 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 518).t.Sat ((callAt 518).lift σ) :=
    call_sat_of h 518 (callAt 518) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 518).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 518).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 518).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits519 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 519 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 519).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 519).plugs = [(Xark.R1cs.LC.var (519 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 519).base = bitBase 519 := by rfl
  have glc : (bitGLC 519 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 519).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 519 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 519).t.Sat ((callAt 519).lift σ) :=
    call_sat_of h 519 (callAt 519) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 519).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 519).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 519).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits520 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 520 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 520).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 520).plugs = [(Xark.R1cs.LC.var (520 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 520).base = bitBase 520 := by rfl
  have glc : (bitGLC 520 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 520).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 520 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 520).t.Sat ((callAt 520).lift σ) :=
    call_sat_of h 520 (callAt 520) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 520).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 520).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 520).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits521 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 521 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 521).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 521).plugs = [(Xark.R1cs.LC.var (521 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 521).base = bitBase 521 := by rfl
  have glc : (bitGLC 521 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 521).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 521 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 521).t.Sat ((callAt 521).lift σ) :=
    call_sat_of h 521 (callAt 521) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 521).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 521).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 521).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits522 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 522 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 522).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 522).plugs = [(Xark.R1cs.LC.var (522 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 522).base = bitBase 522 := by rfl
  have glc : (bitGLC 522 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 522).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 522 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 522).t.Sat ((callAt 522).lift σ) :=
    call_sat_of h 522 (callAt 522) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 522).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 522).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 522).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits523 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 523 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 523).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 523).plugs = [(Xark.R1cs.LC.var (523 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 523).base = bitBase 523 := by rfl
  have glc : (bitGLC 523 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 523).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 523 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 523).t.Sat ((callAt 523).lift σ) :=
    call_sat_of h 523 (callAt 523) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 523).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 523).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 523).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits524 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 524 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 524).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 524).plugs = [(Xark.R1cs.LC.var (524 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 524).base = bitBase 524 := by rfl
  have glc : (bitGLC 524 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 524).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 524 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 524).t.Sat ((callAt 524).lift σ) :=
    call_sat_of h 524 (callAt 524) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 524).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 524).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 524).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits525 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 525 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 525).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 525).plugs = [(Xark.R1cs.LC.var (525 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 525).base = bitBase 525 := by rfl
  have glc : (bitGLC 525 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 525).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 525 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 525).t.Sat ((callAt 525).lift σ) :=
    call_sat_of h 525 (callAt 525) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 525).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 525).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 525).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits526 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 526 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 526).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 526).plugs = [(Xark.R1cs.LC.var (526 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 526).base = bitBase 526 := by rfl
  have glc : (bitGLC 526 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 526).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 526 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 526).t.Sat ((callAt 526).lift σ) :=
    call_sat_of h 526 (callAt 526) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 526).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 526).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 526).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits527 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 527 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 527).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 527).plugs = [(Xark.R1cs.LC.var (527 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 527).base = bitBase 527 := by rfl
  have glc : (bitGLC 527 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 527).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 527 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 527).t.Sat ((callAt 527).lift σ) :=
    call_sat_of h 527 (callAt 527) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 527).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 527).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 527).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits528 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 528 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 528).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 528).plugs = [(Xark.R1cs.LC.var (528 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 528).base = bitBase 528 := by rfl
  have glc : (bitGLC 528 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 528).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 528 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 528).t.Sat ((callAt 528).lift σ) :=
    call_sat_of h 528 (callAt 528) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 528).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 528).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 528).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits529 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 529 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 529).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 529).plugs = [(Xark.R1cs.LC.var (529 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 529).base = bitBase 529 := by rfl
  have glc : (bitGLC 529 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 529).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 529 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 529).t.Sat ((callAt 529).lift σ) :=
    call_sat_of h 529 (callAt 529) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 529).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 529).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 529).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits530 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 530 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 530).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 530).plugs = [(Xark.R1cs.LC.var (530 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 530).base = bitBase 530 := by rfl
  have glc : (bitGLC 530 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 530).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 530 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 530).t.Sat ((callAt 530).lift σ) :=
    call_sat_of h 530 (callAt 530) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 530).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 530).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 530).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits531 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 531 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 531).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 531).plugs = [(Xark.R1cs.LC.var (531 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 531).base = bitBase 531 := by rfl
  have glc : (bitGLC 531 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 531).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 531 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 531).t.Sat ((callAt 531).lift σ) :=
    call_sat_of h 531 (callAt 531) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 531).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 531).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 531).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits532 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 532 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 532).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 532).plugs = [(Xark.R1cs.LC.var (532 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 532).base = bitBase 532 := by rfl
  have glc : (bitGLC 532 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 532).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 532 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 532).t.Sat ((callAt 532).lift σ) :=
    call_sat_of h 532 (callAt 532) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 532).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 532).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 532).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits533 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 533 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 533).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 533).plugs = [(Xark.R1cs.LC.var (533 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 533).base = bitBase 533 := by rfl
  have glc : (bitGLC 533 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 533).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 533 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 533).t.Sat ((callAt 533).lift σ) :=
    call_sat_of h 533 (callAt 533) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 533).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 533).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 533).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits534 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 534 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 534).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 534).plugs = [(Xark.R1cs.LC.var (534 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 534).base = bitBase 534 := by rfl
  have glc : (bitGLC 534 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 534).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 534 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 534).t.Sat ((callAt 534).lift σ) :=
    call_sat_of h 534 (callAt 534) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 534).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 534).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 534).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits535 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 535 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 535).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 535).plugs = [(Xark.R1cs.LC.var (535 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 535).base = bitBase 535 := by rfl
  have glc : (bitGLC 535 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 535).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 535 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 535).t.Sat ((callAt 535).lift σ) :=
    call_sat_of h 535 (callAt 535) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 535).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 535).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 535).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits536 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 536 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 536).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 536).plugs = [(Xark.R1cs.LC.var (536 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 536).base = bitBase 536 := by rfl
  have glc : (bitGLC 536 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 536).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 536 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 536).t.Sat ((callAt 536).lift σ) :=
    call_sat_of h 536 (callAt 536) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 536).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 536).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 536).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits537 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 537 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 537).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 537).plugs = [(Xark.R1cs.LC.var (537 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 537).base = bitBase 537 := by rfl
  have glc : (bitGLC 537 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 537).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 537 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 537).t.Sat ((callAt 537).lift σ) :=
    call_sat_of h 537 (callAt 537) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 537).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 537).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 537).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits538 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 538 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 538).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 538).plugs = [(Xark.R1cs.LC.var (538 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 538).base = bitBase 538 := by rfl
  have glc : (bitGLC 538 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 538).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 538 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 538).t.Sat ((callAt 538).lift σ) :=
    call_sat_of h 538 (callAt 538) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 538).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 538).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 538).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits539 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 539 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 539).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 539).plugs = [(Xark.R1cs.LC.var (539 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 539).base = bitBase 539 := by rfl
  have glc : (bitGLC 539 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 539).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 539 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 539).t.Sat ((callAt 539).lift σ) :=
    call_sat_of h 539 (callAt 539) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 539).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 539).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 539).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits540 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 540 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 540).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 540).plugs = [(Xark.R1cs.LC.var (540 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 540).base = bitBase 540 := by rfl
  have glc : (bitGLC 540 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 540).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 540 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 540).t.Sat ((callAt 540).lift σ) :=
    call_sat_of h 540 (callAt 540) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 540).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 540).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 540).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits541 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 541 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 541).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 541).plugs = [(Xark.R1cs.LC.var (541 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 541).base = bitBase 541 := by rfl
  have glc : (bitGLC 541 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 541).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 541 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 541).t.Sat ((callAt 541).lift σ) :=
    call_sat_of h 541 (callAt 541) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 541).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 541).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 541).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits542 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 542 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 542).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 542).plugs = [(Xark.R1cs.LC.var (542 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 542).base = bitBase 542 := by rfl
  have glc : (bitGLC 542 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 542).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 542 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 542).t.Sat ((callAt 542).lift σ) :=
    call_sat_of h 542 (callAt 542) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 542).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 542).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 542).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem bits543 (σ : ℕ → F) (h : Sat circuit σ) (tb : ℕ) (htb : tb < 8) :
    ((bitGLC 543 tb).eval σ).val ≤ 1 := by
  have hb0 : (callAt 543).t = Xark.Templates.ToBits.template := by rfl
  have hplugs : (callAt 543).plugs = [(Xark.R1cs.LC.var (543 : ℕ) : Xark.Circuit.ZLC)] := by
    decide +kernel
  have hbase : (callAt 543).base = bitBase 543 := by rfl
  have glc : (bitGLC 543 tb).eval σ
      = (Xark.Templates.ToBits.template.outs ((callAt 543).lift σ)).getD tb 0 := by
    rw [bitGLC_eq_bitOut 543 tb htb hplugs hbase hb0, bitOut_eval, hb0]
  have hs : (callAt 543).t.Sat ((callAt 543).lift σ) :=
    call_sat_of h 543 (callAt 543) (by rfl) (by decide)
  rw [hb0] at hs
  have hspec := Xark.Templates.ToBits.soundness ((callAt 543).lift σ) hs
  rw [Xark.Templates.ToBits.Spec, Xark.Templates.ToBits.SpecAt] at hspec
  have hout : (Xark.Templates.ToBits.template.outs ((callAt 543).lift σ)).getD tb 0
      = Xark.Template.bitOf
          ((Xark.Templates.ToBits.template.ins ((callAt 543).lift σ)).getD 0 0) tb := by
    have := congrArg (fun l => l.getD tb 0) hspec.2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htb] using this
  rw [glc, hout]
  exact bitOf_val_le3 _ _

theorem hbit (σ : ℕ → F) (h : Sat circuit σ) :
    ∀ b tb, b < 544 → tb < 8 → ((bitGLC b tb).eval σ).val ≤ 1 := by
  intro b tb hb htb
  interval_cases b
  · exact bits0 σ h tb htb
  · exact bits1 σ h tb htb
  · exact bits2 σ h tb htb
  · exact bits3 σ h tb htb
  · exact bits4 σ h tb htb
  · exact bits5 σ h tb htb
  · exact bits6 σ h tb htb
  · exact bits7 σ h tb htb
  · exact bits8 σ h tb htb
  · exact bits9 σ h tb htb
  · exact bits10 σ h tb htb
  · exact bits11 σ h tb htb
  · exact bits12 σ h tb htb
  · exact bits13 σ h tb htb
  · exact bits14 σ h tb htb
  · exact bits15 σ h tb htb
  · exact bits16 σ h tb htb
  · exact bits17 σ h tb htb
  · exact bits18 σ h tb htb
  · exact bits19 σ h tb htb
  · exact bits20 σ h tb htb
  · exact bits21 σ h tb htb
  · exact bits22 σ h tb htb
  · exact bits23 σ h tb htb
  · exact bits24 σ h tb htb
  · exact bits25 σ h tb htb
  · exact bits26 σ h tb htb
  · exact bits27 σ h tb htb
  · exact bits28 σ h tb htb
  · exact bits29 σ h tb htb
  · exact bits30 σ h tb htb
  · exact bits31 σ h tb htb
  · exact bits32 σ h tb htb
  · exact bits33 σ h tb htb
  · exact bits34 σ h tb htb
  · exact bits35 σ h tb htb
  · exact bits36 σ h tb htb
  · exact bits37 σ h tb htb
  · exact bits38 σ h tb htb
  · exact bits39 σ h tb htb
  · exact bits40 σ h tb htb
  · exact bits41 σ h tb htb
  · exact bits42 σ h tb htb
  · exact bits43 σ h tb htb
  · exact bits44 σ h tb htb
  · exact bits45 σ h tb htb
  · exact bits46 σ h tb htb
  · exact bits47 σ h tb htb
  · exact bits48 σ h tb htb
  · exact bits49 σ h tb htb
  · exact bits50 σ h tb htb
  · exact bits51 σ h tb htb
  · exact bits52 σ h tb htb
  · exact bits53 σ h tb htb
  · exact bits54 σ h tb htb
  · exact bits55 σ h tb htb
  · exact bits56 σ h tb htb
  · exact bits57 σ h tb htb
  · exact bits58 σ h tb htb
  · exact bits59 σ h tb htb
  · exact bits60 σ h tb htb
  · exact bits61 σ h tb htb
  · exact bits62 σ h tb htb
  · exact bits63 σ h tb htb
  · exact bits64 σ h tb htb
  · exact bits65 σ h tb htb
  · exact bits66 σ h tb htb
  · exact bits67 σ h tb htb
  · exact bits68 σ h tb htb
  · exact bits69 σ h tb htb
  · exact bits70 σ h tb htb
  · exact bits71 σ h tb htb
  · exact bits72 σ h tb htb
  · exact bits73 σ h tb htb
  · exact bits74 σ h tb htb
  · exact bits75 σ h tb htb
  · exact bits76 σ h tb htb
  · exact bits77 σ h tb htb
  · exact bits78 σ h tb htb
  · exact bits79 σ h tb htb
  · exact bits80 σ h tb htb
  · exact bits81 σ h tb htb
  · exact bits82 σ h tb htb
  · exact bits83 σ h tb htb
  · exact bits84 σ h tb htb
  · exact bits85 σ h tb htb
  · exact bits86 σ h tb htb
  · exact bits87 σ h tb htb
  · exact bits88 σ h tb htb
  · exact bits89 σ h tb htb
  · exact bits90 σ h tb htb
  · exact bits91 σ h tb htb
  · exact bits92 σ h tb htb
  · exact bits93 σ h tb htb
  · exact bits94 σ h tb htb
  · exact bits95 σ h tb htb
  · exact bits96 σ h tb htb
  · exact bits97 σ h tb htb
  · exact bits98 σ h tb htb
  · exact bits99 σ h tb htb
  · exact bits100 σ h tb htb
  · exact bits101 σ h tb htb
  · exact bits102 σ h tb htb
  · exact bits103 σ h tb htb
  · exact bits104 σ h tb htb
  · exact bits105 σ h tb htb
  · exact bits106 σ h tb htb
  · exact bits107 σ h tb htb
  · exact bits108 σ h tb htb
  · exact bits109 σ h tb htb
  · exact bits110 σ h tb htb
  · exact bits111 σ h tb htb
  · exact bits112 σ h tb htb
  · exact bits113 σ h tb htb
  · exact bits114 σ h tb htb
  · exact bits115 σ h tb htb
  · exact bits116 σ h tb htb
  · exact bits117 σ h tb htb
  · exact bits118 σ h tb htb
  · exact bits119 σ h tb htb
  · exact bits120 σ h tb htb
  · exact bits121 σ h tb htb
  · exact bits122 σ h tb htb
  · exact bits123 σ h tb htb
  · exact bits124 σ h tb htb
  · exact bits125 σ h tb htb
  · exact bits126 σ h tb htb
  · exact bits127 σ h tb htb
  · exact bits128 σ h tb htb
  · exact bits129 σ h tb htb
  · exact bits130 σ h tb htb
  · exact bits131 σ h tb htb
  · exact bits132 σ h tb htb
  · exact bits133 σ h tb htb
  · exact bits134 σ h tb htb
  · exact bits135 σ h tb htb
  · exact bits136 σ h tb htb
  · exact bits137 σ h tb htb
  · exact bits138 σ h tb htb
  · exact bits139 σ h tb htb
  · exact bits140 σ h tb htb
  · exact bits141 σ h tb htb
  · exact bits142 σ h tb htb
  · exact bits143 σ h tb htb
  · exact bits144 σ h tb htb
  · exact bits145 σ h tb htb
  · exact bits146 σ h tb htb
  · exact bits147 σ h tb htb
  · exact bits148 σ h tb htb
  · exact bits149 σ h tb htb
  · exact bits150 σ h tb htb
  · exact bits151 σ h tb htb
  · exact bits152 σ h tb htb
  · exact bits153 σ h tb htb
  · exact bits154 σ h tb htb
  · exact bits155 σ h tb htb
  · exact bits156 σ h tb htb
  · exact bits157 σ h tb htb
  · exact bits158 σ h tb htb
  · exact bits159 σ h tb htb
  · exact bits160 σ h tb htb
  · exact bits161 σ h tb htb
  · exact bits162 σ h tb htb
  · exact bits163 σ h tb htb
  · exact bits164 σ h tb htb
  · exact bits165 σ h tb htb
  · exact bits166 σ h tb htb
  · exact bits167 σ h tb htb
  · exact bits168 σ h tb htb
  · exact bits169 σ h tb htb
  · exact bits170 σ h tb htb
  · exact bits171 σ h tb htb
  · exact bits172 σ h tb htb
  · exact bits173 σ h tb htb
  · exact bits174 σ h tb htb
  · exact bits175 σ h tb htb
  · exact bits176 σ h tb htb
  · exact bits177 σ h tb htb
  · exact bits178 σ h tb htb
  · exact bits179 σ h tb htb
  · exact bits180 σ h tb htb
  · exact bits181 σ h tb htb
  · exact bits182 σ h tb htb
  · exact bits183 σ h tb htb
  · exact bits184 σ h tb htb
  · exact bits185 σ h tb htb
  · exact bits186 σ h tb htb
  · exact bits187 σ h tb htb
  · exact bits188 σ h tb htb
  · exact bits189 σ h tb htb
  · exact bits190 σ h tb htb
  · exact bits191 σ h tb htb
  · exact bits192 σ h tb htb
  · exact bits193 σ h tb htb
  · exact bits194 σ h tb htb
  · exact bits195 σ h tb htb
  · exact bits196 σ h tb htb
  · exact bits197 σ h tb htb
  · exact bits198 σ h tb htb
  · exact bits199 σ h tb htb
  · exact bits200 σ h tb htb
  · exact bits201 σ h tb htb
  · exact bits202 σ h tb htb
  · exact bits203 σ h tb htb
  · exact bits204 σ h tb htb
  · exact bits205 σ h tb htb
  · exact bits206 σ h tb htb
  · exact bits207 σ h tb htb
  · exact bits208 σ h tb htb
  · exact bits209 σ h tb htb
  · exact bits210 σ h tb htb
  · exact bits211 σ h tb htb
  · exact bits212 σ h tb htb
  · exact bits213 σ h tb htb
  · exact bits214 σ h tb htb
  · exact bits215 σ h tb htb
  · exact bits216 σ h tb htb
  · exact bits217 σ h tb htb
  · exact bits218 σ h tb htb
  · exact bits219 σ h tb htb
  · exact bits220 σ h tb htb
  · exact bits221 σ h tb htb
  · exact bits222 σ h tb htb
  · exact bits223 σ h tb htb
  · exact bits224 σ h tb htb
  · exact bits225 σ h tb htb
  · exact bits226 σ h tb htb
  · exact bits227 σ h tb htb
  · exact bits228 σ h tb htb
  · exact bits229 σ h tb htb
  · exact bits230 σ h tb htb
  · exact bits231 σ h tb htb
  · exact bits232 σ h tb htb
  · exact bits233 σ h tb htb
  · exact bits234 σ h tb htb
  · exact bits235 σ h tb htb
  · exact bits236 σ h tb htb
  · exact bits237 σ h tb htb
  · exact bits238 σ h tb htb
  · exact bits239 σ h tb htb
  · exact bits240 σ h tb htb
  · exact bits241 σ h tb htb
  · exact bits242 σ h tb htb
  · exact bits243 σ h tb htb
  · exact bits244 σ h tb htb
  · exact bits245 σ h tb htb
  · exact bits246 σ h tb htb
  · exact bits247 σ h tb htb
  · exact bits248 σ h tb htb
  · exact bits249 σ h tb htb
  · exact bits250 σ h tb htb
  · exact bits251 σ h tb htb
  · exact bits252 σ h tb htb
  · exact bits253 σ h tb htb
  · exact bits254 σ h tb htb
  · exact bits255 σ h tb htb
  · exact bits256 σ h tb htb
  · exact bits257 σ h tb htb
  · exact bits258 σ h tb htb
  · exact bits259 σ h tb htb
  · exact bits260 σ h tb htb
  · exact bits261 σ h tb htb
  · exact bits262 σ h tb htb
  · exact bits263 σ h tb htb
  · exact bits264 σ h tb htb
  · exact bits265 σ h tb htb
  · exact bits266 σ h tb htb
  · exact bits267 σ h tb htb
  · exact bits268 σ h tb htb
  · exact bits269 σ h tb htb
  · exact bits270 σ h tb htb
  · exact bits271 σ h tb htb
  · exact bits272 σ h tb htb
  · exact bits273 σ h tb htb
  · exact bits274 σ h tb htb
  · exact bits275 σ h tb htb
  · exact bits276 σ h tb htb
  · exact bits277 σ h tb htb
  · exact bits278 σ h tb htb
  · exact bits279 σ h tb htb
  · exact bits280 σ h tb htb
  · exact bits281 σ h tb htb
  · exact bits282 σ h tb htb
  · exact bits283 σ h tb htb
  · exact bits284 σ h tb htb
  · exact bits285 σ h tb htb
  · exact bits286 σ h tb htb
  · exact bits287 σ h tb htb
  · exact bits288 σ h tb htb
  · exact bits289 σ h tb htb
  · exact bits290 σ h tb htb
  · exact bits291 σ h tb htb
  · exact bits292 σ h tb htb
  · exact bits293 σ h tb htb
  · exact bits294 σ h tb htb
  · exact bits295 σ h tb htb
  · exact bits296 σ h tb htb
  · exact bits297 σ h tb htb
  · exact bits298 σ h tb htb
  · exact bits299 σ h tb htb
  · exact bits300 σ h tb htb
  · exact bits301 σ h tb htb
  · exact bits302 σ h tb htb
  · exact bits303 σ h tb htb
  · exact bits304 σ h tb htb
  · exact bits305 σ h tb htb
  · exact bits306 σ h tb htb
  · exact bits307 σ h tb htb
  · exact bits308 σ h tb htb
  · exact bits309 σ h tb htb
  · exact bits310 σ h tb htb
  · exact bits311 σ h tb htb
  · exact bits312 σ h tb htb
  · exact bits313 σ h tb htb
  · exact bits314 σ h tb htb
  · exact bits315 σ h tb htb
  · exact bits316 σ h tb htb
  · exact bits317 σ h tb htb
  · exact bits318 σ h tb htb
  · exact bits319 σ h tb htb
  · exact bits320 σ h tb htb
  · exact bits321 σ h tb htb
  · exact bits322 σ h tb htb
  · exact bits323 σ h tb htb
  · exact bits324 σ h tb htb
  · exact bits325 σ h tb htb
  · exact bits326 σ h tb htb
  · exact bits327 σ h tb htb
  · exact bits328 σ h tb htb
  · exact bits329 σ h tb htb
  · exact bits330 σ h tb htb
  · exact bits331 σ h tb htb
  · exact bits332 σ h tb htb
  · exact bits333 σ h tb htb
  · exact bits334 σ h tb htb
  · exact bits335 σ h tb htb
  · exact bits336 σ h tb htb
  · exact bits337 σ h tb htb
  · exact bits338 σ h tb htb
  · exact bits339 σ h tb htb
  · exact bits340 σ h tb htb
  · exact bits341 σ h tb htb
  · exact bits342 σ h tb htb
  · exact bits343 σ h tb htb
  · exact bits344 σ h tb htb
  · exact bits345 σ h tb htb
  · exact bits346 σ h tb htb
  · exact bits347 σ h tb htb
  · exact bits348 σ h tb htb
  · exact bits349 σ h tb htb
  · exact bits350 σ h tb htb
  · exact bits351 σ h tb htb
  · exact bits352 σ h tb htb
  · exact bits353 σ h tb htb
  · exact bits354 σ h tb htb
  · exact bits355 σ h tb htb
  · exact bits356 σ h tb htb
  · exact bits357 σ h tb htb
  · exact bits358 σ h tb htb
  · exact bits359 σ h tb htb
  · exact bits360 σ h tb htb
  · exact bits361 σ h tb htb
  · exact bits362 σ h tb htb
  · exact bits363 σ h tb htb
  · exact bits364 σ h tb htb
  · exact bits365 σ h tb htb
  · exact bits366 σ h tb htb
  · exact bits367 σ h tb htb
  · exact bits368 σ h tb htb
  · exact bits369 σ h tb htb
  · exact bits370 σ h tb htb
  · exact bits371 σ h tb htb
  · exact bits372 σ h tb htb
  · exact bits373 σ h tb htb
  · exact bits374 σ h tb htb
  · exact bits375 σ h tb htb
  · exact bits376 σ h tb htb
  · exact bits377 σ h tb htb
  · exact bits378 σ h tb htb
  · exact bits379 σ h tb htb
  · exact bits380 σ h tb htb
  · exact bits381 σ h tb htb
  · exact bits382 σ h tb htb
  · exact bits383 σ h tb htb
  · exact bits384 σ h tb htb
  · exact bits385 σ h tb htb
  · exact bits386 σ h tb htb
  · exact bits387 σ h tb htb
  · exact bits388 σ h tb htb
  · exact bits389 σ h tb htb
  · exact bits390 σ h tb htb
  · exact bits391 σ h tb htb
  · exact bits392 σ h tb htb
  · exact bits393 σ h tb htb
  · exact bits394 σ h tb htb
  · exact bits395 σ h tb htb
  · exact bits396 σ h tb htb
  · exact bits397 σ h tb htb
  · exact bits398 σ h tb htb
  · exact bits399 σ h tb htb
  · exact bits400 σ h tb htb
  · exact bits401 σ h tb htb
  · exact bits402 σ h tb htb
  · exact bits403 σ h tb htb
  · exact bits404 σ h tb htb
  · exact bits405 σ h tb htb
  · exact bits406 σ h tb htb
  · exact bits407 σ h tb htb
  · exact bits408 σ h tb htb
  · exact bits409 σ h tb htb
  · exact bits410 σ h tb htb
  · exact bits411 σ h tb htb
  · exact bits412 σ h tb htb
  · exact bits413 σ h tb htb
  · exact bits414 σ h tb htb
  · exact bits415 σ h tb htb
  · exact bits416 σ h tb htb
  · exact bits417 σ h tb htb
  · exact bits418 σ h tb htb
  · exact bits419 σ h tb htb
  · exact bits420 σ h tb htb
  · exact bits421 σ h tb htb
  · exact bits422 σ h tb htb
  · exact bits423 σ h tb htb
  · exact bits424 σ h tb htb
  · exact bits425 σ h tb htb
  · exact bits426 σ h tb htb
  · exact bits427 σ h tb htb
  · exact bits428 σ h tb htb
  · exact bits429 σ h tb htb
  · exact bits430 σ h tb htb
  · exact bits431 σ h tb htb
  · exact bits432 σ h tb htb
  · exact bits433 σ h tb htb
  · exact bits434 σ h tb htb
  · exact bits435 σ h tb htb
  · exact bits436 σ h tb htb
  · exact bits437 σ h tb htb
  · exact bits438 σ h tb htb
  · exact bits439 σ h tb htb
  · exact bits440 σ h tb htb
  · exact bits441 σ h tb htb
  · exact bits442 σ h tb htb
  · exact bits443 σ h tb htb
  · exact bits444 σ h tb htb
  · exact bits445 σ h tb htb
  · exact bits446 σ h tb htb
  · exact bits447 σ h tb htb
  · exact bits448 σ h tb htb
  · exact bits449 σ h tb htb
  · exact bits450 σ h tb htb
  · exact bits451 σ h tb htb
  · exact bits452 σ h tb htb
  · exact bits453 σ h tb htb
  · exact bits454 σ h tb htb
  · exact bits455 σ h tb htb
  · exact bits456 σ h tb htb
  · exact bits457 σ h tb htb
  · exact bits458 σ h tb htb
  · exact bits459 σ h tb htb
  · exact bits460 σ h tb htb
  · exact bits461 σ h tb htb
  · exact bits462 σ h tb htb
  · exact bits463 σ h tb htb
  · exact bits464 σ h tb htb
  · exact bits465 σ h tb htb
  · exact bits466 σ h tb htb
  · exact bits467 σ h tb htb
  · exact bits468 σ h tb htb
  · exact bits469 σ h tb htb
  · exact bits470 σ h tb htb
  · exact bits471 σ h tb htb
  · exact bits472 σ h tb htb
  · exact bits473 σ h tb htb
  · exact bits474 σ h tb htb
  · exact bits475 σ h tb htb
  · exact bits476 σ h tb htb
  · exact bits477 σ h tb htb
  · exact bits478 σ h tb htb
  · exact bits479 σ h tb htb
  · exact bits480 σ h tb htb
  · exact bits481 σ h tb htb
  · exact bits482 σ h tb htb
  · exact bits483 σ h tb htb
  · exact bits484 σ h tb htb
  · exact bits485 σ h tb htb
  · exact bits486 σ h tb htb
  · exact bits487 σ h tb htb
  · exact bits488 σ h tb htb
  · exact bits489 σ h tb htb
  · exact bits490 σ h tb htb
  · exact bits491 σ h tb htb
  · exact bits492 σ h tb htb
  · exact bits493 σ h tb htb
  · exact bits494 σ h tb htb
  · exact bits495 σ h tb htb
  · exact bits496 σ h tb htb
  · exact bits497 σ h tb htb
  · exact bits498 σ h tb htb
  · exact bits499 σ h tb htb
  · exact bits500 σ h tb htb
  · exact bits501 σ h tb htb
  · exact bits502 σ h tb htb
  · exact bits503 σ h tb htb
  · exact bits504 σ h tb htb
  · exact bits505 σ h tb htb
  · exact bits506 σ h tb htb
  · exact bits507 σ h tb htb
  · exact bits508 σ h tb htb
  · exact bits509 σ h tb htb
  · exact bits510 σ h tb htb
  · exact bits511 σ h tb htb
  · exact bits512 σ h tb htb
  · exact bits513 σ h tb htb
  · exact bits514 σ h tb htb
  · exact bits515 σ h tb htb
  · exact bits516 σ h tb htb
  · exact bits517 σ h tb htb
  · exact bits518 σ h tb htb
  · exact bits519 σ h tb htb
  · exact bits520 σ h tb htb
  · exact bits521 σ h tb htb
  · exact bits522 σ h tb htb
  · exact bits523 σ h tb htb
  · exact bits524 σ h tb htb
  · exact bits525 σ h tb htb
  · exact bits526 σ h tb htb
  · exact bits527 σ h tb htb
  · exact bits528 σ h tb htb
  · exact bits529 σ h tb htb
  · exact bits530 σ h tb htb
  · exact bits531 σ h tb htb
  · exact bits532 σ h tb htb
  · exact bits533 σ h tb htb
  · exact bits534 σ h tb htb
  · exact bits535 σ h tb htb
  · exact bits536 σ h tb htb
  · exact bits537 σ h tb htb
  · exact bits538 σ h tb htb
  · exact bits539 σ h tb htb
  · exact bits540 σ h tb htb
  · exact bits541 σ h tb htb
  · exact bits542 σ h tb htb
  · exact bits543 σ h tb htb

end Xark.Circuits.Rsa2048
