/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.Sbox
import Formal.TemplateSolve
import Formal.ToBits

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_aes::sbox`, the AES S-box as a select over its table, proven over its exported rows

The spec is FIPS-197 §5.1.1: `S(x) = A(x⁻¹) ⊕ 0x63` with `x⁻¹` the inverse in
`GF(2⁸) = GF(2)[x]/(x⁸ + x⁴ + x³ + x + 1)` (`0⁻¹ = 0`) and `A` the affine map
`bᵢ ⊕ bᵢ₊₄ ⊕ bᵢ₊₅ ⊕ bᵢ₊₆ ⊕ bᵢ₊₇` (indices mod 8): `Xark.Aes.sbox`. `table_eq` proves the
256-byte table the gadget selects from is that map.

The gadget's 34 rows (`Formal/Templates/Sbox.lean`): 26 products (2 pair products and 9
grid products for the one-hot `lo` of the low nibble, 15 for the binary mux over the high
nibble on the constant combinations `Σₗ SBOX[16h + l]·lo[l]`), then `to_bits::<8>` of the
selected byte `sel` (7 boolean rows and its low row).

* `rows_eq`, `hints_eq`, `outputs_eq`, `inputs_eq`: the export is that shape, by
  `decide +kernel`.
* `agree`: the product rows pin each product variable to a function of the plugs, so any
  two assignments satisfying them with the same input bits agree on them.
* `sel_table`: on each of the 256 bytes, `sel` is the table entry (`decide +kernel`, in
  chunks of sixteen bytes: one chunk per declaration keeps the kernel's memory small).
* `one_hot`: on bit inputs, the 16 selectors `lo` of every satisfying assignment are
  `1` at the low nibble and `0` elsewhere, and sum to `1` (bug checklist 10).
* `soundness`: on bit plugs (the callers' `to_bits` and `xor` outputs: `lean-export
  --coverage` discharges `Assumptions`), every satisfying assignment outputs the bits of
  `S(Σᵢ 2ⁱbᵢ)`.
-/

namespace Xark.Aes

/-- The carry-less product of two bytes: their product in `GF(2)[x]`. -/
def clmul (a b : ℕ) : ℕ :=
  (List.range 8).foldl (fun p i => if b.testBit i then p ^^^ (a <<< i) else p) 0

/-- A polynomial of degree at most 14 reduced modulo `m(x) = x⁸ + x⁴ + x³ + x + 1`
(`0x11B`), highest degree first. -/
def reduce (p : ℕ) : ℕ :=
  (List.range 7).reverse.foldl (fun p i => if p.testBit (i + 8) then p ^^^ (0x11B <<< i) else p) p

/-- The product in `GF(2⁸)`. -/
def gmul (a b : ℕ) : ℕ := reduce (clmul a b)

/-- The inverse in `GF(2⁸)`: the byte `y` with `a · y = 1`, and `0` for `a = 0`. -/
def ginv (a : ℕ) : ℕ := ((List.range 256).find? fun y => gmul a y = 1).getD 0

/-- A byte rotated left by `s < 8`: bit `i` of the result is bit `i − s` (mod 8). -/
def rotl (b s : ℕ) : ℕ := ((b <<< s) ||| (b >>> (8 - s))) % 256

/-- The S-box's affine map: bit `i` is `bᵢ ⊕ bᵢ₋₁ ⊕ bᵢ₋₂ ⊕ bᵢ₋₃ ⊕ bᵢ₋₄ ⊕ cᵢ` (mod 8,
FIPS-197 (5.1) with `bᵢ₊₄ = bᵢ₋₄`, …), `c = 0x63`. -/
def affine (b : ℕ) : ℕ := b ^^^ rotl b 1 ^^^ rotl b 2 ^^^ rotl b 3 ^^^ rotl b 4 ^^^ 0x63

/-- The S-box. -/
def sbox (x : ℕ) : ℕ := affine (ginv x)

/-- The table `xark_aes::SBOX` (FIPS-197 Figure 7). -/
def table : List ℕ := [
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

/-- `∀ v < 16·n, P v` from `n` chunks of sixteen. Each chunk below is its own
`decide +kernel` declaration: the kernel's working set is one chunk's (a whole table in one
`decide +kernel` needed 14 to 22 GB). -/
theorem forall_lt_of_chunks {P : ℕ → Prop} (n : ℕ) (h : ∀ i < n, ∀ j < 16, P (16 * i + j)) :
    ∀ v < 16 * n, P v := fun v hv => by
  have := h (v / 16) (by omega) (v % 16) (by omega)
  rwa [Nat.div_add_mod] at this

section kernel
set_option maxRecDepth 100000

private theorem gmul_ginv_0 :
    ∀ j < 16, (16 * 0 + j) ≠ 0 → gmul (16 * 0 + j) (ginv (16 * 0 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_1 :
    ∀ j < 16, (16 * 1 + j) ≠ 0 → gmul (16 * 1 + j) (ginv (16 * 1 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_2 :
    ∀ j < 16, (16 * 2 + j) ≠ 0 → gmul (16 * 2 + j) (ginv (16 * 2 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_3 :
    ∀ j < 16, (16 * 3 + j) ≠ 0 → gmul (16 * 3 + j) (ginv (16 * 3 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_4 :
    ∀ j < 16, (16 * 4 + j) ≠ 0 → gmul (16 * 4 + j) (ginv (16 * 4 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_5 :
    ∀ j < 16, (16 * 5 + j) ≠ 0 → gmul (16 * 5 + j) (ginv (16 * 5 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_6 :
    ∀ j < 16, (16 * 6 + j) ≠ 0 → gmul (16 * 6 + j) (ginv (16 * 6 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_7 :
    ∀ j < 16, (16 * 7 + j) ≠ 0 → gmul (16 * 7 + j) (ginv (16 * 7 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_8 :
    ∀ j < 16, (16 * 8 + j) ≠ 0 → gmul (16 * 8 + j) (ginv (16 * 8 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_9 :
    ∀ j < 16, (16 * 9 + j) ≠ 0 → gmul (16 * 9 + j) (ginv (16 * 9 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_10 :
    ∀ j < 16, (16 * 10 + j) ≠ 0 → gmul (16 * 10 + j) (ginv (16 * 10 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_11 :
    ∀ j < 16, (16 * 11 + j) ≠ 0 → gmul (16 * 11 + j) (ginv (16 * 11 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_12 :
    ∀ j < 16, (16 * 12 + j) ≠ 0 → gmul (16 * 12 + j) (ginv (16 * 12 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_13 :
    ∀ j < 16, (16 * 13 + j) ≠ 0 → gmul (16 * 13 + j) (ginv (16 * 13 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_14 :
    ∀ j < 16, (16 * 14 + j) ≠ 0 → gmul (16 * 14 + j) (ginv (16 * 14 + j)) = 1 := by
  decide +kernel
private theorem gmul_ginv_15 :
    ∀ j < 16, (16 * 15 + j) ≠ 0 → gmul (16 * 15 + j) (ginv (16 * 15 + j)) = 1 := by
  decide +kernel
private theorem table_eq_0 :
    ∀ j < 16, table.getD (16 * 0 + j) 0 = sbox (16 * 0 + j) := by
  decide +kernel
private theorem table_eq_1 :
    ∀ j < 16, table.getD (16 * 1 + j) 0 = sbox (16 * 1 + j) := by
  decide +kernel
private theorem table_eq_2 :
    ∀ j < 16, table.getD (16 * 2 + j) 0 = sbox (16 * 2 + j) := by
  decide +kernel
private theorem table_eq_3 :
    ∀ j < 16, table.getD (16 * 3 + j) 0 = sbox (16 * 3 + j) := by
  decide +kernel
private theorem table_eq_4 :
    ∀ j < 16, table.getD (16 * 4 + j) 0 = sbox (16 * 4 + j) := by
  decide +kernel
private theorem table_eq_5 :
    ∀ j < 16, table.getD (16 * 5 + j) 0 = sbox (16 * 5 + j) := by
  decide +kernel
private theorem table_eq_6 :
    ∀ j < 16, table.getD (16 * 6 + j) 0 = sbox (16 * 6 + j) := by
  decide +kernel
private theorem table_eq_7 :
    ∀ j < 16, table.getD (16 * 7 + j) 0 = sbox (16 * 7 + j) := by
  decide +kernel
private theorem table_eq_8 :
    ∀ j < 16, table.getD (16 * 8 + j) 0 = sbox (16 * 8 + j) := by
  decide +kernel
private theorem table_eq_9 :
    ∀ j < 16, table.getD (16 * 9 + j) 0 = sbox (16 * 9 + j) := by
  decide +kernel
private theorem table_eq_10 :
    ∀ j < 16, table.getD (16 * 10 + j) 0 = sbox (16 * 10 + j) := by
  decide +kernel
private theorem table_eq_11 :
    ∀ j < 16, table.getD (16 * 11 + j) 0 = sbox (16 * 11 + j) := by
  decide +kernel
private theorem table_eq_12 :
    ∀ j < 16, table.getD (16 * 12 + j) 0 = sbox (16 * 12 + j) := by
  decide +kernel
private theorem table_eq_13 :
    ∀ j < 16, table.getD (16 * 13 + j) 0 = sbox (16 * 13 + j) := by
  decide +kernel
private theorem table_eq_14 :
    ∀ j < 16, table.getD (16 * 14 + j) 0 = sbox (16 * 14 + j) := by
  decide +kernel
private theorem table_eq_15 :
    ∀ j < 16, table.getD (16 * 15 + j) 0 = sbox (16 * 15 + j) := by
  decide +kernel
private theorem table_lt_0 :
    ∀ j < 16, table.getD (16 * 0 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_1 :
    ∀ j < 16, table.getD (16 * 1 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_2 :
    ∀ j < 16, table.getD (16 * 2 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_3 :
    ∀ j < 16, table.getD (16 * 3 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_4 :
    ∀ j < 16, table.getD (16 * 4 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_5 :
    ∀ j < 16, table.getD (16 * 5 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_6 :
    ∀ j < 16, table.getD (16 * 6 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_7 :
    ∀ j < 16, table.getD (16 * 7 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_8 :
    ∀ j < 16, table.getD (16 * 8 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_9 :
    ∀ j < 16, table.getD (16 * 9 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_10 :
    ∀ j < 16, table.getD (16 * 10 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_11 :
    ∀ j < 16, table.getD (16 * 11 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_12 :
    ∀ j < 16, table.getD (16 * 12 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_13 :
    ∀ j < 16, table.getD (16 * 13 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_14 :
    ∀ j < 16, table.getD (16 * 14 + j) 0 < 256 := by
  decide +kernel
private theorem table_lt_15 :
    ∀ j < 16, table.getD (16 * 15 + j) 0 < 256 := by
  decide +kernel

end kernel

/-- Every nonzero byte has an inverse: `ginv` is the field inverse (FIPS-197 §4.2). -/
theorem gmul_ginv : ∀ a < 256, a ≠ 0 → gmul a (ginv a) = 1 :=
  forall_lt_of_chunks 16 fun i hi => by
    interval_cases i
    exacts [gmul_ginv_0, gmul_ginv_1, gmul_ginv_2, gmul_ginv_3, gmul_ginv_4, gmul_ginv_5,
      gmul_ginv_6, gmul_ginv_7, gmul_ginv_8, gmul_ginv_9, gmul_ginv_10, gmul_ginv_11, gmul_ginv_12,
      gmul_ginv_13, gmul_ginv_14, gmul_ginv_15]

/-- **The table is the S-box**: entry `x` is `A(x⁻¹) ⊕ 0x63`. -/
theorem table_eq : ∀ x < 256, table.getD x 0 = sbox x :=
  forall_lt_of_chunks 16 fun i hi => by
    interval_cases i
    exacts [table_eq_0, table_eq_1, table_eq_2, table_eq_3, table_eq_4, table_eq_5, table_eq_6,
      table_eq_7, table_eq_8, table_eq_9, table_eq_10, table_eq_11, table_eq_12, table_eq_13,
      table_eq_14, table_eq_15]

theorem table_lt : ∀ x < 256, table.getD x 0 < 256 :=
  forall_lt_of_chunks 16 fun i hi => by
    interval_cases i
    exacts [table_lt_0, table_lt_1, table_lt_2, table_lt_3, table_lt_4, table_lt_5, table_lt_6,
      table_lt_7, table_lt_8, table_lt_9, table_lt_10, table_lt_11, table_lt_12, table_lt_13,
      table_lt_14, table_lt_15]

end Xark.Aes

namespace Xark.Templates.Sbox

open Xark.Template Xark.R1cs Finset
open Xark.Templates.Add32 (IsBit isBit_val sum_map_range testBit_word
  word_lt bit_eq_testBit)

/-! ### The exported rows -/

/-- The operands of product hint `k`. -/
def opnd (k : ℕ) : LC × LC :=
  match template.hints.getD k (.linear 0 (LC.cst 0)) with
  | .product _ a b => (a, b)
  | _ => (LC.cst 0, LC.cst 0)

/-- The selected byte, which the `to_bits` hints decompose. -/
def sel : LC :=
  match template.hints.getD 26 (.linear 0 (LC.cst 0)) with
  | .bit _ l _ => l
  | _ => LC.cst 0

/-- Bit 0 of the selected byte: what the hinted bits `1..7` leave of it. -/
def low : LC :=
  ⟨sel.const, sel.terms ++ (List.range 7).map fun i => (-((2 ^ (i + 1) : ℕ) : F), .wit (26 + i))⟩

def boolRow (w : ℕ) : Row := ⟨LC.var (.wit w), LC.var (.wit w), LC.var (.wit w)⟩

def modelRows : List Row :=
  (List.range 26).map (fun k => ⟨(opnd k).1, (opnd k).2, LC.var (.wit k)⟩) ++
    (List.range 7).map (fun i => boolRow (26 + i)) ++ [⟨low, ⟨low.const - 1, low.terms⟩, ⟨0, []⟩⟩]

def modelHints : List Hint :=
  (List.range 26).map (fun k => .product k (opnd k).1 (opnd k).2) ++
    (List.range 7).map fun i => .bit (26 + i) sel (i + 1)

theorem rows_eq : template.rows = modelRows := by decide +kernel
theorem hints_eq : template.hints = modelHints := by decide +kernel
theorem outputs_eq :
    template.outputs = low :: (List.range 7).map fun i => LC.var (.wit (26 + i)) := by
  decide +kernel
theorem inputs_eq : template.inputs = (List.range 8).map fun j => LC.var (.plug j) := by
  decide +kernel
theorem ordered_hints : ordered 0 template.hints = true := by decide +kernel

/-- `l` reads only plugs below `p` and variables below `k`. -/
def readsBelow (p k : ℕ) (l : LC) : Bool :=
  l.terms.all fun t => match t.2 with
    | .plug j => decide (j < p)
    | .wit w => decide (w < k)

/-- Each product reads the 8 plugs and earlier products; the 11 of the one-hot read only
the low nibble's plugs. -/
theorem opnd_reads : ∀ k < 26, readsBelow 8 k (opnd k).1 ∧ readsBelow 8 k (opnd k).2 := by
  decide +kernel
theorem opnd_reads_low : ∀ k < 11, readsBelow 4 k (opnd k).1 ∧ readsBelow 4 k (opnd k).2 := by
  decide +kernel
theorem sel_reads : readsBelow 8 26 sel = true := by decide +kernel

theorem eval_reads {p k : ℕ} {l : LC} (hl : readsBelow p k l = true) {σ τ : TVar → F}
    (hp : ∀ j < p, σ (.plug j) = τ (.plug j)) (hw : ∀ w < k, σ (.wit w) = τ (.wit w)) :
    l.eval σ = l.eval τ := by
  refine eval_congr fun t ht => ?_
  have := List.all_eq_true.mp hl t ht
  rcases t with ⟨c, v⟩
  cases v with
  | plug j => exact hp j (by simpa using this)
  | wit w => exact hw w (by simpa using this)

/-- The product rows `k < K` hold under `σ`. -/
def ProdSat (K : ℕ) (σ : TVar → F) : Prop :=
  ∀ k < K, (opnd k).1.eval σ * (opnd k).2.eval σ = σ (.wit k)

/-- **The products have no freedom.** Two assignments satisfying the product rows below
`K`, with the same plugs below `p`, agree on every product below `K`, when those rows read
only plugs below `p` (`p = 4, K = 11`: the one-hot; `p = 8, K = 26`: every product). -/
theorem agree (p K : ℕ) (hK : ∀ k < K, readsBelow p k (opnd k).1 ∧ readsBelow p k (opnd k).2)
    {σ τ : TVar → F} (hp : ∀ j < p, σ (.plug j) = τ (.plug j)) (hσ : ProdSat K σ)
    (hτ : ProdSat K τ) : ∀ k < K, σ (.wit k) = τ (.wit k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨ha, hb⟩ := hK k hk
    rw [← hσ k hk, ← hτ k hk, eval_reads ha hp fun w hw => ih w hw (by omega),
      eval_reads hb hp fun w hw => ih w hw (by omega)]

theorem prodSat_of_sat {σ : TVar → F} (h : template.Sat σ) : ProdSat 26 σ := fun k hk => by
  have := h _ (by
    rw [rows_eq, modelRows]
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))
  simpa only [Row.Sat, LC.eval_var] using this

theorem prodSat_solve (x : ℕ → F) : ProdSat 26 (template.solve x) := fun k hk => by
  obtain ⟨o, ho, h⟩ := Xark.Template.Template.solve_hint template x ordered_hints (.product k (opnd k).1 (opnd k).2)
    (by rw [hints_eq, modelHints]; simp only [List.mem_append, List.mem_map, List.mem_range];
        exact Or.inl ⟨k, hk, rfl⟩)
  simp only [Hint.out?, Option.some.injEq] at ho
  subst ho
  exact h.symm

/-! ### The selected byte and the one-hot, on each input -/

/-- Bit `j` of `v`, as a plug value. -/
def bitsOf (v j : ℕ) : F := if v.testBit j then 1 else 0

section kernel
set_option maxRecDepth 100000

private theorem sel_table_0 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 0 + j))) =  ((Aes.table.getD (16 * 0 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_1 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 1 + j))) =  ((Aes.table.getD (16 * 1 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_2 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 2 + j))) =  ((Aes.table.getD (16 * 2 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_3 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 3 + j))) =  ((Aes.table.getD (16 * 3 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_4 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 4 + j))) =  ((Aes.table.getD (16 * 4 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_5 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 5 + j))) =  ((Aes.table.getD (16 * 5 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_6 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 6 + j))) =  ((Aes.table.getD (16 * 6 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_7 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 7 + j))) =  ((Aes.table.getD (16 * 7 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_8 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 8 + j))) =  ((Aes.table.getD (16 * 8 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_9 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 9 + j))) =  ((Aes.table.getD (16 * 9 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_10 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 10 + j))) =  ((Aes.table.getD (16 * 10 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_11 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 11 + j))) =  ((Aes.table.getD (16 * 11 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_12 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 12 + j))) =  ((Aes.table.getD (16 * 12 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_13 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 13 + j))) =  ((Aes.table.getD (16 * 13 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_14 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 14 + j))) =  ((Aes.table.getD (16 * 14 + j) 0 : ℕ) : F) := by decide +kernel
private theorem sel_table_15 : ∀ j < 16, sel.eval (template.solve (bitsOf (16 * 15 + j))) =  ((Aes.table.getD (16 * 15 + j) 0 : ℕ) : F) := by decide +kernel

end kernel

/-- On each byte `v`, the selected byte is `SBOX[v]`. -/
theorem sel_table : ∀ v < 256,
    sel.eval (template.solve (bitsOf v)) = ((Aes.table.getD v 0 : ℕ) : F) :=
  Aes.forall_lt_of_chunks 16 fun i hi => by
    interval_cases i
    exacts [sel_table_0, sel_table_1, sel_table_2, sel_table_3, sel_table_4, sel_table_5,
      sel_table_6, sel_table_7, sel_table_8, sel_table_9, sel_table_10, sel_table_11, sel_table_12,
      sel_table_13, sel_table_14, sel_table_15]

/-- The one-hot pair of `(b₀, b₁)` (`i = b₀ + 2b₁`) and of `(b₂, b₃)`, with `w₀ = b₀b₁` and
`w₁ = b₂b₃`. -/
def pairLC (lo i : ℕ) : LC :=
  match i with
  | 0 => ⟨1, [(-1, .plug lo), (-1, .plug (lo + 1)), (1, .wit (lo / 2))]⟩
  | 1 => ⟨0, [(1, .plug lo), (-1, .wit (lo / 2))]⟩
  | 2 => ⟨0, [(1, .plug (lo + 1)), (-1, .wit (lo / 2))]⟩
  | _ => LC.var (.wit (lo / 2))

def pair (σ : TVar → F) (lo i : ℕ) : F := (pairLC lo i).eval σ

/-- Selector `lo[i + 4j]` of the low nibble, as the gadget forms it from the variables:
the grid product `w_{2+i+3j}` for `i, j < 3`, and what the pair one-hots leave for the last
column and row. -/
def hot (σ : TVar → F) (l : ℕ) : F :=
  let g : ℕ → ℕ → F := fun i j => σ (.wit (2 + i + 3 * j))
  let col : ℕ → F := fun j => pair σ 2 j - (g 0 j + g 1 j + g 2 j)
  let i := l % 4
  let j := l / 4
  if i < 3 ∧ j < 3 then g i j
  else if j < 3 then col j
  else if i < 3 then pair σ 0 i - (g i 0 + g i 1 + g i 2)
  else pair σ 0 3 - (col 0 + col 1 + col 2)

/-- The grid products are the pair one-hots' products, and `w₀`, `w₁` the pairs'. -/
theorem opnd_onehot : opnd 0 = (LC.var (.plug 0), LC.var (.plug 1)) ∧
    opnd 1 = (LC.var (.plug 2), LC.var (.plug 3)) ∧
    ∀ i < 3, ∀ j < 3, opnd (2 + i + 3 * j) = (pairLC 0 i, pairLC 2 j) := by
  decide +kernel

theorem hot_congr {σ τ : TVar → F} (hp : ∀ j < 4, σ (.plug j) = τ (.plug j))
    (hw : ∀ w < 11, σ (.wit w) = τ (.wit w)) : ∀ l < 16, hot σ l = hot τ l := by
  intro l hl
  interval_cases l <;>
    simp [hot, pair, pairLC, LC.var, LC.eval, hp 0 (by norm_num), hp 1 (by norm_num), hp 2 (by norm_num),
      hp 3 (by norm_num), hw 0 (by norm_num), hw 1 (by norm_num), hw 2 (by norm_num),
      hw 3 (by norm_num), hw 4 (by norm_num), hw 5 (by norm_num), hw 6 (by norm_num),
      hw 7 (by norm_num), hw 8 (by norm_num), hw 9 (by norm_num), hw 10 (by norm_num)]

theorem hot_table : ∀ v < 16, ∀ l < 16,
    hot (template.solve (bitsOf v)) l = if l = v then 1 else 0 := by
  decide +kernel

/-! ### Soundness -/

/-- The input assumption: every input is a bit. -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, IsBit v

/-- The byte the inputs spell, `Σᵢ 2ⁱbᵢ`. -/
def byte (ins : List F) : ℕ := ∑ j ∈ range 8, 2 ^ j * (ins.getD j 0).val

/-- The outputs are the 8 bits of `S(Σᵢ 2ⁱbᵢ)`, little-endian. -/
def Spec (ins outs : List F) : Prop :=
  outs = (List.range 8).map fun i => if (Aes.sbox (byte ins)).testBit i then 1 else 0

theorem ins_eq (σ : TVar → F) : template.ins σ = (List.range 8).map fun j => σ (.plug j) := by
  simp [Template.ins, inputs_eq, Function.comp_def]

theorem getD_ins (σ : TVar → F) {j : ℕ} (hj : j < 8) : (template.ins σ).getD j 0 = σ (.plug j) := by
  rw [ins_eq, List.getD_eq_getElem _ _ (by simpa using hj)]; simp

/-- On bit plugs, plug `j` is bit `j` of the byte they spell. -/
theorem plug_bitsOf (σ : TVar → F) (ha : Assumptions (template.ins σ)) :
    byte (template.ins σ) < 256 ∧ ∀ j < 8, σ (.plug j) = bitsOf (byte (template.ins σ)) j := by
  have hb : ∀ j < 8, IsBit (σ (.plug j)) := fun j hj => by
    rw [← getD_ins σ hj]
    exact ha _ (by rw [List.getD_eq_getElem _ _ (by simp [ins_eq]; omega)]; exact List.getElem_mem _)
  have hv : ∀ j < 8, ((template.ins σ).getD j 0).val ≤ 1 := fun j hj => by
    rw [getD_ins σ hj]; exact isBit_val (hb j hj)
  refine ⟨word_lt _ 8 hv, fun j hj => ?_⟩
  refine bit_eq_testBit (hb j hj) ?_
  rw [byte, testBit_word _ 8 hv j hj, getD_ins σ hj]

theorem bitOf_natCast {n : ℕ} (hn : n < 256) (i : ℕ) :
    bitOf (n : F) i = if n.testBit i then 1 else 0 := by
  rw [bitOf, ZMod.val_natCast_of_lt (lt_trans hn (by unfold r; norm_num))]

theorem eval_low (σ : TVar → F) :
    low.eval σ = sel.eval σ - ∑ i ∈ range 7, ((2 ^ (i + 1) : ℕ) : F) * σ (.wit (26 + i)) := by
  simp only [low, LC.eval, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    sum_map_range, neg_mul, Finset.sum_neg_distrib]
  ring

/-- On bit plugs, the selected byte of any assignment satisfying the product rows is
`SBOX[byte]`. -/
theorem sel_eval (σ : TVar → F) (ha : Assumptions (template.ins σ)) (hp : ProdSat 26 σ) :
    sel.eval σ = ((Aes.table.getD (byte (template.ins σ)) 0 : ℕ) : F) := by
  obtain ⟨hlt, hbits⟩ := plug_bitsOf σ ha
  set v := byte (template.ins σ)
  have hplug : ∀ j < 8, σ (.plug j) = template.solve (bitsOf v) (.plug j) := fun j hj => by
    rw [hbits j hj, Xark.Template.Template.solve_plug template _ ordered_hints]
  have hw := agree 8 26 opnd_reads hplug hp (prodSat_solve _)
  rw [eval_reads sel_reads hplug hw, sel_table v hlt]

/-- **Soundness.** On bit inputs, every satisfying assignment outputs the bits of
`S(Σᵢ 2ⁱbᵢ)`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  have hsel := sel_eval σ ha (prodSat_of_sat h)
  have hlt := (plug_bitsOf σ ha).1
  set v := byte (template.ins σ)
  have hrow : ∀ r ∈ modelRows, r.Sat σ := fun r hr => h r (by rw [rows_eq]; exact hr)
  -- The decomposition rows, as `to_bits`' model rows on `σ'`.
  let σ' : TVar → F := fun
    | .plug _ => sel.eval σ
    | .wit i => σ (.wit (26 + i))
  have hlow : (ToBits.lowLC 7).eval σ' = low.eval σ := by
    rw [ToBits.eval_lowLC, eval_low]
  have hs : Xark.R1cs.Sat (ToBits.modelRows 7) σ' := by
    rw [ToBits.sat_iff]
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hrow (boolRow (26 + i)) (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))))
      simpa [Row.Sat, boolRow] using this
    · have := hrow _ (List.mem_append.mpr (.inr (List.mem_singleton_self _)))
      simp only [Row.Sat, LC.eval, List.map_nil, List.sum_nil, add_zero] at this
      rw [hlow]
      simp only [LC.eval] at this ⊢
      linear_combination this
  obtain ⟨-, hout⟩ := ToBits.model_sound 7 (by norm_num) σ' hs
  have houts : template.outs σ = (ToBits.modelOutputs 7).map (·.eval σ') := by
    simp [Template.outs, outputs_eq, ToBits.modelOutputs, hlow, σ']
  rw [Spec, houts, hout, ← Aes.table_eq _ hlt]
  refine List.map_congr_left fun i _ => ?_
  simp only [σ']
  rw [hsel, bitOf_natCast (Aes.table_lt _ hlt)]

/-- What `Spec` outputs are bits: a producer of bits for the calls it feeds
(`lean-export --coverage`, "assumptions discharged by producer"). -/
theorem outs_isBit {ins outs : List F} (h : Spec ins outs) : ∀ v ∈ outs, IsBit v := by
  rw [h]
  intro v hv
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **The one-hot.** On bit inputs, every satisfying assignment's 16 selectors of the low
nibble `l = b₀ + 2b₁ + 4b₂ + 8b₃` are `1` at `l` and `0` elsewhere, so they sum to `1`. -/
theorem one_hot (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    (∀ l < 16, hot σ l = if l = byte (template.ins σ) % 16 then 1 else 0) ∧
      ∑ l ∈ range 16, hot σ l = 1 := by
  obtain ⟨hlt, hbits⟩ := plug_bitsOf σ ha
  obtain ⟨v, hv⟩ : ∃ v, v = byte (template.ins σ) % 16 := ⟨_, rfl⟩
  have hplug : ∀ j < 4, σ (.plug j) = template.solve (bitsOf v) (.plug j) := fun j hj => by
    rw [hbits j (by omega), Xark.Template.Template.solve_plug template _ ordered_hints, bitsOf,
      bitsOf, hv, show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.testBit_mod_two_pow]
    simp [hj]
  have hw := agree 4 11 opnd_reads_low hplug
    (fun k hk => prodSat_of_sat h k (by omega)) (fun k hk => prodSat_solve _ k (by omega))
  have hhot := hot_congr hplug hw
  have hl : ∀ l < 16, hot σ l = if l = v then 1 else 0 := fun l hl => by
    rw [hhot l hl, hot_table v (by rw [hv]; exact Nat.mod_lt _ (by norm_num)) l hl]
  refine ⟨fun l h => hv ▸ hl l h, ?_⟩
  rw [Finset.sum_congr rfl fun l h => hl l (Finset.mem_range.mp h), Finset.sum_ite_eq']
  simp [hv, Nat.mod_lt]

end Xark.Templates.Sbox
