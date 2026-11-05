/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.MulCertK1
import Formal.MulCertR1
import Formal.Secp256k1Group

set_option linter.style.header false
set_option linter.style.longLine false
set_option exponentiation.threshold 600

/-!
# `xark_bignum::mul_cert_k1`, proven over its exported rows

`mul_cert_k1(a, b, t)` asserts `a·b ≡ t (mod p)` for secp256k1's `p = 2²⁵⁶ − c`,
`c = 2³² + 977`, over 8 × 32-bit limb vectors whose limbs may be unreduced (below `2³⁴`).
The limb products come from `mul_cert_r1`'s 15 rows `A(ωᵢ)·B(ωᵢ)` at small points; the
columns `2³²ᵐ` fold mod `Y⁸ − Y − 977` (`= p` at `Y = 2³²`) and split after the sixth word,
`ℓₘ + 2¹⁹²·hₘ ≡ 2³²ᵐ (mod p)`, so `E = L + 2¹⁹²·H ≡ a·b − t`:

```text
  Pᵢ = A(ωᵢ)·B(ωᵢ)                         i < 15                 (15 rows)
  L = Σ LOᵢ·Pᵢ − Σ_{k<6} 2³²ᵏ·tₖ,  H = Σ HIᵢ·Pᵢ − t₆ − 2³²·t₇     (linear)
  K + 8 = q < 2⁴⁰,  T + 8 < 2⁴⁷,  T = 2⁶⁴·K − H                     (85 rows)
  L + c·K = 2¹⁹²·T                                                   (1 row)
```

`q = ⌊(H + 2⁶³ + 2⁶⁷)/2⁶⁴⌋` is the hinted quotient. Since `p = 2²⁵⁶ − c`, the last row with
the two range checks says `E = K·p` over the integers (`int_sound`; every field equation
stays below `2²⁵³`, the no-wrap bound, bug checklist 5). The rows are the model below
(`rows_eq`, …, by `decide +kernel`).

* `soundness`: if every limb of `a`, `b`, `t` is below `2³⁴`, every assignment satisfying the
  rows has `a·b ≡ t (mod p)`. The callers enforce the bound (`Formal/EcK1Check.lean`'s
  operand bounds `lo_hi`; `ecdsa_verify_packed`'s `phi_x` and final comparison by their own
  range rows, `formal/coverage-allowlist.txt`).
-/

namespace Xark.Templates.MulCertK1

open Xark.Template Xark.R1cs
open Xark.Templates.EcK1Check (norm eval_norm)
open Xark.Templates.MulCertR1 (pt ZL ZL.lc ZL.neg aZL bZL ec map_ec prod_eval num8 num8_mul
  sum_bd cnt cnt_eq S eval_lc S_append S_scale S_neg S_range eval_a eval_b wit_eq vand_F vZ
  cast_vZ Av Bv Tv ec_cast num8_congr)

/-- `L`'s and `H`'s coefficients of the products. -/
def LO (i : ℕ) : ℤ := ([1185733791817175022924712974372438372930331471981874800876400346553703665820,
    7532377983992352815137279022198273432546786243903279580690534117658497852353,
    10237718478628148948426570229423619173256326742102272297913238835664122004457,
    10850163885430594293735379828443965351958623545011669517140021837554759680171,
    10691117041282485274483783370715796550464560397292781489540265443495529268402,
    10860315677969016130201661141405999631129693614428688990903574755512392632291,
    -5042824592723942988945833234058137232164090280010197874330890546591437308098,
    7928773172434777067688383830053622879226049343510124887642735433025465636762,
    -5365465422624813893656003597829379913225810922268944787212034300127946829462,
    -1954433861713551557863714542579906492850583717807121342655986156685304658357,
    877666827331549468968552482651778577334417800136540938553767841025196345246,
    6186660721010143203533947949968427630060060682098791620460582437277471902486,
    6903521529107129656182174853046909266036249220349851901115147460033591939641,
    -203367904532453802288154715378758714677939821427538841608994930248082548003,
    4976771288109216028210477643337176753620418881946029852066249985579465903143] : List ℤ).getD i 0
def HI (i : ℕ) : ℤ := ([-8223310202727175663580470465848428192558352274842652618059886443451980321704,
    -871230540185822044104071362720638191918432909700945681376215508999109565259,
    -664313720428245859954284583541090716456479859248186712533951090743063195665,
    987216774258473263016157449014370990855809970460967348519945688807136144636,
    2202970899181122291888048653488803474052057403070825878671174453476841147902,
    -8151342775303169968381506571086978786444840306918621054102351448340432948025,
    259611743084534558328784880018628833317462659541925602081610242809938929632,
    -2285019823063606696242764519394744439236502605319322361693430272072109371083,
    -1500969680245491099780180099390594726791859058047284918558439113789138168127,
    6356916758059472108445955439562923497540805376917122688284337237921240484164,
    1126245767620976072817494277447469608899171266077625386795617102904432169773,
    -6949323896951846029987230538498072847235656194202156565607789390508639235761,
    -2913071591567856129553790931086250518619988520530119653299616630120941102436,
    1445234999368244946873091531628341940124632218446465639779110317152194271662,
    -2707857582938884972031638904851015014076191566121677322598319331622177735326] : List ℤ).getD i 0

def loZL : ZL := (0, (List.range 15).map (fun i => (LO i, .wit i)) ++
  (List.range 6).map fun k => (-2 ^ (32 * k), .plug (16 + k)))
def hiZL : ZL := (0, (List.range 15).map (fun i => (HI i, .wit i)) ++
  [(-1, .plug 22), (-2 ^ 32, .plug 23)])
/-- `K + 8 = q`. -/
def kbZL : ZL := (0, [(1, .wit 15)])
/-- `T + 8 = 2⁶⁴·(q − 8) − H + 8`. -/
def tbZL : ZL := (8 - 2 ^ 67, hiZL.neg.2 ++ [(2 ^ 64, .wit 15)])
/-- `L + c·K − 2¹⁹²·T`. -/
def eZL : ZL := (2 ^ 259 - 8 * 4294968273,
  loZL.2 ++ [(4294968273, .wit 15)] ++ tbZL.2.map fun t => (-2 ^ 192 * t.1, t.2))

def rows : List Row :=
  (List.range 15).map (fun i => ⟨(aZL i).lc, (bZL i).lc, LC.var (.wit i)⟩) ++
    bitRows kbZL.lc 17 39 ++ bitRows tbZL.lc 56 46 ++ [⟨eZL.lc, ⟨1, []⟩, ⟨0, []⟩⟩]

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = rows := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 24).map fun j => LC.var (.plug j) := by
  decide +kernel
theorem outputs_eq : template.outputs = [] := by decide +kernel

/-! ### The integer certificate -/

/-- `ℓₘ`, `hₘ`: `Y^m mod (Y⁸ − Y − 977)` at `Y = 2³²`, split after its sixth word, so
`ℓₘ + 2¹⁹²·hₘ ≡ 2³²ᵐ (mod p)`. -/
def ell (m : ℕ) : ℤ := ([1, 4294967296, 18446744073709551616, 79228162514264337593543950336, 340282366920938463463374607431768211456, 1461501637330902918203684832716283019655932542976, 0, 0, 4294968273, 18446748269892599808, 79228180536733297607775879168, 340282444326853239899632436324207689728, 1461501969786775399960563636433274480493475135488, 1427887099672292151085000081563808510203846094487552, 0] : List ℤ).getD m 0
def hh (m : ℕ) : ℤ := ([0, 0, 0, 0, 0, 0, 1, 4294967296, 0, 0, 0, 0, 0, 1, 4294968273] : List ℤ).getD m 0

/-- secp256k1's `p`. -/
def pZ : ℤ := 2 ^ 256 - 4294968273
theorem pZ_eq : ((Xark.secp256k1_p : ℕ) : ℤ) = pZ := by norm_num [Xark.secp256k1_p, pZ]

theorem vand_lo : ∀ m < 15,
    (((List.range 15).map fun i => LO i * pt i ^ m).sum - ell m) % (r : ℤ) = 0 := by decide +kernel
theorem vand_hi : ∀ m < 15,
    (((List.range 15).map fun i => HI i * pt i ^ m).sum - hh m) % (r : ℤ) = 0 := by decide +kernel
theorem kap : ∀ m < 15, (ell m + 2 ^ 192 * hh m - 2 ^ (32 * m)) % pZ = 0 := by decide +kernel

/-- Limbs below `2³⁴`. -/
def Lim (v : ℕ → ℤ) (n : ℕ) : Prop := ∀ i < n, 0 ≤ v i ∧ v i ≤ 2 ^ 34 - 1

theorem ec_bd (a b : ℕ → ℤ) (ha : Lim a 8) (hb : Lim b 8) (m : ℕ) (hm : m < 15) :
    0 ≤ ec a b m ∧ ec a b m ≤ cnt m * (2 ^ 34 - 1) ^ 2 := by
  rw [← cnt_eq m hm, Finset.sum_mul]
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  constructor
  · refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
    split_ifs
    · exact mul_nonneg (ha i (by simpa using hi)).1 (hb j (by simpa using hj)).1
    · rfl
  · refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    split_ifs
    · obtain ⟨h1, h2⟩ := ha i (by simpa using hi); obtain ⟨h3, h4⟩ := hb j (by simpa using hj)
      rw [sq]; exact mul_le_mul h2 h4 h3 (by norm_num)
    · rfl

/-- `L` and `H` as integers, from the columns `e` and `t`. -/
def Lo (e T : ℕ → ℤ) : ℤ :=
  ∑ m ∈ Finset.range 15, ell m * e m - ∑ k ∈ Finset.range 6, 2 ^ (32 * k) * T k
def Hi (e T : ℕ → ℤ) : ℤ := ∑ m ∈ Finset.range 15, hh m * e m - (T 6 + 2 ^ 32 * T 7)

theorem bd_lo : ∑ m ∈ Finset.range 15, min (ell m) 0 * (cnt m * (2 ^ 34 - 1) ^ 2) = 0 ∧
    ∑ m ∈ Finset.range 15, max (ell m) 0 * (cnt m * (2 ^ 34 - 1) ^ 2) < 2 ^ 239 - 2 ^ 234 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ell, cnt]; norm_num
theorem bd_hi : ∑ m ∈ Finset.range 15, min (hh m) 0 * (cnt m * (2 ^ 34 - 1) ^ 2) = 0 ∧
    ∑ m ∈ Finset.range 15, max (hh m) 0 * (cnt m * (2 ^ 34 - 1) ^ 2) < 2 ^ 104 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hh, cnt]; norm_num

theorem lo_bds (e T : ℕ → ℤ) (he : ∀ m < 15, 0 ≤ e m ∧ e m ≤ cnt m * (2 ^ 34 - 1) ^ 2) (hT : Lim T 8) :
    -2 ^ 195 < Lo e T ∧ Lo e T < 2 ^ 239 - 2 ^ 234 := by
  obtain ⟨h1, h2⟩ := sum_bd ell (fun m => cnt m * (2 ^ 34 - 1) ^ 2) e 15 he
  obtain ⟨b1, b2⟩ := bd_lo
  have ht : 0 ≤ ∑ k ∈ Finset.range 6, 2 ^ (32 * k) * T k ∧
      ∑ k ∈ Finset.range 6, 2 ^ (32 * k) * T k < 2 ^ 195 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have := hT 0 (by norm_num); have := hT 1 (by norm_num); have := hT 2 (by norm_num)
    have := hT 3 (by norm_num); have := hT 4 (by norm_num); have := hT 5 (by norm_num)
    constructor <;> norm_num <;> omega
  unfold Lo; constructor <;> linarith [ht.1, ht.2]

theorem hi_bds (e T : ℕ → ℤ) (he : ∀ m < 15, 0 ≤ e m ∧ e m ≤ cnt m * (2 ^ 34 - 1) ^ 2) (hT : Lim T 8) :
    -2 ^ 67 < Hi e T ∧ Hi e T < 2 ^ 104 := by
  obtain ⟨h1, h2⟩ := sum_bd hh (fun m => cnt m * (2 ^ 34 - 1) ^ 2) e 15 he
  obtain ⟨b1, b2⟩ := bd_hi
  have := hT 6 (by norm_num); have := hT 7 (by norm_num)
  unfold Hi; constructor <;> nlinarith

/-- `L + 2¹⁹²·H ≡ a·b − t (mod p)`: `a·b − t = L + 2¹⁹²·H − p·Σ κₘ·eₘ`. -/
theorem lo_hi_eq (a b T : ℕ → ℤ) : ∃ κ : ℤ,
    num8 a * num8 b - num8 T = Lo (ec a b) T + 2 ^ 192 * Hi (ec a b) T - pZ * κ := by
  have hk : ∀ m ∈ Finset.range 15, 2 ^ (32 * m) * ec a b m =
      (ell m + 2 ^ 192 * hh m) * ec a b m -
        pZ * ((ell m + 2 ^ 192 * hh m - 2 ^ (32 * m)) / pZ * ec a b m) := by
    intro m hm
    have := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (kap m (Finset.mem_range.mp hm)))
    linear_combination (ec a b m) * this
  refine ⟨∑ m ∈ Finset.range 15, (ell m + 2 ^ 192 * hh m - 2 ^ (32 * m)) / pZ * ec a b m, ?_⟩
  rw [num8_mul, Finset.sum_congr rfl hk, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Lo, Hi, num8, Finset.sum_range_succ, Finset.sum_range_zero, add_mul]
  ring


/-- **The certificate's integer content.** With every limb below `2³⁴`, `K ∈ [−8, 2⁴⁰ − 8)`,
`T ∈ [−8, 2⁴⁷ − 8)` and the two field equations `L + c·K = 2¹⁹²·T`, `T = 2⁶⁴·K − H`,
`p ∣ a·b − t`. -/
theorem int_sound (a b T : ℕ → ℤ) (K Tt : ℤ) (ha : Lim a 8) (hb : Lim b 8) (hT : Lim T 8)
    (hK : -8 ≤ K ∧ K < 2 ^ 40 - 8) (hTt : -8 ≤ Tt ∧ Tt < 2 ^ 47 - 8)
    (h1 : ((Lo (ec a b) T + 4294968273 * K - 2 ^ 192 * Tt : ℤ) : F) = 0)
    (h2 : ((Tt - 2 ^ 64 * K + Hi (ec a b) T : ℤ) : F) = 0) :
    pZ ∣ num8 a * num8 b - num8 T := by
  have he := fun m hm => ec_bd a b ha hb m hm
  obtain ⟨l1, l2⟩ := lo_bds _ T he hT
  obtain ⟨i1, i2⟩ := hi_bds _ T he hT
  have e1 := MulCertR1.lift _ h1 (by rw [abs_lt]; constructor <;> nlinarith)
  have e2 := MulCertR1.lift _ h2 (by rw [abs_lt]; constructor <;> nlinarith)
  obtain ⟨κ, hκ⟩ := lo_hi_eq a b T
  refine ⟨K - κ, ?_⟩
  rw [hκ]; unfold pZ; linear_combination e1 + 2 ^ 192 * e2

/-! ### The rows' meaning -/

theorem eval_lo (σ : TVar → F) : loZL.lc.eval σ = ∑ i ∈ Finset.range 15, ((LO i : ℤ) : F) * σ (.wit i) -
    ∑ k ∈ Finset.range 6, (2 : F) ^ (32 * k) * σ (.plug (16 + k)) := by
  rw [eval_lc]; simp only [loZL, S_append, S_range]; push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]; ring
theorem eval_hi (σ : TVar → F) : hiZL.lc.eval σ = ∑ i ∈ Finset.range 15, ((HI i : ℤ) : F) * σ (.wit i) -
    (σ (.plug 22) + 2 ^ 32 * σ (.plug 23)) := by
  rw [eval_lc]; simp only [hiZL, S_append, S_range]; simp [S]; ring
theorem eval_kb (σ : TVar → F) : kbZL.lc.eval σ = σ (.wit 15) := by
  rw [eval_lc]; simp [kbZL, S]
theorem eval_tb (σ : TVar → F) :
    tbZL.lc.eval σ = 2 ^ 64 * σ (.wit 15) + 8 - 2 ^ 67 - hiZL.lc.eval σ := by
  rw [eval_lc tbZL, eval_lc hiZL]
  simp only [tbZL, ZL.neg, S_append, S_neg]
  rw [show hiZL.1 = 0 from rfl]; simp [S]; ring
theorem eval_e (σ : TVar → F) : eZL.lc.eval σ = loZL.lc.eval σ + 4294968273 * (σ (.wit 15) - 8) -
    2 ^ 192 * (tbZL.lc.eval σ - 8) := by
  rw [eval_lc eZL, eval_lc loZL, eval_lc tbZL]
  simp only [eZL, S_append, S_scale]
  rw [show loZL.1 = 0 from rfl, show tbZL.1 = 8 - 2 ^ 67 from rfl]; simp [S]; ring

theorem sat_rows (σ : TVar → F) : Xark.R1cs.Sat rows σ ↔
    (∀ i < 15, (aZL i).lc.eval σ * (bZL i).lc.eval σ = σ (.wit i)) ∧
      Xark.R1cs.Sat (bitRows kbZL.lc 17 39) σ ∧
      Xark.R1cs.Sat (bitRows tbZL.lc 56 46) σ ∧ eZL.lc.eval σ = 0 := by
  simp only [Xark.R1cs.Sat, rows, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun r hr => h r (Or.inl (Or.inl (Or.inr hr))),
      fun r hr => h r (Or.inl (Or.inr hr)), ?_⟩
    · simpa [Row.Sat] using h _ (Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩)))
    · simpa [Row.Sat, LC.eval] using h _ (Or.inr rfl)
  · rintro ⟨hp, hk, ht, he⟩ row ((((⟨i, hi, rfl⟩ | hr) | hr) | rfl))
    · simpa [Row.Sat] using hp i hi
    · exact hk _ hr
    · exact ht _ hr
    · simpa [Row.Sat, LC.eval] using he

theorem lo_eval (σ : TVar → F) (hp : ∀ i < 15, (aZL i).lc.eval σ * (bZL i).lc.eval σ = σ (.wit i)) :
    loZL.lc.eval σ = ((Lo (ec (Av σ) (Bv σ)) (Tv σ) : ℤ) : F) := by
  have hs : ∑ i ∈ Finset.range 15, ((LO i : ℤ) : F) * σ (.wit i) = ∑ i ∈ Finset.range 15,
      ((LO i : ℤ) : F) * ∑ m ∈ Finset.range 15, ((pt i : ℤ) : F) ^ m *
        ec (fun j => σ (.plug j)) (fun j => σ (.plug (8 + j))) m :=
    Finset.sum_congr rfl fun i hi => by rw [wit_eq σ hp i (Finset.mem_range.mp hi)]
  rw [eval_lo, hs, vand_F LO ell vand_lo]
  simp only [Lo, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_sum, ec_cast, Tv, cast_vZ]

theorem hi_eval (σ : TVar → F) (hp : ∀ i < 15, (aZL i).lc.eval σ * (bZL i).lc.eval σ = σ (.wit i)) :
    hiZL.lc.eval σ = ((Hi (ec (Av σ) (Bv σ)) (Tv σ) : ℤ) : F) := by
  have hs : ∑ i ∈ Finset.range 15, ((HI i : ℤ) : F) * σ (.wit i) = ∑ i ∈ Finset.range 15,
      ((HI i : ℤ) : F) * ∑ m ∈ Finset.range 15, ((pt i : ℤ) : F) ^ m *
        ec (fun j => σ (.plug j)) (fun j => σ (.plug (8 + j))) m :=
    Finset.sum_congr rfl fun i hi => by rw [wit_eq σ hp i (Finset.mem_range.mp hi)]
  rw [eval_hi, hs, vand_F HI hh vand_hi]
  simp only [Hi, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_sum, ec_cast, Tv, cast_vZ]

/-! ### Soundness -/

-- The generated constant obligations unfold `IsBit` too (`add32`'s assumption).
export Xark.Templates.Add32 (IsBit)

/-- The input assumption: every limb of `a`, `b` and `t` is below `2³⁴`. Each caller enforces
it (`Formal/EcK1Check.lean`'s `lo_hi`, `formal/coverage-allowlist.txt`). -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, v.val < 2 ^ 34

/-- Input `j`'s canonical value. -/
def lz (ins : List F) (j : ℕ) : ℤ := ((ins.getD j 0).val : ℤ)

/-- `a·b ≡ t (mod p)`, the three inputs read as 8-limb numbers in base `2³²`. -/
def Spec (ins : List F) : Prop :=
  ((num8 (fun j => lz ins j) : ℤ) : ZMod Xark.secp256k1_p) * ((num8 fun j => lz ins (8 + j) : ℤ) : ZMod _) =
    ((num8 fun j => lz ins (16 + j) : ℤ) : ZMod _)

theorem spec_iff (X Y Z : ℤ) :
    ((X : ZMod Xark.secp256k1_p) * (Y : ZMod _) = (Z : ZMod _)) ↔ pZ ∣ X * Y - Z := by
  rw [← sub_eq_zero, ← Int.cast_mul, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, pZ_eq]

theorem ins_eq (σ : TVar → F) : template.ins σ = (List.range 24).map fun j => σ (.plug j) := by
  simp [Template.ins, inputs_eq]

theorem lz_ins (σ : TVar → F) (j : ℕ) (hj : j < 24) : lz (template.ins σ) j = vZ σ j := by
  rw [lz, ins_eq, List.getD_eq_getElem _ _ (by simpa using hj)]; simp [vZ]

theorem spec_vals (σ : TVar → F) : Spec (template.ins σ) ↔
    pZ ∣ num8 (Av σ) * num8 (Bv σ) - num8 (Tv σ) := by
  rw [Spec, num8_congr _ (Av σ) fun j hj => lz_ins σ j (by omega),
    num8_congr _ (Bv σ) fun j hj => lz_ins σ _ (by omega),
    num8_congr _ (Tv σ) fun j hj => lz_ins σ _ (by omega), spec_iff]

theorem lims (σ : TVar → F) (ha : Assumptions (template.ins σ)) :
    Lim (Av σ) 8 ∧ Lim (Bv σ) 8 ∧ Lim (Tv σ) 8 := by
  have hv : ∀ j < 24, 0 ≤ vZ σ j ∧ vZ σ j ≤ 2 ^ 34 - 1 := fun j hj => by
    have := ha _ (by rw [ins_eq]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    unfold vZ; omega
  exact ⟨fun i hi => hv i (by omega), fun i hi => hv _ (by omega), fun i hi => hv _ (by omega)⟩

/-- **Soundness.** If every limb of `a`, `b`, `t` is below `2³⁴`, every assignment satisfying
the exported rows has `a·b ≡ t (mod p)`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  rw [Template.Sat, rows_eq, sat_rows] at h
  obtain ⟨hp, hk, ht, he⟩ := h
  obtain ⟨la, lb, lt⟩ := lims σ ha
  have hK := bits_sound kbZL.lc 17 39 (by norm_num) σ hk
  have hT := bits_sound tbZL.lc 56 46 (by norm_num) σ ht
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℤ, Kb = ((kbZL.lc.eval σ).val : ℤ) := ⟨_, rfl⟩
  obtain ⟨Tb, hTb⟩ : ∃ Tb : ℤ, Tb = ((tbZL.lc.eval σ).val : ℤ) := ⟨_, rfl⟩
  have cK : ((Kb : ℤ) : F) = kbZL.lc.eval σ := by rw [hKb, Int.cast_natCast, ZMod.natCast_zmod_val]
  have cT : ((Tb : ℤ) : F) = tbZL.lc.eval σ := by rw [hTb, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hK' : 0 ≤ Kb ∧ Kb < 2 ^ 40 := by
    generalize (kbZL.lc.eval σ).val = kv at hK hKb; subst hKb; omega
  have hT' : 0 ≤ Tb ∧ Tb < 2 ^ 47 := by
    generalize (tbZL.lc.eval σ).val = tv at hT hTb; subst hTb; omega
  rw [spec_vals]
  refine int_sound _ _ _ (Kb - 8) (Tb - 8) la lb lt
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ?_ ?_
  · push_cast; rw [cK, cT, ← lo_eval σ hp, eval_kb]; rw [eval_e] at he
    linear_combination he
  · push_cast; rw [cK, cT, ← hi_eval σ hp, eval_tb, eval_kb]; ring

end Xark.Templates.MulCertK1
