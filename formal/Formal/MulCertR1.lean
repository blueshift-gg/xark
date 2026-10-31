/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.MulCertR1
import Formal.CertCall
import Formal.Secp256r1Group

set_option linter.style.header false
set_option linter.style.longLine false
set_option exponentiation.threshold 600

namespace Xark.Templates.MulCertR1

open Xark.Template Xark.R1cs
open Xark.Templates.EcK1Check (norm eval_norm)

/-- The evaluation points. -/
def pt (i : ℕ) : ℤ := [0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6, 7, -7].getD i 0
/-- `L`'s and `H`'s coefficients of the products. -/
def LO (i : ℕ) : ℤ := [9363695963018136371772207501888011185057361295673458298760118506927698404381,
    3101071155502605351026484082051190841481527969099589744492656422263611879870,
    -690904967865553908019009363007571838928885465635762243658731796537507193859,
    256225885409253718062557022574936405035467193120491463903323163317571138900,
    887497334438707814991195163580610633139029299892521034645282519898879885554,
    2181101555989893254135221809418113128195011863720505735598176604469702270361,
    6350696313857077509226549995570063385292215994858482729831480464349624893139,
    7976670793853647505480671914368216556543358684113142538090307562902073820475,
    -2262151849262957615799669056281535545446036517988355197786315506515109168542,
    -1313737316520783473782574801835550086850694107522010151811455466464057274042,
    -2346537917885507797743681105474227387019368301504270575635800663285852440491,
    -7439779688142332093641697000764276818772980490043904628804056878686217351318,
    7789229095286828943191255023306409733993036010958532347169306130958930965552,
    -164014998212821937493426102316728210314857971371200643987472474444118783118,
    -1800818487626918419159679337820386892855821056955186107108614402579422551244].getD i 0
def HI (i : ℕ) : ℤ := [1011728051526495070430399616529842720778787803040074331232270180561418765911,
    -2143672397289882142323425778723577627401260356556557406808321135434209679198,
    -28484482730352181803256137106277371154815648629616021463995163792149900983,
    -6221576812364631487096530200949609124630045305714714877582373183822089277587,
    4471381942475191821641329605165599412181420495324749025246455615776461844075,
    -2686439557397858515101815998203399077926491185536194818376414008168729334738,
    -10763905692860362477353783804455275288014545422686424210342128636795339338494,
    -8545899654506934771522518882977485173132193937211987332561547022324575528175,
    2603900754342303388331934728689637114610062599098757882361910687811558547087,
    4570305160136366643975041522131053535870439368061723394964113354022547770337,
    -1986948166696069907635798084761835853005184906221707111279675919550137285845,
    3287327061506095839027523073285627398746012351398081048246495227756153619192,
    4799062079688944208046447727706920064275310183731841173320189888946735507325,
    -5251524203381129672254494820896632780528391578830777156733042897338289540577,
    -5003496954287451038607458310691863039217468859683282263922141174225164663947].getD i 0
/-- `p′ = (p + 1)/2⁹⁶`. -/
def PP : ℤ := 1461501636990620551361974531767172749817708281857

abbrev ZL := ℤ × List (ℤ × TVar)
def ZL.lc (d : ZL) : LC := norm ⟨(d.1 : F), d.2.map fun t => ((t.1 : F), t.2)⟩
def ZL.neg (d : ZL) : ZL := (-d.1, d.2.map fun t => (-t.1, t.2))

def aZL (i : ℕ) : ZL := (0, (List.range 8).map fun j => (pt i ^ j, .plug j))
def bZL (i : ℕ) : ZL := (0, (List.range 8).map fun j => (pt i ^ j, .plug (8 + j)))
def loZL : ZL := (0, (List.range 15).map (fun i => (LO i, .wit i)) ++
  [(-1, .plug 16), (-2 ^ 32, .plug 17), (-2 ^ 64, .plug 18)])
def hiZL : ZL := (0, (List.range 15).map (fun i => (HI i, .wit i)) ++
  (List.range 5).map fun k => (-2 ^ (32 * k), .plug (19 + k)))
/-- `N = 2¹⁴⁰ + 2⁴² − L`, the divided operand. -/
def nZL : ZL := (2 ^ 140 + 2 ^ 42, loZL.neg.2)
/-- `K + 2⁴² = N − 2⁹⁶·q`. -/
def kbZL : ZL := (nZL.1, nZL.2 ++ [(-2 ^ 96, .wit 15)])
/-- `T + 2⁴² = (K + 2⁴² − 2⁴²)·p′ − H + 2⁴²`. -/
def tbZL : ZL := ((kbZL.1 - 2 ^ 42) * PP + 2 ^ 42,
  kbZL.2.map (fun t => (PP * t.1, t.2)) ++ hiZL.neg.2)
/-- `L + K − 2⁹⁶·T`. -/
def eZL : ZL := (kbZL.1 - 2 ^ 42 - 2 ^ 96 * (tbZL.1 - 2 ^ 42),
  loZL.2 ++ kbZL.2 ++ tbZL.2.map fun t => (-2 ^ 96 * t.1, t.2))

def rows : List Row :=
  (List.range 15).map (fun i => ⟨(aZL i).lc, (bZL i).lc, LC.var (.wit i)⟩) ++
    MulCertK1.bitRows kbZL.lc 17 42 ++ MulCertK1.bitRows tbZL.lc 59 42 ++
    [⟨eZL.lc, ⟨1, []⟩, ⟨0, []⟩⟩]

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows = rows := by decide +kernel
theorem inputs_eq : template.inputs = (List.range 24).map fun j => LC.var (.plug j) := by
  decide +kernel
theorem outputs_eq : template.outputs = [] := by decide +kernel


/-! ### The integer certificate -/

/-- `ℓₘ`, `hₘ`: `Y^m mod (Y⁸ − Y⁷ + Y⁶ + Y³ − 1)` at `Y = 2³²`, split after its third word,
so `ℓₘ + 2⁹⁶·hₘ ≡ 2³²ᵐ (mod p)`. -/
def ell (m : ℕ) : ℤ := [1, 4294967296, 18446744073709551616, 0, 0, 0, 0, 0, 1, 4294967297, 18446744078004518912, 18446744073709551615, -4294967297, -18446744078004518913, -18446744078004518913].getD m 0
def hh (m : ℕ) : ℤ := [0, 0, 0, 1, 4294967296, 18446744073709551616, 79228162514264337593543950336, 340282366920938463463374607431768211456, 340282366841710300949110269838224261119, -79228162514264337597838917633, -340282366920938463481821351509772730368, -340282366920938463481821351505477763070, -340282366920938463463374607423178276862, -340282366841710300912216781682215223295, 237684487579686500932345921536].getD m 0
/-- The number of limb pairs in column `m`. -/
def cnt (m : ℕ) : ℤ := [1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1].getD m 0

/-- secp256r1's `p`. -/
def pZ : ℤ := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
theorem p_PP : pZ = 2 ^ 96 * PP - 1 := by norm_num [pZ, PP]
theorem pZ_eq : ((Xark.secp256r1_p : ℕ) : ℤ) = pZ := by norm_num [Xark.secp256r1_p, pZ]

theorem vand_lo : ∀ m < 15,
    (((List.range 15).map fun i => LO i * pt i ^ m).sum - ell m) % (r : ℤ) = 0 := by decide +kernel
theorem vand_hi : ∀ m < 15,
    (((List.range 15).map fun i => HI i * pt i ^ m).sum - hh m) % (r : ℤ) = 0 := by decide +kernel
theorem kap : ∀ m < 15, (ell m + 2 ^ 96 * hh m - 2 ^ (32 * m)) % pZ = 0 := by decide +kernel

/-- Column `m` of `a·b`: `Σ_{i+j=m} aᵢbⱼ`. -/
def ec {R : Type*} [CommRing R] (a b : ℕ → R) (m : ℕ) : R :=
  ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8, if i + j = m then a i * b j else 0

theorem map_ec {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : ℕ → R) (m : ℕ) :
    f (ec a b m) = ec (fun i => f (a i)) (fun j => f (b j)) m := by
  simp only [ec, map_sum]; congr 1; funext i; congr 1; funext j; split_ifs <;> simp

theorem prod_eval {R : Type*} [CommRing R] (a b : ℕ → R) (w : R) :
    (∑ j ∈ Finset.range 8, w ^ j * a j) * (∑ j ∈ Finset.range 8, w ^ j * b j) =
      ∑ m ∈ Finset.range 15, w ^ m * ec a b m := by
  rw [Finset.sum_mul_sum]
  simp only [ec, Finset.mul_sum, mul_ite, mul_zero]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_ite_eq, if_pos (by simp at hi hj ⊢; omega), pow_add]
  ring

/-- `Σ 2^(32j)·v j`, an 8-limb number. -/
def num8 {R : Type*} [CommRing R] (v : ℕ → R) : R := ∑ j ∈ Finset.range 8, 2 ^ (32 * j) * v j

theorem num8_mul (a b : ℕ → ℤ) :
    num8 a * num8 b = ∑ m ∈ Finset.range 15, 2 ^ (32 * m) * ec a b m := by
  have := prod_eval a b (2 ^ 32)
  simp only [← pow_mul] at this
  exact this

theorem sum_bd (c E e : ℕ → ℤ) (n : ℕ) (he : ∀ m < n, 0 ≤ e m ∧ e m ≤ E m) :
    ∑ m ∈ Finset.range n, min (c m) 0 * E m ≤ ∑ m ∈ Finset.range n, c m * e m ∧
      ∑ m ∈ Finset.range n, c m * e m ≤ ∑ m ∈ Finset.range n, max (c m) 0 * E m := by
  constructor <;> refine Finset.sum_le_sum fun m hm => ?_ <;>
    obtain ⟨h0, h1⟩ := he m (Finset.mem_range.mp hm) <;> rcases le_total (c m) 0 with hc | hc
  · rw [min_eq_left hc]; nlinarith
  · rw [min_eq_right hc]; nlinarith
  · rw [max_eq_right hc]; nlinarith
  · rw [max_eq_left hc]; nlinarith

theorem cnt_eq : ∀ m < 15,
    ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8, (if i + j = m then (1 : ℤ) else 0) = cnt m := by
  intro m hm; interval_cases m <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero, cnt] <;> norm_num

/-- Limbs below `2³⁵`. -/
def Lim (v : ℕ → ℤ) (n : ℕ) : Prop := ∀ i < n, 0 ≤ v i ∧ v i ≤ 2 ^ 35 - 1

theorem ec_bd (a b : ℕ → ℤ) (ha : Lim a 8) (hb : Lim b 8) (m : ℕ) (hm : m < 15) :
    0 ≤ ec a b m ∧ ec a b m ≤ cnt m * (2 ^ 35 - 1) ^ 2 := by
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
def Lo (e T : ℕ → ℤ) : ℤ := ∑ m ∈ Finset.range 15, ell m * e m - (T 0 + 2 ^ 32 * T 1 + 2 ^ 64 * T 2)
def Hi (e T : ℕ → ℤ) : ℤ :=
  ∑ m ∈ Finset.range 15, hh m * e m - ∑ k ∈ Finset.range 5, 2 ^ (32 * k) * T (3 + k)

theorem bd_lo : ∑ m ∈ Finset.range 15, min (ell m) 0 * (cnt m * (2 ^ 35 - 1) ^ 2) ≥ -2 ^ 136 ∧
    ∑ m ∈ Finset.range 15, max (ell m) 0 * (cnt m * (2 ^ 35 - 1) ^ 2) < 2 ^ 137 + 2 ^ 136 + 2 ^ 120 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ell, cnt]; norm_num
theorem bd_hi : ∑ m ∈ Finset.range 15, min (hh m) 0 * (cnt m * (2 ^ 35 - 1) ^ 2) ≥ -2 ^ 205 ∧
    ∑ m ∈ Finset.range 15, max (hh m) 0 * (cnt m * (2 ^ 35 - 1) ^ 2) < 2 ^ 205 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hh, cnt]; norm_num

theorem lo_bds (e T : ℕ → ℤ) (he : ∀ m < 15, 0 ≤ e m ∧ e m ≤ cnt m * (2 ^ 35 - 1) ^ 2) (hT : Lim T 8) :
    -2 ^ 137 < Lo e T ∧ Lo e T < 2 ^ 137 + 2 ^ 136 + 2 ^ 120 := by
  obtain ⟨h1, h2⟩ := sum_bd ell (fun m => cnt m * (2 ^ 35 - 1) ^ 2) e 15 he
  obtain ⟨b1, b2⟩ := bd_lo
  have := hT 0 (by norm_num); have := hT 1 (by norm_num); have := hT 2 (by norm_num)
  unfold Lo; constructor <;> nlinarith

theorem hi_bds (e T : ℕ → ℤ) (he : ∀ m < 15, 0 ≤ e m ∧ e m ≤ cnt m * (2 ^ 35 - 1) ^ 2) (hT : Lim T 8) :
    -2 ^ 206 < Hi e T ∧ Hi e T < 2 ^ 206 := by
  obtain ⟨h1, h2⟩ := sum_bd hh (fun m => cnt m * (2 ^ 35 - 1) ^ 2) e 15 he
  obtain ⟨b1, b2⟩ := bd_hi
  have ht : 0 ≤ ∑ k ∈ Finset.range 5, 2 ^ (32 * k) * T (3 + k) ∧
      ∑ k ∈ Finset.range 5, 2 ^ (32 * k) * T (3 + k) ≤ 2 ^ 165 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have := hT 3 (by norm_num); have := hT 4 (by norm_num); have := hT 5 (by norm_num)
    have := hT 6 (by norm_num); have := hT 7 (by norm_num)
    constructor <;> norm_num <;> omega
  unfold Hi; constructor <;> linarith [ht.1, ht.2]

/-- `L + 2⁹⁶·H ≡ a·b − t (mod p)`: `a·b − t = L + 2⁹⁶·H − p·Σ κₘ·eₘ`. -/
theorem lo_hi_eq (a b T : ℕ → ℤ) : ∃ κ : ℤ,
    num8 a * num8 b - num8 T = Lo (ec a b) T + 2 ^ 96 * Hi (ec a b) T - pZ * κ := by
  have hk : ∀ m ∈ Finset.range 15, 2 ^ (32 * m) * ec a b m =
      (ell m + 2 ^ 96 * hh m) * ec a b m - pZ * ((ell m + 2 ^ 96 * hh m - 2 ^ (32 * m)) / pZ * ec a b m) := by
    intro m hm
    have := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (kap m (Finset.mem_range.mp hm)))
    linear_combination (ec a b m) * this
  refine ⟨∑ m ∈ Finset.range 15, (ell m + 2 ^ 96 * hh m - 2 ^ (32 * m)) / pZ * ec a b m, ?_⟩
  rw [num8_mul, Finset.sum_congr rfl hk, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Lo, Hi, num8, Finset.sum_range_succ, Finset.sum_range_zero, add_mul]
  ring

theorem lift (x : ℤ) (h : (x : F) = 0) (hb : |x| < 2 ^ 253) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x r).mp h)
    (lt_trans hb (by exact_mod_cast two_pow_lt_r))

/-- **The certificate's integer content.** With every limb below `2³⁵`, `K`, `T` in
`[−2⁴², 2⁴²)` and the two field equations `L + K = 2⁹⁶·T`, `T = K·p′ − H`, `p ∣ a·b − t`. -/
theorem int_sound (a b T : ℕ → ℤ) (K Tt : ℤ) (ha : Lim a 8) (hb : Lim b 8) (hT : Lim T 8)
    (hK : -2 ^ 42 ≤ K ∧ K < 2 ^ 42) (hTt : -2 ^ 42 ≤ Tt ∧ Tt < 2 ^ 42)
    (h1 : ((Lo (ec a b) T + K - 2 ^ 96 * Tt : ℤ) : F) = 0)
    (h2 : ((Tt - K * PP + Hi (ec a b) T : ℤ) : F) = 0) :
    pZ ∣ num8 a * num8 b - num8 T := by
  have he := fun m hm => ec_bd a b ha hb m hm
  obtain ⟨l1, l2⟩ := lo_bds _ T he hT
  obtain ⟨i1, i2⟩ := hi_bds _ T he hT
  have e1 := lift _ h1 (by rw [abs_lt]; constructor <;> nlinarith)
  have e2 := lift _ h2 (by rw [abs_lt]; constructor <;> nlinarith [show PP = 1461501636990620551361974531767172749817708281857 from rfl])
  obtain ⟨κ, hκ⟩ := lo_hi_eq a b T
  exact ⟨K - κ, by rw [hκ]; linear_combination e1 + 2 ^ 96 * e2 - K * p_PP⟩

/-! ### The rows' meaning -/

/-- A term list's value. -/
def S (ts : List (ℤ × TVar)) (σ : TVar → F) : F := (ts.map fun t => ((t.1 : ℤ) : F) * σ t.2).sum

theorem eval_lc (d : ZL) (σ : TVar → F) : d.lc.eval σ = ((d.1 : ℤ) : F) + S d.2 σ := by
  rw [ZL.lc, eval_norm]; simp [LC.eval, S, List.map_map, Function.comp_def]

theorem S_append (a b : List (ℤ × TVar)) (σ : TVar → F) : S (a ++ b) σ = S a σ + S b σ := by
  simp [S]
theorem S_scale (k : ℤ) (ts : List (ℤ × TVar)) (σ : TVar → F) :
    S (ts.map fun t => (k * t.1, t.2)) σ = (k : F) * S ts σ := by
  induction ts with
  | nil => simp [S]
  | cons t ts ih => simp only [S, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; push_cast; ring
theorem S_neg (ts : List (ℤ × TVar)) (σ : TVar → F) :
    S (ts.map fun t => (-t.1, t.2)) σ = -S ts σ := by
  induction ts with
  | nil => simp [S]
  | cons t ts ih => simp only [S, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; push_cast; ring
theorem S_range (n : ℕ) (c : ℕ → ℤ) (v : ℕ → TVar) (σ : TVar → F) :
    S ((List.range n).map fun i => (c i, v i)) σ = ∑ i ∈ Finset.range n, ((c i : ℤ) : F) * σ (v i) := by
  simp only [S, List.map_map, Function.comp_def, Xark.Templates.Add32.sum_map_range]

theorem eval_a (i : ℕ) (σ : TVar → F) :
    (aZL i).lc.eval σ = ∑ j ∈ Finset.range 8, ((pt i : ℤ) : F) ^ j * σ (.plug j) := by
  rw [eval_lc]; simp only [aZL, S_range, Int.cast_zero, zero_add, Int.cast_pow]
theorem eval_b (i : ℕ) (σ : TVar → F) :
    (bZL i).lc.eval σ = ∑ j ∈ Finset.range 8, ((pt i : ℤ) : F) ^ j * σ (.plug (8 + j)) := by
  rw [eval_lc]; simp only [bZL, S_range, Int.cast_zero, zero_add, Int.cast_pow]
theorem eval_lo (σ : TVar → F) : loZL.lc.eval σ = ∑ i ∈ Finset.range 15, ((LO i : ℤ) : F) * σ (.wit i) -
    (σ (.plug 16) + 2 ^ 32 * σ (.plug 17) + 2 ^ 64 * σ (.plug 18)) := by
  rw [eval_lc]; simp only [loZL, S_append, S_range]; simp [S]; ring
theorem eval_hi (σ : TVar → F) : hiZL.lc.eval σ = ∑ i ∈ Finset.range 15, ((HI i : ℤ) : F) * σ (.wit i) -
    ∑ k ∈ Finset.range 5, (2 : F) ^ (32 * k) * σ (.plug (19 + k)) := by
  rw [eval_lc]; simp only [hiZL, S_append, S_range]; push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]; ring
theorem eval_tb (σ : TVar → F) :
    tbZL.lc.eval σ = (kbZL.lc.eval σ - 2 ^ 42) * (PP : F) + 2 ^ 42 - hiZL.lc.eval σ := by
  rw [eval_lc tbZL, eval_lc kbZL, eval_lc hiZL]
  simp only [tbZL, ZL.neg, S_append, S_scale, S_neg]
  rw [show hiZL.1 = 0 from rfl]; push_cast; ring
theorem eval_e (σ : TVar → F) : eZL.lc.eval σ = loZL.lc.eval σ + kbZL.lc.eval σ - 2 ^ 42 -
    2 ^ 96 * (tbZL.lc.eval σ - 2 ^ 42) := by
  rw [eval_lc eZL, eval_lc loZL, eval_lc kbZL, eval_lc tbZL]
  simp only [eZL, S_append, S_scale]
  rw [show loZL.1 = 0 from rfl]; push_cast; ring

theorem sat_rows (σ : TVar → F) : Xark.R1cs.Sat rows σ ↔
    (∀ i < 15, (aZL i).lc.eval σ * (bZL i).lc.eval σ = σ (.wit i)) ∧
      Xark.R1cs.Sat (MulCertK1.bitRows kbZL.lc 17 42) σ ∧
      Xark.R1cs.Sat (MulCertK1.bitRows tbZL.lc 59 42) σ ∧ eZL.lc.eval σ = 0 := by
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

/-- With the product rows holding, product `i` is `Σₘ ωᵢᵐ·eₘ`. -/
theorem wit_eq (σ : TVar → F) (hp : ∀ i < 15, (aZL i).lc.eval σ * (bZL i).lc.eval σ = σ (.wit i))
    (i : ℕ) (hi : i < 15) : σ (.wit i) = ∑ m ∈ Finset.range 15, ((pt i : ℤ) : F) ^ m *
      ec (fun j => σ (.plug j)) (fun j => σ (.plug (8 + j))) m := by
  rw [← hp i hi, eval_a, eval_b, prod_eval]

/-- The inverse Vandermonde step: `Σᵢ Cᵢ·Pᵢ = Σₘ tgtₘ·eₘ` in `Fr`. -/
theorem vand_F (C tgt : ℕ → ℤ)
    (h : ∀ m < 15, (((List.range 15).map fun i => C i * pt i ^ m).sum - tgt m) % (r : ℤ) = 0)
    (e : ℕ → F) : ∑ i ∈ Finset.range 15, ((C i : ℤ) : F) * ∑ m ∈ Finset.range 15, ((pt i : ℤ) : F) ^ m * e m =
      ∑ m ∈ Finset.range 15, ((tgt m : ℤ) : F) * e m := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr
    (Int.dvd_of_emod_eq_zero (h m (Finset.mem_range.mp hm)))
  rw [Xark.Templates.Add32.sum_map_range] at hd
  push_cast at hd
  have : ∑ i ∈ Finset.range 15, ((C i : ℤ) : F) * (((pt i : ℤ) : F) ^ m * e m) =
      (∑ i ∈ Finset.range 15, ((C i : ℤ) : F) * ((pt i : ℤ) : F) ^ m) * e m := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this]; linear_combination e m * hd

/-- A plug's canonical value. -/
def vZ (σ : TVar → F) (j : ℕ) : ℤ := ((σ (.plug j)).val : ℤ)
theorem cast_vZ (σ : TVar → F) (j : ℕ) : ((vZ σ j : ℤ) : F) = σ (.plug j) := by simp [vZ]
abbrev Av (σ : TVar → F) : ℕ → ℤ := fun j => vZ σ j
abbrev Bv (σ : TVar → F) : ℕ → ℤ := fun j => vZ σ (8 + j)
abbrev Tv (σ : TVar → F) : ℕ → ℤ := fun j => vZ σ (16 + j)

theorem ec_cast (σ : TVar → F) (m : ℕ) : ((ec (Av σ) (Bv σ) m : ℤ) : F) =
    ec (fun j => σ (.plug j)) (fun j => σ (.plug (8 + j))) m := by
  have := map_ec (Int.castRingHom F) (Av σ) (Bv σ) m
  simpa [cast_vZ] using this

theorem lo_eval (σ : TVar → F) (hp : ∀ i < 15, (aZL i).lc.eval σ * (bZL i).lc.eval σ = σ (.wit i)) :
    loZL.lc.eval σ = ((Lo (ec (Av σ) (Bv σ)) (Tv σ) : ℤ) : F) := by
  have hs : ∑ i ∈ Finset.range 15, ((LO i : ℤ) : F) * σ (.wit i) = ∑ i ∈ Finset.range 15,
      ((LO i : ℤ) : F) * ∑ m ∈ Finset.range 15, ((pt i : ℤ) : F) ^ m *
        ec (fun j => σ (.plug j)) (fun j => σ (.plug (8 + j))) m :=
    Finset.sum_congr rfl fun i hi => by rw [wit_eq σ hp i (Finset.mem_range.mp hi)]
  rw [eval_lo, hs, vand_F LO ell vand_lo]
  simp only [Lo, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_sum, ec_cast, Tv, cast_vZ]

theorem hi_eval (σ : TVar → F) (hp : ∀ i < 15, (aZL i).lc.eval σ * (bZL i).lc.eval σ = σ (.wit i)) :
    hiZL.lc.eval σ = ((Hi (ec (Av σ) (Bv σ)) (Tv σ) : ℤ) : F) := by
  have hs : ∑ i ∈ Finset.range 15, ((HI i : ℤ) : F) * σ (.wit i) = ∑ i ∈ Finset.range 15,
      ((HI i : ℤ) : F) * ∑ m ∈ Finset.range 15, ((pt i : ℤ) : F) ^ m *
        ec (fun j => σ (.plug j)) (fun j => σ (.plug (8 + j))) m :=
    Finset.sum_congr rfl fun i hi => by rw [wit_eq σ hp i (Finset.mem_range.mp hi)]
  rw [eval_hi, hs, vand_F HI hh vand_hi]
  simp only [Hi, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_sum, ec_cast, Tv, cast_vZ, show ∀ x, 16 + (3 + x) = 19 + x from fun x => by omega]

/-! ### Soundness -/

-- The generated constant obligations unfold `IsBit` too (`add32`'s assumption).
export Xark.Templates.Add32 (IsBit)

/-- The input assumption: every limb of `a`, `b` and `t` is below `2³⁵`. Each caller enforces
it (`formal/coverage-allowlist.txt`, `EcR1Check`). -/
def Assumptions (ins : List F) : Prop := ∀ v ∈ ins, v.val < 2 ^ 35

/-- Input `j`'s canonical value. -/
def lz (ins : List F) (j : ℕ) : ℤ := ((ins.getD j 0).val : ℤ)

/-- `a·b ≡ t (mod p)`, the three inputs read as 8-limb numbers in base `2³²`. -/
def Spec (ins : List F) : Prop :=
  ((num8 (fun j => lz ins j) : ℤ) : ZMod Xark.secp256r1_p) * ((num8 fun j => lz ins (8 + j) : ℤ) : ZMod _) =
    ((num8 fun j => lz ins (16 + j) : ℤ) : ZMod _)

theorem spec_iff (X Y Z : ℤ) :
    ((X : ZMod Xark.secp256r1_p) * (Y : ZMod _) = (Z : ZMod _)) ↔ pZ ∣ X * Y - Z := by
  rw [← sub_eq_zero, ← Int.cast_mul, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, pZ_eq]

theorem ins_eq (σ : TVar → F) : template.ins σ = (List.range 24).map fun j => σ (.plug j) := by
  simp [Template.ins, inputs_eq]

theorem lz_ins (σ : TVar → F) (j : ℕ) (hj : j < 24) : lz (template.ins σ) j = vZ σ j := by
  rw [lz, ins_eq, List.getD_eq_getElem _ _ (by simpa using hj)]; simp [vZ]

theorem num8_congr (f g : ℕ → ℤ) (h : ∀ j < 8, f j = g j) : num8 f = num8 g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

theorem spec_vals (σ : TVar → F) : Spec (template.ins σ) ↔
    pZ ∣ num8 (Av σ) * num8 (Bv σ) - num8 (Tv σ) := by
  rw [Spec, num8_congr _ (Av σ) fun j hj => lz_ins σ j (by omega),
    num8_congr _ (Bv σ) fun j hj => lz_ins σ _ (by omega),
    num8_congr _ (Tv σ) fun j hj => lz_ins σ _ (by omega), spec_iff]

theorem lims (σ : TVar → F) (ha : Assumptions (template.ins σ)) :
    Lim (Av σ) 8 ∧ Lim (Bv σ) 8 ∧ Lim (Tv σ) 8 := by
  have hv : ∀ j < 24, 0 ≤ vZ σ j ∧ vZ σ j ≤ 2 ^ 35 - 1 := fun j hj => by
    have := ha _ (by rw [ins_eq]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    unfold vZ; omega
  exact ⟨fun i hi => hv i (by omega), fun i hi => hv _ (by omega), fun i hi => hv _ (by omega)⟩

/-- **Soundness.** If every limb of `a`, `b`, `t` is below `2³⁵`, every assignment satisfying
the exported rows has `a·b ≡ t (mod p)`. -/
theorem soundness (σ : TVar → F) (ha : Assumptions (template.ins σ)) (h : template.Sat σ) :
    Spec (template.ins σ) := by
  rw [Template.Sat, rows_eq, sat_rows] at h
  obtain ⟨hp, hk, ht, he⟩ := h
  obtain ⟨la, lb, lt⟩ := lims σ ha
  have hK := MulCertK1.bits_sound kbZL.lc 17 42 (by norm_num) σ hk
  have hT := MulCertK1.bits_sound tbZL.lc 59 42 (by norm_num) σ ht
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℤ, Kb = ((kbZL.lc.eval σ).val : ℤ) := ⟨_, rfl⟩
  obtain ⟨Tb, hTb⟩ : ∃ Tb : ℤ, Tb = ((tbZL.lc.eval σ).val : ℤ) := ⟨_, rfl⟩
  have cK : ((Kb : ℤ) : F) = kbZL.lc.eval σ := by rw [hKb, Int.cast_natCast, ZMod.natCast_zmod_val]
  have cT : ((Tb : ℤ) : F) = tbZL.lc.eval σ := by rw [hTb, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hK' : 0 ≤ Kb ∧ Kb < 2 ^ 43 := by
    generalize (kbZL.lc.eval σ).val = kv at hK hKb; subst hKb; omega
  have hT' : 0 ≤ Tb ∧ Tb < 2 ^ 43 := by
    generalize (tbZL.lc.eval σ).val = tv at hT hTb; subst hTb; omega
  rw [spec_vals]
  refine int_sound _ _ _ (Kb - 2 ^ 42) (Tb - 2 ^ 42) la lb lt
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ?_ ?_
  · push_cast; rw [cK, cT, ← lo_eval σ hp]; rw [eval_e] at he; linear_combination he
  · push_cast; rw [cK, cT, ← hi_eval σ hp, eval_tb]; ring

end Xark.Templates.MulCertR1
