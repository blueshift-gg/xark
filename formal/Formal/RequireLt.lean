/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Add32
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

set_option linter.style.header false

/-!
# `xark_bignum::require_lt`, proven over its exported rows

`require_lt::<L, B>(x, m₋₁)` accepts exactly when `x ≤ m₋₁` as `L`-limb numbers in base
`2^B`. It is a chunked lexicographic comparison (zkGolf RSA record 31516100): bits `n j`,
`1` iff the operands differ at limb `j` or above; `f k = n k − n (k+1)` one-hot at the top
differing limb; the limbs above it equal; and `m₋₁[k] − 1 − x[k]` there a `B`-bit number.

The model takes `m₋₁`'s limbs as linear combinations `mv`. The exported templates are the
harness calls `require_lt::<3, 86>`, `<3, 85>`, `<4, 64>`, `<8, 32>` and `<24, 86>` on fresh
`x` and `m₋₁` (`mv = plugM L`); `Formal/RequireLt{3x86,3x85,4x64,8x32,24x86}.lean` show each
equal to the model by `decide +kernel` and state its theorems. Production passes `m₋₁` as a constant, so its rows
are those templates with constant plugs (`Template.soundness_inst`, checked by
`cargo xtask lean-export --coverage`). The generic theorems hold for any `L ≤ 32`,
`B + 3 < 253`, but bind the gadget only at those widths:

* **soundness**: if `x`'s limbs are below `2^B`, every assignment satisfying the rows has
  `x ≤ m₋₁`. Nothing is assumed about `m₋₁`: the rows pin its limbs at and above the
  first difference, and its lower limbs only add to it.

The input assumption, `x`'s limbs `< 2^B`, is each caller's: `mul_divmod`'s `range_bits`
on `r`, `sub2`'s and `assert_canonical`'s `range_check_limbs`, the callers of `on_curve_k1` /
`on_curve_r1` (`unpack8`), ed25519 `point_in`'s `to_bits::<85>` (in `limbs32`), secp256k1's
`unpack` and secp256r1's `unpack4` (bit decompositions), and `eddsa_verify`'s scalar bits
(`formal/coverage-allowlist.txt` names the LC-plug ones).
-/

namespace Xark.Templates

open Xark.Template

/-- A field literal's canonical value, for `simp` (the generated constant obligations). -/
@[scoped simp] theorem val_ofNat (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n : F)).val =
    n % 21888242871839275222246405745257275088548364400416034343698204186575808495617 := by
  rw [← Nat.cast_ofNat, ZMod.val_natCast]; rfl

@[scoped simp] theorem val_one : (1 : F).val = 1 := by
  rw [← Nat.cast_one, ZMod.val_natCast]; rfl

end Xark.Templates

namespace Xark.Templates.RequireLt

open Xark.Template Xark.R1cs Xark.Templates.Add32

/-! ### The parametric model -/

section Model

variable (L B : ℕ) (mv : ℕ → LC)

/-- `l + c · m`, as the frontend writes it: `m`'s constant folded in, its terms appended. -/
def addTo (l m : LC) (c : F) : LC :=
  ⟨l.const + c * m.const, l.terms ++ m.terms.map fun t => (c * t.1, t.2)⟩

/-- `m₋₁` given as variables, the plugs after `x`'s. -/
def plugM (j : ℕ) : LC := ⟨0, [(1, .plug (L + j))]⟩

/-- `n j`, `1` iff `x` and `m₋₁` differ at limb `j` or above; the `j`-th hint from the top. -/
def nv (j : ℕ) : TVar := .wit (L - 1 - j)
/-- `f k · (m₋₁[k] − 1 − x[k])`. -/
def pv (k : ℕ) : TVar := .wit (4 * L - 1 + k)
/-- Bit `i` of the selected difference. -/
def bv (i : ℕ) : TVar := .wit (5 * L - 1 + 2 * i)

/-- `f k = n k − n (k+1)`, with `n L = 0`. -/
def fLC (k : ℕ) : LC :=
  if k + 1 < L then ⟨0, [(-1, nv L (k + 1)), (1, nv L k)]⟩ else ⟨0, [(1, nv L k)]⟩

/-- `m₋₁[k] − 1 − x[k]`; `mv k` is limb `k` of `m₋₁`. -/
def dLC (k : ℕ) : LC := addTo ⟨-1, [(-1, .plug k)]⟩ (mv k) 1

/-- The `i`-th hint's operand, `j = L−1−i`:
`m₋₁[j] − x[j] − 1 + 2^(B+1)·n (j+1) + 2^(B+2)`. -/
def tLC (i : ℕ) : LC :=
  let l := addTo ⟨((2 ^ (B + 2) - 1 : ℕ) : F), [(-1, .plug (L - 1 - i))]⟩ (mv (L - 1 - i)) 1
  ⟨l.const, l.terms ++ (if i = 0 then [] else [(((2 ^ (B + 1) : ℕ) : F), .wit (i - 1))])⟩

/-- `Σ_k f k · (m₋₁[k] − 1 − x[k])`. -/
def pSum : LC := ⟨0, (List.range L).map fun k => (1, pv L k)⟩

def sq (l : LC) : Row := ⟨l, l, l⟩

def eqRow (j : ℕ) : Row :=
  ⟨⟨1, [(-1, nv L j)]⟩, addTo ⟨0, [(1, .plug j)]⟩ (mv j) (-1), ⟨0, []⟩⟩

def prodRow (k : ℕ) : Row := ⟨fLC L k, dLC mv k, ⟨0, [(1, pv L k)]⟩⟩

def recompRow : Row :=
  ⟨⟨0, (List.range L).map (fun k => (-1, pv L k)) ++
      (List.range B).map fun i => (((2 ^ i : ℕ) : F), bv L i)⟩, ⟨1, []⟩, ⟨0, []⟩⟩

def rows : List Row :=
  (List.range L).map (fun j => sq ⟨0, [(1, nv L j)]⟩) ++
  (List.range (L - 1)).map (fun k => sq (fLC L k)) ++
  (List.range L).map (eqRow L mv) ++ (List.range L).map (prodRow L mv) ++
  (List.range B).map (fun i => sq ⟨0, [(1, bv L i)]⟩) ++ [recompRow L B]

def inputs : List LC :=
  (List.range L).map (fun j => ⟨0, [(1, .plug j)]⟩) ++ (List.range L).map mv

/-- A template is the model at `(L, B)` with `m₋₁`'s limbs `mv`. -/
def Is (t : Template) : Prop :=
  t.inputs = inputs L mv ∧ t.outputs = [] ∧ t.rows = rows L B mv

instance (t : Template) : Decidable (Is L B mv t) := by unfold Is; infer_instance

end Model

/-! ### Limb vectors over the naturals -/

/-- `Σ_{j<n} a j · 2^(B·j)`, the number with limbs `a` in base `2^B`. -/
def limbs (a : ℕ → ℕ) (B n : ℕ) : ℕ := ∑ j ∈ Finset.range n, a j * 2 ^ (B * j)

/-- Limbs below `2^B` make a number below `2^(B·n)`. -/
theorem limbs_lt {a : ℕ → ℕ} {B n : ℕ} (ha : ∀ j < n, a j < 2 ^ B) :
    limbs a B n < 2 ^ (B * n) := by
  induction n with
  | zero => simp [limbs]
  | succ n ih =>
    rw [limbs, Finset.sum_range_succ, ← limbs]
    have h1 := ih fun j hj => ha j (by omega)
    have h3 : (a n + 1) * 2 ^ (B * n) ≤ 2 ^ B * 2 ^ (B * n) :=
      Nat.mul_le_mul_right _ (ha n (by omega))
    rw [show B * (n + 1) = B * n + B by ring, pow_add]
    nlinarith

/-- Lexicographic order: equal limbs above `k`, a smaller limb at `k` and limbs of `a`
below `2^B` under it make `a` the smaller number, whatever `b`'s lower limbs are. -/
theorem limbs_lt_of_lex {a b : ℕ → ℕ} {B n k : ℕ} (hk : k < n) (ha : ∀ j < k, a j < 2 ^ B)
    (hab : a k < b k) (heq : ∀ j, k < j → j < n → a j = b j) : limbs a B n < limbs b B n := by
  have split : ∀ c : ℕ → ℕ, limbs c B n =
      limbs c B k + c k * 2 ^ (B * k) + ∑ j ∈ Finset.Ico (k + 1) n, c j * 2 ^ (B * j) := by
    intro c
    rw [limbs, ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ n by omega),
      Finset.sum_range_succ, limbs]
  rw [split a, split b]
  have hup : ∑ j ∈ Finset.Ico (k + 1) n, a j * 2 ^ (B * j) =
      ∑ j ∈ Finset.Ico (k + 1) n, b j * 2 ^ (B * j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_Ico] at hj; rw [heq j (by omega) hj.2]
  have hlo := limbs_lt (a := a) (B := B) (n := k) ha
  have h3 : (a k + 1) * 2 ^ (B * k) ≤ b k * 2 ^ (B * k) := Nat.mul_le_mul_right _ hab
  have := Nat.zero_le (limbs b B k)
  nlinarith

/-! ### The comparison over the field -/

instance : Fact (Nat.Prime r) := bn254_r_prime

theorem two_pow_lt_r' {e : ℕ} (he : e ≤ 253) : 2 ^ e < r :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) he) two_pow_lt_r

/-- What the rows say, read as equations between field values, implies `x ≤ m₋₁`:
`n` the difference flags (`n L = 0`), `P` the selected products, `b` the difference's bits. -/
theorem core_sound {L B : ℕ} (hL : L ≤ 32) (hB : B + 3 < 253) (X M n P b : ℕ → F)
    (hn : n L = 0) (hx : ∀ j < L, (X j).val < 2 ^ B)
    (hf : ∀ k < L, (n k - n (k + 1)) * (n k - n (k + 1)) = n k - n (k + 1))
    (h0 : n 0 * n 0 = n 0)
    (heq : ∀ j < L, (1 - n j) * (X j - M j) = 0)
    (hp : ∀ k < L, (n k - n (k + 1)) * (M k - 1 - X k) = P k)
    (hb : ∀ i < B, b i * b i = b i)
    (hs : ∑ i ∈ Finset.range B, ((2 ^ i : ℕ) : F) * b i = ∑ k ∈ Finset.range L, P k) :
    limbs (fun j => (X j).val) B L ≤ limbs (fun j => (M j).val) B L := by
  set f : ℕ → F := fun k => n k - n (k + 1) with hfdef
  have fbit : ∀ k < L, IsBit (f k) := fun k hk => isBit_of_mul_self (hf k hk)
  have tele : ∀ j, n j = n 0 - ∑ k ∈ Finset.range j, f k := fun j => by
    rw [hfdef, Finset.sum_range_sub']; ring
  have hn0 : n 0 = ∑ k ∈ Finset.range L, f k := by
    have := tele L; rw [hn] at this; linear_combination -this
  have hcast : ∑ k ∈ Finset.range L, f k = ((∑ k ∈ Finset.range L, (f k).val : ℕ) : F) := by
    push_cast; exact Finset.sum_congr rfl fun k _ => (ZMod.natCast_zmod_val _).symm
  have hle : ∑ k ∈ Finset.range L, (f k).val ≤ L := by
    calc _ ≤ ∑ _k ∈ Finset.range L, 1 :=
          Finset.sum_le_sum fun k hk => isBit_val (fbit k (Finset.mem_range.mp hk))
      _ = L := by simp
  have hr : 32 < r := lt_of_lt_of_le (by norm_num) (two_pow_lt_r' (e := 6) (by norm_num)).le
  have hsum01 : ∑ k ∈ Finset.range L, (f k).val = 0 ∨ ∑ k ∈ Finset.range L, (f k).val = 1 := by
    rcases isBit_of_mul_self h0 with h | h
    · left; exact nat_eq_of_cast (by omega) (by omega) (by rw [← hcast, ← hn0, h]; simp)
    · right; exact nat_eq_of_cast (by omega) (by omega) (by rw [← hcast, ← hn0, h]; simp)
  have hval0 : ∀ k < L, (f k).val = 0 → f k = 0 := fun k _ h => (ZMod.val_eq_zero _).mp h
  rcases hsum01 with h | h
  · -- no difference: every limb equal
    have hz : ∀ k < L, f k = 0 := fun k hk =>
      hval0 k hk ((Finset.sum_eq_zero_iff.mp h) k (Finset.mem_range.mpr hk))
    have hn0' : n 0 = 0 := by
      rw [hn0]; exact Finset.sum_eq_zero fun k hk => hz k (by simpa using hk)
    refine le_of_eq (Finset.sum_congr rfl fun j hj => ?_)
    have hj := Finset.mem_range.mp hj
    have hnj : n j = 0 := by
      rw [tele j, hn0', Finset.sum_eq_zero fun k hk => hz k (by simp at hk; omega)]; simp
    have := heq j hj
    rw [hnj, sub_zero, one_mul, sub_eq_zero] at this
    simp only [this]
  · -- the first difference is at `k0`
    obtain ⟨k0, hk0, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by rw [h]; exact one_ne_zero : ∑ k ∈ Finset.range L, (f k).val ≠ 0)
    have hk0L := Finset.mem_range.mp hk0
    have hf1 : f k0 = 1 := (fbit k0 hk0L).resolve_left fun h' => hne (by simp [h'])
    have hrest := Finset.add_sum_erase _ (fun k => (f k).val) hk0
    rw [h, show (f k0).val = 1 by simp [hf1]] at hrest
    have hfk : ∀ k < L, f k = if k = k0 then 1 else 0 := by
      intro k hk
      split_ifs with hkk
      · rw [hkk, hf1]
      · exact hval0 k hk ((Finset.sum_eq_zero_iff.mp
          (by omega : ∑ x ∈ (Finset.range L).erase k0, (f x).val = 0)) k
          (Finset.mem_erase.mpr ⟨hkk, Finset.mem_range.mpr hk⟩))
    have hsumj : ∀ j ≤ L, ∑ k ∈ Finset.range j, f k = if k0 < j then 1 else 0 := by
      intro j hj
      rw [Finset.sum_congr rfl fun k hk => hfk k (by simp at hk; omega)]
      simp [Finset.sum_ite_eq']
    have hn01 : n 0 = 1 := by rw [hn0, hsumj L le_rfl, if_pos hk0L]
    have above : ∀ j, k0 < j → j < L → X j = M j := by
      intro j hkj hj
      have hnj : n j = 0 := by rw [tele j, hn01, hsumj j hj.le, if_pos hkj]; simp
      have := heq j hj
      rw [hnj, sub_zero, one_mul, sub_eq_zero] at this
      exact this
    have hP : ∑ k ∈ Finset.range L, P k = M k0 - 1 - X k0 := by
      rw [Finset.sum_congr rfl fun k hk => (hp k (Finset.mem_range.mp hk)).symm]
      rw [Finset.sum_congr rfl fun k hk =>
        show f k * (M k - 1 - X k) = if k = k0 then M k - 1 - X k else 0 by
          rw [hfk k (Finset.mem_range.mp hk)]; split_ifs <;> simp]
      simp [Finset.sum_ite_eq', hk0L]
    have hbits : ∀ i < B, (b i).val ≤ 1 := fun i hi => isBit_val (isBit_of_mul_self (hb i hi))
    have hD := word_lt (fun i => (b i).val) B hbits
    rw [cast_sum (fun i => 2 ^ i) b, hP] at hs
    set D := ∑ i ∈ Finset.range B, 2 ^ i * (b i).val
    have hM : M k0 = (((X k0).val + 1 + D : ℕ) : F) := by
      rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val, hs, Nat.cast_one]; ring
    have hxk := hx k0 hk0L
    have hMv : (M k0).val = (X k0).val + 1 + D := by
      rw [hM, ZMod.val_natCast_of_lt]
      have := two_pow_lt_r' (e := B + 2) (by omega)
      rw [pow_add] at this; omega
    refine (limbs_lt_of_lex hk0L (fun j hj => hx j (by omega)) (by omega)
      fun j h1 h2 => by simp only [above j h1 h2]).le

/-- The `i`-th flag's hint, read over the naturals: bit `B + 2` of
`2^(B+2) − 1 − X + M + 2^(B+1)·c` is `1` iff `c = 1` or `X < M`. -/
theorem bit_step {B : ℕ} (hB : B + 3 < 253) {X M : F} {c : ℕ} (hx : X.val < 2 ^ B)
    (hm : M.val < 2 ^ B) (hc : c ≤ 1) :
    bitOf (((2 ^ (B + 2) - 1 : ℕ) : F) - X + M + ((2 ^ (B + 1) : ℕ) : F) * (c : F)) (B + 2) =
      if c = 1 ∨ X.val < M.val then 1 else 0 := by
  conv_lhs => rw [← ZMod.natCast_zmod_val X, ← ZMod.natCast_zmod_val M]
  set xv := X.val
  set mv := M.val
  have h2 : 2 ^ (B + 1) = 2 * 2 ^ B := by rw [pow_succ]; ring
  have h4 : 2 ^ (B + 2) = 4 * 2 ^ B := by rw [pow_add]; ring
  have h8 : 2 ^ (B + 3) = 8 * 2 ^ B := by rw [pow_add]; ring
  have hr := two_pow_lt_r' (e := B + 3) (by omega)
  have hP1 : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have hcq : (c = 0 ∧ 2 ^ (B + 1) * c = 0) ∨ (c = 1 ∧ 2 ^ (B + 1) * c = 2 ^ (B + 1)) := by
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simp
  set T := 2 ^ (B + 2) - 1 - xv + mv + 2 ^ (B + 1) * c with hT
  have hTnat : T + xv = (2 ^ (B + 2) - 1) + mv + 2 ^ (B + 1) * c := by omega
  have hcast : ((2 ^ (B + 2) - 1 : ℕ) : F) - (xv : F) + (mv : F) + ((2 ^ (B + 1) : ℕ) : F) * (c : F)
      = (T : F) := by
    have := congrArg (Nat.cast : ℕ → F) hTnat
    simp only [Nat.cast_add, Nat.cast_mul] at this
    linear_combination -this
  rw [hcast, bitOf, ZMod.val_natCast_of_lt (by omega : T < r)]
  by_cases hcond : c = 1 ∨ xv < mv
  · have e : T = 2 ^ (B + 2) + (T - 2 ^ (B + 2)) := by omega
    rw [if_pos hcond, e, Nat.testBit_two_pow_add_eq,
      Nat.testBit_lt_two_pow (by omega : T - 2 ^ (B + 2) < 2 ^ (B + 2))]
    rfl
  · rw [if_neg hcond, Nat.testBit_lt_two_pow (by omega : T < 2 ^ (B + 2))]
    rfl

/-! ### The exported rows' meaning -/

section Rows

variable {L B : ℕ} {mv : ℕ → LC}

theorem eval_addTo (l m : LC) (c : F) (σ : TVar → F) :
    (addTo l m c).eval σ = l.eval σ + c * m.eval σ := by
  have h : (m.terms.map fun x => c * x.1 * σ x.2).sum =
      c * (m.terms.map fun t => t.1 * σ t.2).sum := by
    rw [← List.sum_map_mul_left]; simp [mul_assoc]
  simp [addTo, LC.eval, List.map_map, Function.comp_def, h]; ring

theorem eval_append (l : LC) (e : List (F × TVar)) (σ : TVar → F) :
    (⟨l.const, l.terms ++ e⟩ : LC).eval σ = l.eval σ + (⟨0, e⟩ : LC).eval σ := by
  simp [LC.eval, List.map_append, List.sum_append]; ring

/-- `n j` under `σ`, `0` from limb `L` up. -/
def nval (L : ℕ) (σ : TVar → F) (j : ℕ) : F := if j < L then σ (nv L j) else 0

theorem eval_fLC (σ : TVar → F) {k : ℕ} (hk : k < L) :
    (fLC L k).eval σ = nval L σ k - nval L σ (k + 1) := by
  by_cases h : k + 1 < L
  · simp [fLC, nval, h, hk, LC.eval]; ring
  · simp [fLC, nval, h, hk, LC.eval]

theorem eval_dLC (σ : TVar → F) (k : ℕ) :
    (dLC mv k).eval σ = (mv k).eval σ - 1 - σ (.plug k) := by
  rw [dLC, eval_addTo]; simp [LC.eval]; ring

theorem eval_tLC (σ : TVar → F) {j : ℕ} (hj : j < L) :
    (tLC L B mv (L - 1 - j)).eval σ = ((2 ^ (B + 2) - 1 : ℕ) : F) - σ (.plug j) +
      (mv j).eval σ + ((2 ^ (B + 1) : ℕ) : F) * nval L σ (j + 1) := by
  have e1 : L - 1 - (L - 1 - j) = j := by omega
  have ha := eval_addTo ⟨((2 ^ (B + 2) - 1 : ℕ) : F), [(-1, .plug j)]⟩ (mv j) 1 σ
  unfold tLC
  rw [e1]
  rw [eval_append, ha]
  by_cases h0 : L - 1 - j = 0
  · have h1 : ¬ j + 1 < L := by omega
    simp [h0, h1, nval, LC.eval]; ring
  · have h1 : j + 1 < L := by omega
    have e2 : L - 1 - j - 1 = L - 1 - (j + 1) := by omega
    simp [h0, h1, nval, LC.eval, e2, nv]; ring

theorem eval_pSum (σ : TVar → F) :
    (pSum L).eval σ = ∑ k ∈ Finset.range L, σ (pv L k) := by
  simp [pSum, LC.eval, List.map_map, Function.comp_def, sum_map_range]

theorem ins_x {t : Template} (ht : Is L B mv t) (σ : TVar → F) {j : ℕ} (hj : j < L) :
    (t.ins σ).getD j 0 = σ (.plug j) := by
  rw [Template.ins, ht.1]
  simp only [inputs, List.map_append, List.map_map, Function.comp_def,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hj)]
  simp [LC.eval, hj]

theorem ins_m {t : Template} (ht : Is L B mv t) (σ : TVar → F) {j : ℕ} (hj : j < L) :
    (t.ins σ).getD (L + j) 0 = (mv j).eval σ := by
  rw [Template.ins, ht.1]
  simp [inputs, List.map_map, Function.comp_def, List.getD_eq_getElem?_getD, hj,
    List.getElem_append_right]

theorem sat_rows {t : Template} (ht : Is L B mv t) {σ : TVar → F} (h : t.Sat σ) :
    ∀ row ∈ rows L B mv, row.Sat σ := by
  have := h; rwa [Template.Sat, ht.2.2] at this

/-- The input assumption of soundness: `x`'s limbs are below `2^B`. -/
def Assumptions (L B : ℕ) (ins : List F) : Prop := ∀ j < L, (ins.getD j 0).val < 2 ^ B

theorem assumptions_of_take {L B : ℕ} {ins : List F} (h : ∀ v ∈ ins.take L, v.val < 2 ^ B) :
    Assumptions L B ins := by
  intro j hj
  rcases lt_or_ge j ins.length with h1 | h1
  · rw [List.getD_eq_getElem _ _ h1]
    have hjt : j < (ins.take L).length := by rw [List.length_take]; omega
    simpa using h _ (List.getElem_mem hjt)
  · rw [List.getD_eq_default _ _ h1]; simp

/-- The spec: `x ≤ m₋₁`, the two operands read as numbers in base `2^B`. -/
def Spec (L B : ℕ) (ins : List F) : Prop :=
  limbs (fun j => (ins.getD j 0).val) B L ≤ limbs (fun j => (ins.getD (L + j) 0).val) B L

theorem spec_iff {t : Template} (ht : Is L B mv t) (σ : TVar → F) :
    Spec L B (t.ins σ) ↔ limbs (fun j => (σ (.plug j)).val) B L ≤
      limbs (fun j => ((mv j).eval σ).val) B L := by
  have e1 : limbs (fun j => ((t.ins σ).getD j 0).val) B L =
      limbs (fun j => (σ (.plug j)).val) B L :=
    Finset.sum_congr rfl fun j hj => by simp only; rw [ins_x ht σ (by simpa using hj)]
  have e2 : limbs (fun j => ((t.ins σ).getD (L + j) 0).val) B L =
      limbs (fun j => ((mv j).eval σ).val) B L :=
    Finset.sum_congr rfl fun j hj => by simp only; rw [ins_m ht σ (by simpa using hj)]
  rw [Spec, e1, e2]

/-- **Soundness.** If `x`'s limbs are below `2^B`, every assignment satisfying the rows has
`x ≤ m₋₁`. -/
theorem soundness {t : Template} (ht : Is L B mv t) (hL : 0 < L) (hL32 : L ≤ 32)
    (hB : B + 3 < 253)
    (σ : TVar → F) (ha : Assumptions L B (t.ins σ)) (h : t.Sat σ) : Spec L B (t.ins σ) := by
  have hrow := sat_rows ht h
  rw [spec_iff ht]
  have lists : ∀ {α} (l : List α) (f : α → Row) (a : α), a ∈ l → f a ∈ l.map f :=
    fun l f a ha => List.mem_map_of_mem ha
  refine core_sound hL32 hB (fun j => σ (.plug j)) (fun j => (mv j).eval σ) (nval L σ)
    (fun k => σ (pv L k)) (fun i => σ (bv L i)) (by simp [nval])
    (fun j hj => by rw [← ins_x ht σ hj]; exact ha j hj) ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    by_cases h : k + 1 < L
    · have := hrow _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _
          (lists _ (fun k => sq (fLC L k)) k (List.mem_range.mpr (by omega))))))))
      simpa only [Row.Sat, sq, eval_fLC σ hk] using this
    · have := hrow _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _
          (lists _ (fun j => sq ⟨0, [(1, nv L j)]⟩) k (List.mem_range.mpr hk)))))))
      simp only [Row.Sat, sq, LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        at this
      simp only [nval, if_pos hk, if_neg h, sub_zero]
      linear_combination this
  · have := hrow _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _
        (lists _ (fun j => sq ⟨0, [(1, nv L j)]⟩) 0 (List.mem_range.mpr hL)))))))
    simp only [Row.Sat, sq, LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      at this
    simp only [nval, if_pos hL]
    linear_combination this
  · intro j hj
    have := hrow _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (lists _ (eqRow L mv) j (List.mem_range.mpr hj))))))
    simp only [Row.Sat, eqRow, eval_addTo] at this
    generalize (mv j).eval σ = M at this ⊢
    simp only [LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    simp only [nval, if_pos hj]
    linear_combination this
  · intro k hk
    have := hrow _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (lists _ (prodRow L mv) k (List.mem_range.mpr hk)))))
    simp only [Row.Sat, prodRow] at this
    rw [eval_fLC σ hk, eval_dLC] at this
    generalize (mv k).eval σ = M at this ⊢
    simp only [LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    linear_combination this
  · intro i hi
    have := hrow _ (List.mem_append_left _ (List.mem_append_right _
      (lists _ (fun i => sq ⟨0, [(1, bv L i)]⟩) i (List.mem_range.mpr hi))))
    simp only [Row.Sat, sq, LC.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      at this
    linear_combination this
  · have := hrow _ (List.mem_append_right _ (List.mem_singleton_self _))
    simp only [Row.Sat, recompRow, LC.eval, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, sum_map_range, List.map_nil, List.sum_nil, neg_mul, one_mul,
      Finset.sum_neg_distrib] at this
    linear_combination this

end Rows

end Xark.Templates.RequireLt
