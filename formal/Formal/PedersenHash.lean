/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.PedersenHash
import Formal.PedersenData
import Formal.GrumpkinOrder
import Formal.Add32
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_pedersen::pedersen_hash`, proven over its exported rows

`Formal/Templates/PedersenHash.lean` is the R1CS the frontend emits for one call of
`xark_pedersen::pedersen_hash` (`cargo xtask lean-export pedersen_hash`), 774 rows. For
each scalar `mₛ` (`s = 0, 1`): 128 booleanity rows and the recomposition `Σ 2ⁱ·bᵢ = mₛ`;
42 three-bit windows, each a `lookup3_xy` (bellman/sapling-crypto, 3 rows) into the
constant table `(j + 2)·8ʷ·Gₛ`; a two-bit window 42 (1 row); 42 incomplete adds (3 rows
each) summing the entries; and an incomplete add of the constant `−off·Gₛ`, where
`off = Σ_{w≤42} 2·8ʷ`. Then a guard row `(x₁ − x₀)·inv = 1` and the incomplete add
`m₀·G₀ + m₁·G₁`. The model below spells these rows out by variable index, and
`rows_eq` (`decide +kernel`) shows the export equals it in normal form.

* **Sound** (`soundness`, no input assumptions): every assignment satisfying the rows
  has scalars `m₀, m₁ ∈ [1, 2¹²⁸)` and outputs the affine coordinates of
  `m₀·G₀ + m₁·G₁`. The rows enforce the range themselves, so the template rejects
  `m = 0` and anything else out of range rather than computing a wrong point.
  Every incomplete add is safe: before window `w` the accumulator is `S·Gₛ` with
  `S < 2·8ʷ ≤ (d + 2)·8ʷ`, the entry's multiple (`window_xne`), all multiples stay below
  `11·8⁴² < q` (`eleven_lt_q`), and `Gₛ` has prime order `q` (`order`, from
  `Formal/GrumpkinOrder.lean`), so equal `x` would force `q` to divide a positive
  number below `q`. The correction add is safe for `m ≥ 1` the same way and the rows
  reject `m = 0` there (`corr_sound`). The final add's `x₀ ≠ x₁` is the guard row.

The window tables are constants the export pins: `tab`/`corr` read the generators'
certified addition chains in `Formal/PedersenData.lean`, and `chainFacts_of` (kernel
checks in chunks) shows that each table entry is the claimed multiple of `Gₛ` (`multiples`, `tab_pt`,
`corr_pt`). Design after clean-orchard's fixed-base proofs (zksecurity/clean-orchard
@ b5b93ee), with the Grumpkin order proven here (Pratt certificate, no axiom).
-/

namespace Xark.Templates.PedersenHash

open Xark.Template Xark.R1cs Xark.Grumpkin Xark.PedersenData

/-! ### Linear combinations, built naively and compared in normal form -/

/-- The variable `wit j`. -/
def v (j : ℕ) : LC := ⟨0, [(1, .wit j)]⟩

/-- The constant `x`. -/
def k (x : F) : LC := ⟨x, []⟩

def lcAdd (a b : LC) : LC := ⟨a.const + b.const, a.terms ++ b.terms⟩
def lcSmul (x : F) (a : LC) : LC := ⟨x * a.const, a.terms.map fun t => (x * t.1, t.2)⟩
def lcSub (a b : LC) : LC := lcAdd a (lcSmul (-1) b)

scoped infixl:65 " +' " => lcAdd
scoped infixl:65 " -' " => lcSub
scoped infixr:73 " •' " => lcSmul

/-- A variable's position in the normal form. -/
def key : TVar → ℕ
  | .plug i => 2 * i
  | .wit j => 2 * j + 1

/-- Insert a term into terms sorted by `key`, merging a variable's coefficients and
dropping zeros. -/
def ins (t : F × TVar) : List (F × TVar) → List (F × TVar)
  | [] => if t.1 = 0 then [] else [t]
  | u :: l =>
    if t.2 = u.2 then (if t.1 + u.1 = 0 then l else (t.1 + u.1, u.2) :: l)
    else if key t.2 < key u.2 then (if t.1 = 0 then u :: l else t :: u :: l)
    else u :: ins t l

/-- The normal form: terms sorted by variable, one per variable, none zero. -/
def norm (a : LC) : LC := ⟨a.const, a.terms.foldr ins []⟩

def Row.norm (x : Row) : Row := ⟨PedersenHash.norm x.a, PedersenHash.norm x.b, PedersenHash.norm x.c⟩

/-! ### The model: the rows `pedersen_hash` emits, by variable index -/

/-- The window tables: `tab s w j` is entry `j` of window `w` of generator `s`, and
`corr s` the correction point, as points of the chains in `Formal/PedersenData.lean`. -/
def pts : ℕ → List (ℕ × ℕ)
  | 0 => points [gen0] chain0
  | _ => points [gen1] chain1

def offIdx : ℕ → ℕ
  | 0 => offIdx0
  | _ => offIdx1

def tab (s w j : ℕ) : F × F :=
  let p := (pts s).getD (1 + 8 * w + j) (0, 0)
  ((p.1 : F), (p.2 : F))

def corr (s : ℕ) : F × F :=
  let p := (pts s).getD (offIdx s) (0, 0)
  ((p.1 : F), -(p.2 : F))

/-- `bellman lookup3_xy`'s two linear parts for coordinate values `t`: the value is
`low + b₀ · high` with `b₁₂ = b₁ · b₂`. -/
def low (t : ℕ → F) (b1 b2 b12 : LC) : LC :=
  k (t 0) +' (t 2 - t 0) •' b1 +' (t 4 - t 0) •' b2 +' (t 6 - t 4 - t 2 + t 0) •' b12

def high (t : ℕ → F) (b1 b2 b12 : LC) : LC :=
  k (t 1 - t 0) +' (t 3 - t 2 - t 1 + t 0) •' b1 +' (t 5 - t 4 - t 1 + t 0) •' b2 +'
    (t 7 - t 6 - t 5 + t 4 - t 3 + t 2 + t 1 - t 0) •' b12

/-- The 2-bit lookup's value for coordinate values `t`, with `b₀₁ = b₀ · b₁`. -/
def look2 (t : ℕ → F) (b0 b1 b01 : LC) : LC :=
  k (t 0) +' (t 1 - t 0) •' b0 +' (t 2 - t 0) •' b1 +' (t 3 - t 2 - t 1 + t 0) •' b01

/-- A point as two linear combinations. -/
abbrev P := LC × LC

/-- `lookup3` of window `w` of generator `s` on bits `b`, allocating from `a`. -/
def look3Rows (s w b a : ℕ) : List Row :=
  [⟨v (b + 1), v (b + 2), v a⟩,
   ⟨v b, high (fun j => (tab s w j).1) (v (b + 1)) (v (b + 2)) (v a), v (a + 1)⟩,
   ⟨v b, high (fun j => (tab s w j).2) (v (b + 1)) (v (b + 2)) (v a), v (a + 2)⟩]

def look3Out (s w b a : ℕ) : P :=
  (low (fun j => (tab s w j).1) (v (b + 1)) (v (b + 2)) (v a) +' v (a + 1),
   low (fun j => (tab s w j).2) (v (b + 1)) (v (b + 2)) (v a) +' v (a + 2))

/-- The last window's 2-bit lookup. -/
def look2Rows (b a : ℕ) : List Row := [⟨v b, v (b + 1), v a⟩]

def look2Out (s w b a : ℕ) : P :=
  (look2 (fun j => (tab s w j).1) (v b) (v (b + 1)) (v a),
   look2 (fun j => (tab s w j).2) (v b) (v (b + 1)) (v a))

/-- The incomplete add `p + q`, allocating from `a`: `λ = a + 7`, `x₃ = a + 8`,
`y₃ = a + 9`. -/
def addRows (p q : P) (a : ℕ) : List Row :=
  [⟨v (a + 7), q.1 -' p.1, q.2 -' p.2⟩,
   ⟨v (a + 7), v (a + 7), v (a + 8) +' p.1 +' q.1⟩,
   ⟨v (a + 7), p.1 -' v (a + 8), v (a + 9) +' p.2⟩]

def addOut (a : ℕ) : P := (v (a + 8), v (a + 9))

/-- Scalar `s`'s variables start at `942 · s`: its 128 bits, 128 merged booleanity
products, then the multiplication. -/
def base (s : ℕ) : ℕ := 942 * s

/-- The plug holding scalar `s`. -/
def plug (s : ℕ) : LC := ⟨0, [(1, .plug s)]⟩

def bitsLC (s : ℕ) : LC := ⟨0, (List.range 128).map fun i => (((2 ^ i : ℕ) : F), .wit (base s + i))⟩

def decompRows (s : ℕ) : List Row :=
  (List.range 128).map (fun i => ⟨v (base s + i), v (base s + i), v (base s + i)⟩) ++
    [⟨bitsLC s -' plug s, k 1, k 0⟩]

/-- Window `w`'s lookup allocates from `win s w`, its add from `win s w + 3`. -/
def win (s w : ℕ) : ℕ := base s + 256 + 3 + 16 * (w - 1)

/-- The accumulator after window `w` (`w ≥ 1`). -/
def acc (s w : ℕ) : P := addOut (win s w + 3)

/-- The accumulator before window `w + 1`: window 0's lookup, or an add's output. -/
def accBefore (s w : ℕ) : P := if w = 0 then look3Out s 0 (base s) (base s + 256) else acc s w

/-- Windows `1 ≤ w ≤ 41`: a lookup and an add. -/
def winRows (s w : ℕ) : List Row :=
  look3Rows s w (base s + 3 * w) (win s w) ++
    addRows (accBefore s (w - 1)) (look3Out s w (base s + 3 * w) (win s w)) (win s w + 3)

/-- Window 42 (bits 126, 127) allocates from `win s 42`, its add from `win s 42 + 1`;
the correction add from `win s 42 + 14`. -/
def lastRows (s : ℕ) : List Row :=
  look2Rows (base s + 126) (win s 42) ++
    addRows (acc s 41) (look2Out s 42 (base s + 126) (win s 42)) (win s 42 + 1) ++
    addRows (addOut (win s 42 + 1)) (k (corr s).1, k (corr s).2) (win s 42 + 14)

/-- `mᵢ · Gᵢ`'s point. -/
def term (s : ℕ) : P := addOut (win s 42 + 14)

def mulRows (s : ℕ) : List Row :=
  decompRows s ++ look3Rows s 0 (base s) (base s + 256) ++
    (List.range 41).flatMap (fun j => winRows s (j + 1)) ++ lastRows s

/-- The guard `(x₁ − x₀) · inv = 1` and the final add, from `1884`. -/
def modelRows : List Row :=
  mulRows 0 ++ mulRows 1 ++ [⟨(term 1).1 -' (term 0).1, v 1884, k 1⟩] ++ addRows (term 0) (term 1) 1886

set_option maxRecDepth 100000 in
theorem rows_eq : template.rows.map Row.norm = modelRows.map Row.norm := by
  decide +kernel

/-! ### Values of the naive operations and of normal forms -/

section eval

variable (σ : TVar → F)

@[simp] theorem eval_v (j : ℕ) : (v j).eval σ = σ (.wit j) := by simp [v, LC.eval]

@[simp] theorem eval_k (x : F) : (k x).eval σ = x := by simp [k, LC.eval]

@[simp] theorem eval_add (a b : LC) : (a +' b).eval σ = a.eval σ + b.eval σ := by
  simp only [lcAdd, LC.eval, List.map_append, List.sum_append]; ring

@[simp] theorem eval_smul (x : F) (a : LC) : (x •' a).eval σ = x * a.eval σ := by
  simp only [lcSmul, LC.eval, List.map_map, Function.comp_def, mul_add]
  rw [← List.sum_map_mul_left]; simp only [mul_assoc]

@[simp] theorem eval_sub (a b : LC) : (a -' b).eval σ = a.eval σ - b.eval σ := by
  simp [lcSub]; ring

@[simp] theorem eval_plug (s : ℕ) : (plug s).eval σ = σ (.plug s) := by simp [plug, LC.eval]

theorem sum_ins (t : F × TVar) (l : List (F × TVar)) :
    ((ins t l).map fun u => u.1 * σ u.2).sum = t.1 * σ t.2 + (l.map fun u => u.1 * σ u.2).sum := by
  induction l with
  | nil => unfold ins; split_ifs with h <;> simp [h]
  | cons u l ih =>
    unfold ins
    split_ifs with h1 h2 h3 h4
    · simp only [List.map_cons, List.sum_cons, h1]; linear_combination (-σ u.2) * h2
    · simp only [List.map_cons, List.sum_cons, h1]; ring
    · simp [h4]
    · simp
    · simp only [List.map_cons, List.sum_cons, ih]; ring

@[simp] theorem eval_norm (a : LC) : (PedersenHash.norm a).eval σ = a.eval σ := by
  simp only [PedersenHash.norm, LC.eval]
  congr 1
  induction a.terms with
  | nil => rfl
  | cons t l ih => rw [List.foldr_cons, sum_ins, ih]; simp

theorem row_norm_sat (x : Row) : (Row.norm x).Sat σ ↔ x.Sat σ := by
  simp [Row.norm, Xark.R1cs.Row.Sat]

/-- Rows with the same normal forms have the same solutions. -/
theorem sat_of_norm {A B : List Row} (h : A.map Row.norm = B.map Row.norm) :
    Xark.R1cs.Sat A σ ↔ Xark.R1cs.Sat B σ := by
  have key : ∀ C : List Row, Xark.R1cs.Sat C σ ↔ ∀ x ∈ C.map Row.norm, x.Sat σ := by
    intro C; simp [Xark.R1cs.Sat, row_norm_sat]
  rw [key, key, h]

theorem sat_append (A B : List Row) :
    Xark.R1cs.Sat (A ++ B) σ ↔ Xark.R1cs.Sat A σ ∧ Xark.R1cs.Sat B σ := by
  simp [Xark.R1cs.Sat, or_imp, forall_and]

theorem sat_flatMap (l : List ℕ) (f : ℕ → List Row) :
    Xark.R1cs.Sat (l.flatMap f) σ ↔ ∀ j ∈ l, Xark.R1cs.Sat (f j) σ := by
  simp only [Xark.R1cs.Sat, List.mem_flatMap]
  constructor
  · intro h j hj x hx; exact h x ⟨j, hj, hx⟩
  · rintro h x ⟨j, hj, hx⟩; exact h j hj x hx

theorem sat_cons (x : Row) (A : List Row) :
    Xark.R1cs.Sat (x :: A) σ ↔ x.Sat σ ∧ Xark.R1cs.Sat A σ := by
  simp [Xark.R1cs.Sat]

theorem sat_nil : Xark.R1cs.Sat ([] : List Row) σ := by simp [Xark.R1cs.Sat]

end eval

/-! ### The generators: on the curve, of order `q`, with their tables -/

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Xark.Templates.Add32 (IsBit isBit_val isBit_of_mul_self word_lt word_testBit cast_sum
  nat_eq_of_cast sum_map_range)

def gen : ℕ → ℕ × ℕ
  | 0 => gen0
  | _ => gen1

def chain : ℕ → List Step
  | 0 => chain0
  | _ => chain1

def qIdx : ℕ → ℕ
  | 0 => qIdx0
  | _ => qIdx1

/-- `Σ_{w<43} 2·8^w`, the offsets the windows add. -/
def off : ℕ := ∑ j ∈ Finset.range 43, 2 * 8 ^ j

theorem off_eq : off = 194447066811964836264785489961010406546 := by
  simp [off, Finset.sum_range_succ]

/-- The facts about generator `s` the kernel checks, besides its chain: `Gₛ` is on the
curve with coordinates below `r`, and the chain's points list has the claimed length, index
`qIdx s` in range and `−Gₛ` there. -/
def genOk (s : ℕ) : Bool :=
  let Q := points [gen s] (chain s)
  decide ((gen s).1 < r) && decide ((gen s).2 < r) &&
    ((gen s).2 ^ 2 + 17) % r == (gen s).1 ^ 3 % r &&
    decide (Q.length = 749) && decide (offIdx s < 749) && decide (qIdx s < 749) &&
    Q.getD (qIdx s) (0, 0) == ((gen s).1, r - (gen s).2)

/-- The chain's multiples: the table entries are `(j + 2)·8ʷ`, `offIdx s` is `off` and
`qIdx s` is `q − 1`. -/
def coeffsOk (s : ℕ) : Bool :=
  let C := (coeffsRev [1] (chain s)).reverse
  decide (C.length = 749) &&
    (List.range 43).all (fun w => (List.range 8).all fun j =>
      C.getD (1 + 8 * w + j) 0 == (j + 2) * 8 ^ w) &&
    C.getD (offIdx s) 0 == 194447066811964836264785489961010406546 &&
    C.getD (qIdx s) 0 == q - 1

/-- The facts about generator `s`'s chain the kernel checks. -/
def chainFacts (s : ℕ) : Bool := genOk s && check [gen s] (chain s) && coeffsOk s

/-- Steps `50i .. 50i + 49` of generator `s`'s chain, checked against the points before
them (`check_of_chunks`). -/
def chunkOk (s i : ℕ) : Bool :=
  check (points [gen s] ((chain s).take (50 * i))) (((chain s).drop (50 * i)).take 50)

/-! Each kernel check below is its own declaration: one needs a few GB, the whole
`chainFacts` in one `decide +kernel` needed 22 GB. -/
section kernel
set_option maxRecDepth 100000

theorem genOk0 : genOk 0 = true := by decide +kernel
theorem genOk1 : genOk 1 = true := by decide +kernel
theorem coeffsOk0 : coeffsOk 0 = true := by decide +kernel
theorem coeffsOk1 : coeffsOk 1 = true := by decide +kernel
theorem chain_len (s : ℕ) (hs : s < 2) : (chain s).length ≤ 50 * 15 := by
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  all_goals decide +kernel
theorem chunkOk_0_0 : chunkOk 0 0 = true := by decide +kernel
theorem chunkOk_0_1 : chunkOk 0 1 = true := by decide +kernel
theorem chunkOk_0_2 : chunkOk 0 2 = true := by decide +kernel
theorem chunkOk_0_3 : chunkOk 0 3 = true := by decide +kernel
theorem chunkOk_0_4 : chunkOk 0 4 = true := by decide +kernel
theorem chunkOk_0_5 : chunkOk 0 5 = true := by decide +kernel
theorem chunkOk_0_6 : chunkOk 0 6 = true := by decide +kernel
theorem chunkOk_0_7 : chunkOk 0 7 = true := by decide +kernel
theorem chunkOk_0_8 : chunkOk 0 8 = true := by decide +kernel
theorem chunkOk_0_9 : chunkOk 0 9 = true := by decide +kernel
theorem chunkOk_0_10 : chunkOk 0 10 = true := by decide +kernel
theorem chunkOk_0_11 : chunkOk 0 11 = true := by decide +kernel
theorem chunkOk_0_12 : chunkOk 0 12 = true := by decide +kernel
theorem chunkOk_0_13 : chunkOk 0 13 = true := by decide +kernel
theorem chunkOk_0_14 : chunkOk 0 14 = true := by decide +kernel
theorem chunkOk_1_0 : chunkOk 1 0 = true := by decide +kernel
theorem chunkOk_1_1 : chunkOk 1 1 = true := by decide +kernel
theorem chunkOk_1_2 : chunkOk 1 2 = true := by decide +kernel
theorem chunkOk_1_3 : chunkOk 1 3 = true := by decide +kernel
theorem chunkOk_1_4 : chunkOk 1 4 = true := by decide +kernel
theorem chunkOk_1_5 : chunkOk 1 5 = true := by decide +kernel
theorem chunkOk_1_6 : chunkOk 1 6 = true := by decide +kernel
theorem chunkOk_1_7 : chunkOk 1 7 = true := by decide +kernel
theorem chunkOk_1_8 : chunkOk 1 8 = true := by decide +kernel
theorem chunkOk_1_9 : chunkOk 1 9 = true := by decide +kernel
theorem chunkOk_1_10 : chunkOk 1 10 = true := by decide +kernel
theorem chunkOk_1_11 : chunkOk 1 11 = true := by decide +kernel
theorem chunkOk_1_12 : chunkOk 1 12 = true := by decide +kernel
theorem chunkOk_1_13 : chunkOk 1 13 = true := by decide +kernel
theorem chunkOk_1_14 : chunkOk 1 14 = true := by decide +kernel

end kernel

theorem chainOk {s : ℕ} (hs : s < 2) : check [gen s] (chain s) = true := by
  refine check_of_chunks _ _ 50 15 (chain_len s hs) fun i hi => ?_
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · interval_cases i
    exacts [chunkOk_0_0, chunkOk_0_1, chunkOk_0_2, chunkOk_0_3, chunkOk_0_4, chunkOk_0_5,
      chunkOk_0_6, chunkOk_0_7, chunkOk_0_8, chunkOk_0_9, chunkOk_0_10, chunkOk_0_11, chunkOk_0_12,
      chunkOk_0_13, chunkOk_0_14]
  · interval_cases i
    exacts [chunkOk_1_0, chunkOk_1_1, chunkOk_1_2, chunkOk_1_3, chunkOk_1_4, chunkOk_1_5,
      chunkOk_1_6, chunkOk_1_7, chunkOk_1_8, chunkOk_1_9, chunkOk_1_10, chunkOk_1_11, chunkOk_1_12,
      chunkOk_1_13, chunkOk_1_14]

theorem chainFacts_of {s : ℕ} (hs : s < 2) : chainFacts s = true := by
  have hc := chainOk hs
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · rw [chainFacts, genOk0, coeffsOk0, hc]; rfl
  · rw [chainFacts, genOk1, coeffsOk1, hc]; rfl

theorem pts_eq (s : ℕ) : pts s = points [gen s] (chain s) := by
  rcases s with _ | s <;> rfl

theorem offIdx_eq (s : ℕ) : offIdx s = PedersenHash.offIdx s := rfl

section gens

variable {s : ℕ} (hs : s < 2)
include hs

theorem facts : (gen s).1 < r ∧ (gen s).2 < r ∧ ((gen s).2 ^ 2 + 17) % r = (gen s).1 ^ 3 % r ∧
    check [gen s] (chain s) = true ∧ (points [gen s] (chain s)).length = 749 ∧
    (coeffs [1] (chain s)).length = 749 ∧
    (∀ w < 43, ∀ j < 8, (coeffs [1] (chain s)).getD (1 + 8 * w + j) 0 = (j + 2) * 8 ^ w) ∧
    (coeffs [1] (chain s)).getD (offIdx s) 0 = off ∧ offIdx s < 749 ∧ qIdx s < 749 ∧
    (coeffs [1] (chain s)).getD (qIdx s) 0 = q - 1 ∧
    (points [gen s] (chain s)).getD (qIdx s) (0, 0) = ((gen s).1, r - (gen s).2) := by
  have h := chainFacts_of hs
  rw [coeffs_one]
  simp only [chainFacts, genOk, coeffsOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨hx, hy, he, hQ, hoi, hqi, hp, hc, hC, ht, ho, hq⟩ := h
  exact ⟨hx, hy, he, hc, hQ, hC, ht, off_eq ▸ ho, hoi, hqi, hq, hp⟩

end gens

theorem gen_nonsingular {s : ℕ} (hs : s < 2) :
    grumpkinCurve.Nonsingular ((gen s).1 : F) ((gen s).2 : F) := by
  obtain ⟨-, -, he, -⟩ := facts hs
  rw [nonsingular_iff]
  have := cast_eq_of_mod he
  push_cast at this
  linear_combination this

/-- Generator `Gₛ`. -/
def Gpt (s : ℕ) : GrumpkinPoint :=
  if hs : s < 2 then some _ _ (gen_nonsingular hs) else 0

theorem multiples {s : ℕ} (hs : s < 2) :
    Multiples (Gpt s) (pts s) (coeffs [1] (chain s)) := by
  obtain ⟨hx, hy, -, hc, -⟩ := facts hs
  rw [pts_eq, Gpt, dif_pos hs]
  exact check_sound _ (multiples_start hx hy _) hc

theorem tab_pt {s w j : ℕ} (hs : s < 2) (hw : w < 43) (hj : j < 8) :
    ∃ h, (some (tab s w j).1 (tab s w j).2 h : GrumpkinPoint) = ((j + 2) * 8 ^ w) • Gpt s := by
  obtain ⟨-, -, -, -, hQ, -, ht, -⟩ := facts hs
  obtain ⟨h, e⟩ := multiples_get (multiples hs) (i := 1 + 8 * w + j)
    (by rw [pts_eq, hQ]; omega)
  rw [ht w hw j hj] at e
  exact ⟨h, e⟩

theorem corr_pt {s : ℕ} (hs : s < 2) :
    ∃ h, (some (corr s).1 (corr s).2 h : GrumpkinPoint) = -(off • Gpt s) := by
  obtain ⟨-, -, -, -, hQ, -, -, ho, hoi, -⟩ := facts hs
  obtain ⟨h, e⟩ := multiples_get (multiples hs) (i := offIdx s) (by rw [pts_eq, hQ]; exact hoi)
  rw [ho] at e
  have h' : grumpkinCurve.Nonsingular (corr s).1 (corr s).2 := by
    rw [nonsingular_iff] at h ⊢; simp only [corr, neg_sq]; exact h
  exact ⟨h', by rw [← e]; exact some_neg rfl⟩

theorem Gpt_ne_zero {s : ℕ} (hs : s < 2) : Gpt s ≠ 0 := by
  rw [Gpt, dif_pos hs]; exact some_ne_zero _

/-- **Each generator has order `q`.** -/
theorem order {s : ℕ} (hs : s < 2) : addOrderOf (Gpt s) = q := by
  obtain ⟨-, hy, -, -, hQ, -, -, -, -, hqi, hq, hp⟩ := facts hs
  refine addOrderOf_eq_q (Gpt_ne_zero hs) ?_
  obtain ⟨h, e⟩ := multiples_get (multiples hs) (i := qIdx s) (by rw [pts_eq, hQ]; exact hqi)
  rw [hq] at e
  rw [← e]
  simp only [pts_eq, hp]
  conv_rhs => rw [Gpt, dif_pos hs]
  exact some_neg (by rw [Nat.cast_sub hy.le, ZMod.natCast_self, zero_sub])

/-! ### Digits and partial sums -/

/-- Bit `i` of scalar `s`'s decomposition, as a natural (`0` past bit 127). -/
def bitN (σ : TVar → F) (s i : ℕ) : ℕ := if i < 128 then (σ (.wit (base s + i))).val else 0

/-- Window `w`'s digit. -/
def digit (σ : TVar → F) (s w : ℕ) : ℕ :=
  bitN σ s (3 * w) + 2 * bitN σ s (3 * w + 1) + 4 * bitN σ s (3 * w + 2)

/-- The multiple of `Gₛ` after window `w`: `Σ_{j ≤ w} (digit_j + 2)·8^j`. -/
def S (σ : TVar → F) (s w : ℕ) : ℕ := ∑ j ∈ Finset.range (w + 1), (digit σ s j + 2) * 8 ^ j

/-- Scalar `s`'s bits are bits. -/
def Bits (σ : TVar → F) (s : ℕ) : Prop := ∀ i < 128, IsBit (σ (.wit (base s + i)))

section digits

variable {σ : TVar → F} {s : ℕ}

theorem bitN_le (hb : Bits σ s) (i : ℕ) : bitN σ s i ≤ 1 := by
  unfold bitN; split_ifs with h
  · exact isBit_val (hb i h)
  · omega

theorem digit_le (hb : Bits σ s) (w : ℕ) : digit σ s w ≤ 7 := by
  have := bitN_le hb (3 * w); have := bitN_le hb (3 * w + 1); have := bitN_le hb (3 * w + 2)
  unfold digit; omega

theorem S_succ (w : ℕ) : S σ s (w + 1) = S σ s w + (digit σ s (w + 1) + 2) * 8 ^ (w + 1) := by
  simp only [S]; rw [Finset.sum_range_succ]

theorem S_lt (hb : Bits σ s) (w : ℕ) : S σ s w < 2 * 8 ^ (w + 1) := by
  induction w with
  | zero => have := digit_le hb 0; simp only [S, zero_add, Finset.sum_range_one, pow_zero, mul_one]; omega
  | succ w ih =>
    rw [S_succ]; have := digit_le hb (w + 1)
    have h8 : 8 ^ (w + 1 + 1) = 8 * 8 ^ (w + 1) := by ring
    nlinarith

theorem two_le_S (w : ℕ) : 2 ≤ S σ s w := by
  have h := Finset.single_le_sum (f := fun j => (digit σ s j + 2) * 8 ^ j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos w) : 0 ∈ Finset.range (w + 1))
  simp only [pow_zero, mul_one] at h; unfold S; omega

theorem eleven_lt_q : 11 * 8 ^ 42 < q := by unfold q; norm_num

/-- `Σ_{j<n} 8^j·(f(3j) + 2f(3j+1) + 4f(3j+2)) = Σ_{i<3n} 2^i·f(i)`. -/
theorem regroup (f : ℕ → ℕ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (f (3 * j) + 2 * f (3 * j + 1) + 4 * f (3 * j + 2)) * 8 ^ j =
      ∑ i ∈ Finset.range (3 * n), f i * 2 ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      show (8 : ℕ) ^ n = 2 ^ (3 * n) by rw [pow_mul]; norm_num]
    ring

/-- The windows' digits make up the scalar. -/
theorem sum_digits :
    ∑ j ∈ Finset.range 43, digit σ s j * 8 ^ j =
      ∑ i ∈ Finset.range 128, (σ (.wit (base s + i))).val * 2 ^ i := by
  rw [show (∑ j ∈ Finset.range 43, digit σ s j * 8 ^ j) =
    ∑ j ∈ Finset.range 43, (bitN σ s (3 * j) + 2 * bitN σ s (3 * j + 1) +
      4 * bitN σ s (3 * j + 2)) * 8 ^ j from rfl, regroup, show 3 * 43 = 128 + 1 from rfl,
    Finset.sum_range_succ]
  simp only [bitN, lt_self_iff_false, if_false, zero_mul, add_zero]
  exact Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.mp hi)]

theorem S_42 : S σ s 42 = (∑ j ∈ Finset.range 43, digit σ s j * 8 ^ j) + off := by
  simp only [S, off, add_mul, Finset.sum_add_distrib]

end digits

/-! ### Window lookups -/

theorem lookup3_eq (t : ℕ → F) {b0 b1 b2 : F} (h0 : IsBit b0) (h1 : IsBit b1) (h2 : IsBit b2) :
    t 0 + (t 2 - t 0) * b1 + (t 4 - t 0) * b2 + (t 6 - t 4 - t 2 + t 0) * (b1 * b2) +
      b0 * ((t 1 - t 0) + (t 3 - t 2 - t 1 + t 0) * b1 + (t 5 - t 4 - t 1 + t 0) * b2 +
        (t 7 - t 6 - t 5 + t 4 - t 3 + t 2 + t 1 - t 0) * (b1 * b2)) =
    t (b0.val + 2 * b1.val + 4 * b2.val) := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    simp [ZMod.val_one] <;> ring

theorem lookup2_eq (t : ℕ → F) {b0 b1 : F} (h0 : IsBit b0) (h1 : IsBit b1) :
    t 0 + (t 1 - t 0) * b0 + (t 2 - t 0) * b1 + (t 3 - t 2 - t 1 + t 0) * (b0 * b1) =
    t (b0.val + 2 * b1.val) := by
  (rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> simp [ZMod.val_one]); ring

/-- A 3-bit window's rows select its table entry. -/
theorem look3_sound {s w b a : ℕ} {σ : TVar → F} (h0 : IsBit (σ (.wit b)))
    (h1 : IsBit (σ (.wit (b + 1)))) (h2 : IsBit (σ (.wit (b + 2))))
    (h : Xark.R1cs.Sat (look3Rows s w b a) σ) :
    (look3Out s w b a).1.eval σ =
        (tab s w ((σ (.wit b)).val + 2 * (σ (.wit (b + 1))).val + 4 * (σ (.wit (b + 2))).val)).1 ∧
      (look3Out s w b a).2.eval σ =
        (tab s w ((σ (.wit b)).val + 2 * (σ (.wit (b + 1))).val + 4 * (σ (.wit (b + 2))).val)).2 := by
  simp only [look3Rows, sat_cons, sat_nil, and_true, Xark.R1cs.Row.Sat, eval_v] at h
  obtain ⟨e12, ex, ey⟩ := h
  simp only [look3Out, high, low, eval_add, eval_smul, eval_k, eval_v] at ex ey ⊢
  rw [← ex, ← ey, ← e12]
  constructor
  · rw [← lookup3_eq (fun j => (tab s w j).1) h0 h1 h2]
  · rw [← lookup3_eq (fun j => (tab s w j).2) h0 h1 h2]

theorem look2_sound {s w b a : ℕ} {σ : TVar → F} (h0 : IsBit (σ (.wit b)))
    (h1 : IsBit (σ (.wit (b + 1)))) (h : Xark.R1cs.Sat (look2Rows b a) σ) :
    (look2Out s w b a).1.eval σ = (tab s w ((σ (.wit b)).val + 2 * (σ (.wit (b + 1))).val)).1 ∧
      (look2Out s w b a).2.eval σ = (tab s w ((σ (.wit b)).val + 2 * (σ (.wit (b + 1))).val)).2 := by
  simp only [look2Rows, sat_cons, sat_nil, and_true, Xark.R1cs.Row.Sat, eval_v] at h
  simp only [look2Out, look2, eval_add, eval_smul, eval_k, eval_v]
  rw [← h]
  exact ⟨lookup2_eq (fun j => (tab s w j).1) h0 h1, lookup2_eq (fun j => (tab s w j).2) h0 h1⟩

/-! ### The incomplete add -/

/-- The add's rows, at `x₁ ≠ x₂`, output the sum of two points. -/
theorem add_sound {p q : P} {a : ℕ} {σ : TVar → F} (h : Xark.R1cs.Sat (addRows p q a) σ)
    {h₁ : grumpkinCurve.Nonsingular (p.1.eval σ) (p.2.eval σ)}
    {h₂ : grumpkinCurve.Nonsingular (q.1.eval σ) (q.2.eval σ)} (hx : p.1.eval σ ≠ q.1.eval σ) :
    ∃ h₃, (some _ _ h₁ + some _ _ h₂ : GrumpkinPoint) =
      some ((addOut a).1.eval σ) ((addOut a).2.eval σ) h₃ := by
  simp only [addRows, sat_cons, sat_nil, and_true, Xark.R1cs.Row.Sat, eval_v, eval_sub,
    eval_add] at h
  obtain ⟨r1, r2, r3⟩ := h
  simp only [addOut, eval_v]
  exact add_some_eq hx r1 (by linear_combination -r2) (by linear_combination -r3)

/-! ### One scalar's multiplication, window by window -/

/-- The accumulator before window `w + 1` is the point `S_w · Gₛ`. -/
def AccPt (σ : TVar → F) (s w : ℕ) : Prop :=
  ∃ h, (some ((accBefore s w).1.eval σ) ((accBefore s w).2.eval σ) h : GrumpkinPoint) =
    S σ s w • Gpt s

theorem pt_congr {x y x' y' : F} (hx : x = x') (hy : y = y') {h' : grumpkinCurve.Nonsingular x' y'}
    {Q : GrumpkinPoint} (e : (some x' y' h' : GrumpkinPoint) = Q) :
    ∃ h, (some x y h : GrumpkinPoint) = Q := by
  subst hx; subst hy; exact ⟨h', e⟩

theorem bit_of {σ : TVar → F} {s : ℕ} (hb : Bits σ s) {i : ℕ} (hi : i < 128) {j : ℕ}
    (hj : j = base s + i) : IsBit (σ (.wit j)) := hj ▸ hb i hi

theorem digit_eq {σ : TVar → F} {s w : ℕ} (hw : w ≤ 41) :
    (σ (.wit (base s + 3 * w))).val + 2 * (σ (.wit (base s + 3 * w + 1))).val +
      4 * (σ (.wit (base s + 3 * w + 2))).val = digit σ s w := by
  simp only [digit, bitN, if_pos (show 3 * w < 128 by omega), if_pos (show 3 * w + 1 < 128 by omega),
    if_pos (show 3 * w + 2 < 128 by omega), add_assoc]

/-- Window 0's lookup is the first accumulator. -/
theorem acc_zero {σ : TVar → F} {s : ℕ} (hs : s < 2) (hb : Bits σ s)
    (h : Xark.R1cs.Sat (look3Rows s 0 (base s) (base s + 256)) σ) : AccPt σ s 0 := by
  obtain ⟨ex, ey⟩ := look3_sound (bit_of hb (i := 0) (by norm_num) rfl)
    (bit_of hb (i := 1) (by norm_num) rfl) (bit_of hb (i := 2) (by norm_num) rfl) h
  have hd := digit_eq (σ := σ) (s := s) (w := 0) (by norm_num)
  simp only [mul_zero, add_zero] at hd ex ey
  rw [hd] at ex ey
  obtain ⟨hq, eq⟩ := tab_pt hs (w := 0) (j := digit σ s 0) (by norm_num)
    (by have := digit_le hb 0; omega)
  have hS : S σ s 0 = (digit σ s 0 + 2) * 8 ^ 0 := by simp [S]
  simp only [AccPt, accBefore, hS]
  exact pt_congr ex ey eq

/-- At window `w`, the accumulator `S_{w−1}·G` and the entry `(d + 2)·8^w·G` have different
`x`: the offsets make every partial sum smaller than the next entry. -/
theorem window_xne {σ : TVar → F} {s w d : ℕ} (hs : s < 2) (hb : Bits σ s) (hw : 1 ≤ w)
    (hw' : w ≤ 42) (hd : d ≤ 7) {x₁ y₁ x₂ y₂ : F} {h₁ : grumpkinCurve.Nonsingular x₁ y₁}
    {h₂ : grumpkinCurve.Nonsingular x₂ y₂} (e₁ : some _ _ h₁ = S σ s (w - 1) • Gpt s)
    (e₂ : some _ _ h₂ = ((d + 2) * 8 ^ w) • Gpt s) : x₁ ≠ x₂ := by
  have hS := S_lt hb (w - 1)
  have hS2 := two_le_S (σ := σ) (s := s) (w - 1)
  rw [Nat.sub_add_cancel hw] at hS
  have h1 : 2 * 8 ^ w ≤ (d + 2) * 8 ^ w := Nat.mul_le_mul_right _ (by omega)
  have h2 : (d + 2) * 8 ^ w ≤ 9 * 8 ^ w := Nat.mul_le_mul_right _ (by omega)
  have h3 : 8 ^ w ≤ 8 ^ 42 := Nat.pow_le_pow_right (by norm_num) hw'
  have := eleven_lt_q
  exact x_ne_of_nsmul (order hs) (by omega) (by omega) (by omega) e₁ e₂

/-- The parts of window `w ≤ 41`: its lookup is the entry `(d + 2)·8^w·G` and differs in `x`
from the accumulator. -/
theorem window_parts {σ : TVar → F} {s w : ℕ} (hs : s < 2) (hb : Bits σ s) (hw : 1 ≤ w)
    (hw' : w ≤ 41) (hacc : AccPt σ s (w - 1))
    (hl : Xark.R1cs.Sat (look3Rows s w (base s + 3 * w) (win s w)) σ) :
    ∃ hp hq, (some ((accBefore s (w - 1)).1.eval σ) ((accBefore s (w - 1)).2.eval σ) hp :
        GrumpkinPoint) = S σ s (w - 1) • Gpt s ∧
      (some ((look3Out s w (base s + 3 * w) (win s w)).1.eval σ)
        ((look3Out s w (base s + 3 * w) (win s w)).2.eval σ) hq : GrumpkinPoint) =
        ((digit σ s w + 2) * 8 ^ w) • Gpt s ∧
      (accBefore s (w - 1)).1.eval σ ≠ (look3Out s w (base s + 3 * w) (win s w)).1.eval σ := by
  obtain ⟨ex, ey⟩ := look3_sound (bit_of hb (i := 3 * w) (by omega) rfl)
    (bit_of hb (i := 3 * w + 1) (by omega) (by ring)) (bit_of hb (i := 3 * w + 2) (by omega)
      (by ring)) hl
  rw [digit_eq hw'] at ex ey
  obtain ⟨hq, eq⟩ := tab_pt hs (w := w) (j := digit σ s w) (by omega)
    (by have := digit_le hb w; omega)
  obtain ⟨hq', eq'⟩ := pt_congr ex ey eq
  obtain ⟨hp, ep⟩ := hacc
  exact ⟨hp, hq', ep, eq', window_xne hs hb hw (by omega) (digit_le hb w) ep eq'⟩

theorem accBefore_pos {s w : ℕ} (hw : 1 ≤ w) : accBefore s w = addOut (win s w + 3) := by
  simp [accBefore, acc, show w ≠ 0 by omega]

/-- **Window step.** Window `w`'s rows take `S_{w−1}·G` to `S_w·G`. -/
theorem window_sound {σ : TVar → F} {s w : ℕ} (hs : s < 2) (hb : Bits σ s) (hw : 1 ≤ w)
    (hw' : w ≤ 41) (hacc : AccPt σ s (w - 1)) (h : Xark.R1cs.Sat (winRows s w) σ) :
    AccPt σ s w := by
  rw [winRows, sat_append] at h
  obtain ⟨hp, hq, ep, eq, hx⟩ := window_parts hs hb hw hw' hacc h.1
  obtain ⟨h₃, e₃⟩ := add_sound h.2 hx (h₁ := hp) (h₂ := hq)
  rw [ep, eq, ← add_nsmul] at e₃
  have hS : S σ s w = S σ s (w - 1) + (digit σ s w + 2) * 8 ^ w := by
    obtain ⟨u, rfl⟩ : ∃ u, w = u + 1 := ⟨w - 1, by omega⟩
    simp [S_succ]
  simp only [AccPt, accBefore_pos hw, hS]
  exact ⟨h₃, e₃.symm⟩

/-- Windows `1 … 41` from their rows. -/
theorem windows_sound {σ : TVar → F} {s : ℕ} (hs : s < 2) (hb : Bits σ s) (h0 : AccPt σ s 0)
    (h : ∀ w, 1 ≤ w → w ≤ 41 → Xark.R1cs.Sat (winRows s w) σ) : AccPt σ s 41 := by
  suffices ∀ n ≤ 41, AccPt σ s n from this 41 le_rfl
  intro n hn
  induction n with
  | zero => exact h0
  | succ n ih => exact window_sound hs hb (by omega) hn (by simpa using ih (by omega)) (h _ (by omega) hn)

/-- Window 42 (2 bits) and the correction. -/
theorem last_parts {σ : TVar → F} {s : ℕ} (hs : s < 2) (hb : Bits σ s) (hacc : AccPt σ s 41)
    (hl : Xark.R1cs.Sat (look2Rows (base s + 126) (win s 42)) σ) :
    ∃ hp hq, (some ((acc s 41).1.eval σ) ((acc s 41).2.eval σ) hp : GrumpkinPoint) =
        S σ s 41 • Gpt s ∧
      (some ((look2Out s 42 (base s + 126) (win s 42)).1.eval σ)
        ((look2Out s 42 (base s + 126) (win s 42)).2.eval σ) hq : GrumpkinPoint) =
        ((digit σ s 42 + 2) * 8 ^ 42) • Gpt s ∧
      (acc s 41).1.eval σ ≠ (look2Out s 42 (base s + 126) (win s 42)).1.eval σ := by
  obtain ⟨ex, ey⟩ := look2_sound (s := s) (w := 42) (bit_of hb (i := 126) (by norm_num) rfl)
    (bit_of hb (i := 127) (by norm_num) rfl) hl
  have hd : (σ (.wit (base s + 126))).val + 2 * (σ (.wit (base s + 126 + 1))).val = digit σ s 42 := by
    simp [digit, bitN]
  rw [hd] at ex ey
  obtain ⟨hq, eq⟩ := tab_pt hs (w := 42) (j := digit σ s 42) (by norm_num)
    (by have := digit_le hb 42; omega)
  obtain ⟨hq', eq'⟩ := pt_congr ex ey eq
  rw [AccPt, accBefore_pos (by norm_num)] at hacc
  obtain ⟨hp, ep⟩ := hacc
  exact ⟨hp, hq', ep, eq', window_xne hs hb (w := 42) (by norm_num) le_rfl (digit_le hb 42) ep eq'⟩

theorem acc42_sound {σ : TVar → F} {s : ℕ} (hs : s < 2) (hb : Bits σ s) (hacc : AccPt σ s 41)
    (hl : Xark.R1cs.Sat (look2Rows (base s + 126) (win s 42)) σ)
    (ha : Xark.R1cs.Sat (addRows (acc s 41) (look2Out s 42 (base s + 126) (win s 42))
      (win s 42 + 1)) σ) :
    ∃ h, (some ((addOut (win s 42 + 1)).1.eval σ) ((addOut (win s 42 + 1)).2.eval σ) h :
      GrumpkinPoint) = S σ s 42 • Gpt s := by
  obtain ⟨hp, hq, ep, eq, hx⟩ := last_parts hs hb hacc hl
  obtain ⟨h₃, e₃⟩ := add_sound ha hx (h₁ := hp) (h₂ := hq)
  rw [ep, eq, ← add_nsmul] at e₃
  have hS := S_succ (σ := σ) (s := s) 41
  simp only [Nat.reduceAdd] at hS
  exact ⟨h₃, by rw [← e₃, hS]⟩

theorem off_pos : 0 < off := by rw [off_eq]; norm_num

theorem off_bound {m : ℕ} (hm : m < 2 ^ 128) : m + off + off < q := by
  rw [off_eq]; unfold q; omega

/-- **Correction.** Adding `−off·G` to `(m + off)·G`: the rows force `m ≠ 0` and output
`m·G`. -/
theorem corr_sound {σ : TVar → F} {s a b : ℕ} (hs : s < 2) {m : ℕ} (hm : m < 2 ^ 128)
    {hp : grumpkinCurve.Nonsingular ((addOut a).1.eval σ) ((addOut a).2.eval σ)}
    (ep : (some _ _ hp : GrumpkinPoint) = (m + off) • Gpt s)
    (h : Xark.R1cs.Sat (addRows (addOut a) (k (corr s).1, k (corr s).2) b) σ) :
    0 < m ∧ ∃ h, (some ((addOut b).1.eval σ) ((addOut b).2.eval σ) h : GrumpkinPoint) =
      m • Gpt s := by
  obtain ⟨hq, eq⟩ := corr_pt hs
  have hord := order hs
  have hb := off_bound hm
  set c : P := (k (corr s).1, k (corr s).2) with hc
  have c1 : c.1.eval σ = (corr s).1 := by simp [hc]
  have c2 : c.2.eval σ = (corr s).2 := by simp [hc]
  obtain ⟨hq', eq'⟩ := pt_congr c1 c2 eq
  -- Equal `x` would make the points equal (then `q ∣ m + 2·off`) or opposite (then the
  -- slope row forces `y = 0`, and `q ∣ 2·off`).
  have hx : (addOut a).1.eval σ ≠ c.1.eval σ := by
    intro hx
    rcases (X_eq_iff (h₁ := hp) (h₂ := hq')).mp hx with e | e
    · rw [ep, eq', eq_neg_iff_add_eq_zero, ← add_nsmul] at e
      have := Nat.le_of_dvd (by have := off_pos; omega) (hord ▸ addOrderOf_dvd_of_nsmul_eq_zero e)
      omega
    · simp only [hc, addRows, sat_cons, sat_nil, and_true, Xark.R1cs.Row.Sat, eval_v, eval_sub,
        eval_add, eval_k] at h
      rw [c1] at hx
      have hy : (addOut a).2.eval σ = -(corr s).2 := by
        rw [neg_some] at e
        injection e with e1 e2
        simp only [negY, grumpkinCurve, c1, c2] at e2
        linear_combination e2
      have r1 := h.1
      rw [hx, sub_self, mul_zero, hy] at r1
      have hy0 : (corr s).2 = 0 := by
        have : (2 : F) * (corr s).2 = 0 := by linear_combination -r1
        exact (mul_eq_zero.mp this).resolve_left two_ne
      have e2 : (some _ _ hq : GrumpkinPoint) = -some _ _ hq := some_neg (by rw [hy0, _root_.neg_zero])
      rw [eq_neg_iff_add_eq_zero, eq, ← neg_add, neg_eq_zero, ← add_nsmul] at e2
      have := Nat.le_of_dvd (by have := off_pos; omega) (hord ▸ addOrderOf_dvd_of_nsmul_eq_zero e2)
      omega
  obtain ⟨h₃, e₃⟩ := add_sound h hx (h₁ := hp) (h₂ := hq')
  rw [ep, eq', add_nsmul, add_neg_cancel_right] at e₃
  refine ⟨Nat.pos_of_ne_zero fun hm0 => hx ?_, h₃, e₃.symm⟩
  subst hm0
  rw [X_eq_iff (h₁ := hp) (h₂ := hq')]; right; rw [ep, eq', neg_neg, zero_add]

/-! ### The scalar's bits -/

theorem eval_bitsLC (σ : TVar → F) (s : ℕ) :
    (bitsLC s).eval σ = ∑ i ∈ Finset.range 128, ((2 ^ i : ℕ) : F) * σ (.wit (base s + i)) := by
  simp [bitsLC, LC.eval, List.map_map, Function.comp_def, sum_map_range]

theorem two_pow_128_lt_r : 2 ^ 128 < r := by unfold r; norm_num

theorem decomp_sound {σ : TVar → F} {s : ℕ} (h : Xark.R1cs.Sat (decompRows s) σ) :
    Bits σ s ∧ (σ (.plug s)).val = ∑ i ∈ Finset.range 128, 2 ^ i * (σ (.wit (base s + i))).val ∧
      (σ (.plug s)).val < 2 ^ 128 := by
  rw [decompRows, sat_append, sat_cons] at h
  obtain ⟨hb, hr, -⟩ := h
  have hbits : Bits σ s := fun i hi => isBit_of_mul_self (by
    simpa [Xark.R1cs.Row.Sat] using hb _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  simp only [Xark.R1cs.Row.Sat, eval_sub, eval_k, eval_plug, mul_one, eval_bitsLC] at hr
  have hlt := word_lt (fun i => (σ (.wit (base s + i))).val) 128 fun i hi => isBit_val (hbits i hi)
  have e : σ (.plug s) = ((∑ i ∈ Finset.range 128, 2 ^ i * (σ (.wit (base s + i))).val : ℕ) : F) := by
    rw [← cast_sum]; linear_combination -hr
  have hv : (σ (.plug s)).val = ∑ i ∈ Finset.range 128, 2 ^ i * (σ (.wit (base s + i))).val := by
    rw [e, ZMod.val_natCast_of_lt (lt_trans hlt two_pow_128_lt_r)]
  exact ⟨hbits, hv, hv ▸ hlt⟩

/-- **One term.** A scalar's rows force `0 < m < 2^128` and output `m·Gₛ`. -/
theorem term_sound {σ : TVar → F} {s : ℕ} (hs : s < 2) (h : Xark.R1cs.Sat (mulRows s) σ) :
    0 < (σ (.plug s)).val ∧ (σ (.plug s)).val < 2 ^ 128 ∧
      ∃ h, (some ((term s).1.eval σ) ((term s).2.eval σ) h : GrumpkinPoint) =
        (σ (.plug s)).val • Gpt s := by
  simp only [mulRows, lastRows, sat_append, sat_flatMap, List.mem_range] at h
  obtain ⟨⟨⟨hd, h0⟩, hw⟩, ⟨hl2, ha42⟩, hc⟩ := h
  obtain ⟨hb, hv, hlt⟩ := decomp_sound hd
  have h41 := windows_sound hs hb (acc_zero hs hb h0) fun w hw1 hw2 => by
    simpa [Nat.sub_add_cancel hw1] using hw (w - 1) (by omega)
  obtain ⟨hp, ep⟩ := acc42_sound hs hb h41 hl2 ha42
  have hm : ∑ j ∈ Finset.range 43, digit σ s j * 8 ^ j = (σ (.plug s)).val := by
    rw [sum_digits, hv]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [S_42, hm] at ep
  obtain ⟨hpos, h₃, e₃⟩ := corr_sound hs hlt ep hc
  exact ⟨hpos, hlt, h₃, e₃⟩

/-! ### The exported template, read structurally -/

theorem inputs_eq : template.inputs = [⟨0, [(1, .plug 0)]⟩, ⟨0, [(1, .plug 1)]⟩] := by
  decide +kernel

theorem outputs_eq : template.outputs = [v 1894, v 1895] := by decide +kernel

theorem ins_eq (σ : TVar → F) : template.ins σ = [σ (.plug 0), σ (.plug 1)] := by
  simp [Template.ins, inputs_eq, LC.eval]

theorem outs_eq (σ : TVar → F) : template.outs σ = [σ (.wit 1894), σ (.wit 1895)] := by
  simp [Template.outs, outputs_eq]

theorem sat_iff (σ : TVar → F) : template.Sat σ ↔ Xark.R1cs.Sat modelRows σ :=
  sat_of_norm σ rows_eq

/-! ### Soundness -/

/-- The spec: the inputs are scalars `m₀, m₁ ∈ [1, 2^128)` and the outputs are the affine
coordinates of the Grumpkin point `m₀·G₀ + m₁·G₁` (a point, so not `0`). -/
def Spec (ins outs : List F) : Prop :=
  ∃ m₀ m₁ : ℕ, ins = [(m₀ : F), (m₁ : F)] ∧ 0 < m₀ ∧ m₀ < 2 ^ 128 ∧ 0 < m₁ ∧ m₁ < 2 ^ 128 ∧
    ∃ x y h, outs = [x, y] ∧ (some x y h : GrumpkinPoint) = m₀ • Gpt 0 + m₁ • Gpt 1

/-- **Soundness.** Every assignment satisfying the exported rows has inputs in
`[1, 2^128)` and outputs the coordinates of `m₀·G₀ + m₁·G₁`. No input assumption: the
rows enforce the range themselves. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  rw [sat_iff, modelRows, sat_append, sat_append, sat_append, sat_cons] at h
  obtain ⟨⟨⟨h0, h1⟩, hg, -⟩, ha⟩ := h
  obtain ⟨p0, l0, hp0, e0⟩ := term_sound (by norm_num) h0
  obtain ⟨p1, l1, hp1, e1⟩ := term_sound (by norm_num) h1
  have hx : (term 0).1.eval σ ≠ (term 1).1.eval σ := by
    intro hx
    simp only [Xark.R1cs.Row.Sat, eval_sub, eval_v, eval_k, hx, sub_self, zero_mul] at hg
    exact zero_ne_one hg
  obtain ⟨h₃, e₃⟩ := add_sound ha hx (h₁ := hp0) (h₂ := hp1)
  rw [e0, e1] at e₃
  refine ⟨_, _, by rw [ins_eq]; simp, p0, l0, p1, l1, _, _, h₃, by rw [outs_eq]; simp [addOut], e₃.symm⟩

end Xark.Templates.PedersenHash
