/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.GrumpkinGroup

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Grumpkin's group order, and points as certified multiples

What a fixed-base multiplication on Grumpkin needs about the curve, proven without
axioms (clean-orchard's Pallas proofs assume the group order, `pallas_natCard`):

* `q_prime`: `q`, BN254's base field modulus, is prime (Pratt certificate).
* `add_some_eq`, `dbl_some_eq`: affine points whose coordinates satisfy the chord
  (or tangent) equations are the group sum.
* `check_sound`: an addition chain from a point `G`, each step checked in the kernel
  by modular arithmetic on naturals, lists multiples of `G` with their coordinates.
* `addOrderOf_eq_q`: a nonzero point `G` with a chain to `(q − 1)·G = −G` has order `q`.
* `x_ne_of_nsmul`: multiples `s·G ≠ ±t·G` of such a point have different `x` when
  `0 < s ≠ t` and `s + t < q`: the fact that makes the incomplete adds of a
  fixed-base multiplication with distinct offsets exact.

Grumpkin's order is `q`; this file never needs that, only `q·G = 0` for the points
it is applied to, which a chain proves.
-/

namespace Pratt

set_option maxRecDepth 100000 in
theorem prime_11465965001 : Nat.Prime 11465965001 :=
  prime_of_certificate 11465965001 3
    [(2, 3), (5, 4), (7, 1), (327599, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_173171039 : Nat.Prime 173171039 :=
  prime_of_certificate 173171039 13
    [(2, 1), (73, 1), (89, 1), (13327, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_1263766531 : Nat.Prime 1263766531 :=
  prime_of_certificate 1263766531 10
    [(2, 1), (3, 1), (5, 1), (13, 1), (911, 1), (3557, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_35385462869 : Nat.Prime 35385462869 :=
  prime_of_certificate 35385462869 2
    [(2, 2), (7, 1), (1263766531, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, prime_1263766531⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_2480874801745591 : Nat.Prime 2480874801745591 :=
  prime_of_certificate 2480874801745591 6
    [(2, 1), (3, 2), (5, 1), (19, 1), (41, 1), (35385462869, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_35385462869⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_13427688667394608761327070753331941386769 : Nat.Prime 13427688667394608761327070753331941386769 :=
  prime_of_certificate 13427688667394608761327070753331941386769 17
    [(2, 4), (3, 1), (7, 1), (11, 1), (1853641, 1), (4562087, 1), (173171039, 1), (2480874801745591, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_173171039, prime_2480874801745591⟩
    (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem prime_21888242871839275222246405745257275088696311157297823662689037894645226208583 : Nat.Prime 21888242871839275222246405745257275088696311157297823662689037894645226208583 :=
  prime_of_certificate 21888242871839275222246405745257275088696311157297823662689037894645226208583 3
    [(2, 1), (3, 2), (13, 1), (29, 1), (67, 1), (229, 1), (311, 1), (983, 1), (11003, 1), (405928799, 1), (11465965001, 1), (13427688667394608761327070753331941386769, 1)]
    (by norm_num) (by decide) (by decide)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_405928799, prime_11465965001, prime_13427688667394608761327070753331941386769⟩
    (by decide) (by decide)

end Pratt

namespace Xark.Grumpkin

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

/-- BN254's base field modulus: Grumpkin's group order. -/
def q : ℕ := 21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- **`q` is prime**, by the Pratt certificate above. -/
theorem q_prime : Nat.Prime q :=
  Pratt.prime_21888242871839275222246405745257275088696311157297823662689037894645226208583

instance : Fact (Nat.Prime q) := ⟨q_prime⟩

/-! ## Points of `y² = x³ − 17` -/

theorem Δ_ne_zero : grumpkinCurve.Δ ≠ 0 := by
  have : grumpkinCurve.Δ = ((124848 : ℕ) : ZMod r) * (-1) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, grumpkinCurve]
    push_cast; ring
  rw [this, mul_neg_one, neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd (by norm_num) h) (by unfold r; norm_num)

/-- A point of Grumpkin is a solution of `y² = x³ − 17`. -/
theorem nonsingular_iff {x y : ZMod r} : grumpkinCurve.Nonsingular x y ↔ y ^ 2 = x ^ 3 - 17 := by
  rw [← equation_iff_nonsingular_of_Δ_ne_zero Δ_ne_zero, equation_iff]
  simp only [grumpkinCurve]
  constructor <;> intro h <;> linear_combination h

theorem two_ne : (2 : ZMod r) ≠ 0 := by
  rw [show (2 : ZMod r) = ((2 : ℕ) : ZMod r) by norm_cast, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd (by norm_num) h) (by unfold r; norm_num)

variable {x₁ y₁ x₂ y₂ x₃ y₃ l : ZMod r}

/-- **Chord.** Points `(x₁, y₁) ≠ ±(x₂, y₂)`, a slope `l` of the line through them,
and `(x₃, y₃)` the third intersection reflected: `(x₃, y₃)` is their sum. -/
theorem add_some_eq {h₁ : grumpkinCurve.Nonsingular x₁ y₁} {h₂ : grumpkinCurve.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) (hl : l * (x₂ - x₁) = y₂ - y₁) (hx₃ : x₃ = l ^ 2 - x₁ - x₂)
    (hy₃ : y₃ = l * (x₁ - x₃) - y₁) :
    ∃ h₃, (some _ _ h₁ + some _ _ h₂ : GrumpkinPoint) = some x₃ y₃ h₃ := by
  have hs : grumpkinCurve.slope x₁ x₂ y₁ y₂ = l := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
    linear_combination hl
  have hX : grumpkinCurve.addX x₁ x₂ (grumpkinCurve.slope x₁ x₂ y₁ y₂) = x₃ := by
    rw [hs, hx₃]; simp [addX, grumpkinCurve]
  have hY : grumpkinCurve.addY x₁ x₂ y₁ (grumpkinCurve.slope x₁ x₂ y₁ y₂) = y₃ := by
    rw [addY, negAddY, hX, hs, hy₃]; simp [negY, grumpkinCurve]; ring
  have h₃ := nonsingular_add h₁ h₂ fun h => hx h.1
  rw [hX, hY] at h₃
  exact ⟨h₃, by rw [add_of_X_ne hx]; simp only [some.injEq]; exact ⟨hX, hY⟩⟩

/-- **Tangent.** A point with `y₁ ≠ 0`, the tangent's slope `l` and `(x₃, y₃)` its
other intersection reflected: `(x₃, y₃)` is the point doubled. -/
theorem dbl_some_eq {h₁ : grumpkinCurve.Nonsingular x₁ y₁} (hy : y₁ ≠ 0)
    (hl : l * (2 * y₁) = 3 * x₁ ^ 2) (hx₃ : x₃ = l ^ 2 - 2 * x₁)
    (hy₃ : y₃ = l * (x₁ - x₃) - y₁) :
    ∃ h₃, (some _ _ h₁ + some _ _ h₁ : GrumpkinPoint) = some x₃ y₃ h₃ := by
  have h2y : 2 * y₁ ≠ 0 := mul_ne_zero two_ne hy
  have hne : y₁ ≠ grumpkinCurve.negY x₁ y₁ := by
    simp only [negY, grumpkinCurve]; intro h; exact h2y (by linear_combination h)
  have hden : y₁ - grumpkinCurve.negY x₁ y₁ = 2 * y₁ := by
    simp only [negY, grumpkinCurve]; ring
  have hs : grumpkinCurve.slope x₁ x₁ y₁ y₁ = l := by
    rw [slope_of_Y_ne rfl hne, hden, div_eq_iff h2y]
    simp only [grumpkinCurve]
    linear_combination -hl
  have hX : grumpkinCurve.addX x₁ x₁ (grumpkinCurve.slope x₁ x₁ y₁ y₁) = x₃ := by
    rw [hs, hx₃]; simp [addX, grumpkinCurve]; ring
  have hY : grumpkinCurve.addY x₁ x₁ y₁ (grumpkinCurve.slope x₁ x₁ y₁ y₁) = y₃ := by
    rw [addY, negAddY, hX, hs, hy₃]; simp [negY, grumpkinCurve]; ring
  have h₃ := nonsingular_add h₁ h₁ fun h => hne h.2
  rw [hX, hY] at h₃
  exact ⟨h₃, by rw [add_self_of_Y_ne hne]; simp only [some.injEq]; exact ⟨hX, hY⟩⟩

/-- Negation flips `y`. -/
theorem some_neg {x y y' : ZMod r} {h : grumpkinCurve.Nonsingular x y}
    {h' : grumpkinCurve.Nonsingular x y'} (hy : y' = -y) :
    (some x y' h' : GrumpkinPoint) = -some x y h := by
  rw [neg_some]; simp [negY, grumpkinCurve, hy]

/-! ## Certified addition chains -/

/-- A chain step `(a, b, x, y)`: the next point is `(x, y) = P_a + P_b`. -/
abbrev Step := ℕ × ℕ × ℕ × ℕ

/-- `a − b` modulo `r`, as a natural, for `b < r`. -/
def sub (a b : ℕ) : ℕ := a + r - b

/-- One step checked against the points `P` so far, by arithmetic modulo `r`: the
chord through `P_a ≠ P_b`, or the tangent at `P_a = P_b`, meets the curve again at
`(x, −y)`. -/
def stepOk (P : List (ℕ × ℕ)) : Step → Bool
  | (a, b, x, y) =>
    let (x₁, y₁) := P.getD a (0, 0)
    let (x₂, y₂) := P.getD b (0, 0)
    a < P.length && b < P.length && x < r && y < r &&
    if a = b then
      y₁ != 0 && (x + 2 * x₁) * (4 * y₁ * y₁) % r == 9 * x₁ ^ 4 % r &&
        (y + y₁) * (2 * y₁) % r == 3 * x₁ ^ 2 * sub x₁ x % r
    else
      x₁ != x₂ && (x + x₁ + x₂) * sub x₂ x₁ ^ 2 % r == sub y₂ y₁ ^ 2 % r &&
        (y + y₁) * sub x₂ x₁ % r == sub y₂ y₁ * sub x₁ x % r

/-- Every step of a chain checks, each against the points before it. -/
def check : List (ℕ × ℕ) → List Step → Bool
  | _, [] => true
  | P, s :: c => stepOk P s && check (P ++ [(s.2.2.1, s.2.2.2)]) c

/-- The points after a chain. -/
def points (P : List (ℕ × ℕ)) (c : List Step) : List (ℕ × ℕ) :=
  P ++ c.map fun s => (s.2.2.1, s.2.2.2)

/-- The multiples of `G` the chain's points are: `c_a + c_b` for a step `(a, b, …)`. -/
def coeffs : List ℕ → List Step → List ℕ
  | C, [] => C
  | C, s :: c => coeffs (C ++ [C.getD s.1 0 + C.getD s.2.1 0]) c

/-- Entry `i` of a list kept newest-first, `0` past its end. -/
def atR (R : List ℕ) (i : ℕ) : ℕ := if i < R.length then R.getD (R.length - 1 - i) 0 else 0

/-- `coeffs` with its list newest-first: `getD` walks a constructor list instead of
normalizing an append chain, which is what lets `decide +kernel` evaluate a 749-step chain
in a few GB instead of 13. -/
def coeffsRev : List ℕ → List Step → List ℕ
  | R, [] => R
  | R, s :: c => coeffsRev ((atR R s.1 + atR R s.2.1) :: R) c

theorem atR_reverse (C : List ℕ) (i : ℕ) : atR C.reverse i = C.getD i 0 := by
  unfold atR
  rw [List.length_reverse]
  split_ifs with hi
  · have h1 : C.length - 1 - i < C.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse h1,
      show C.length - 1 - (C.length - 1 - i) = i by omega]
  · rw [List.getD_eq_default _ _ (by omega)]

theorem coeffs_eq_rev (C : List ℕ) (c : List Step) :
    coeffs C c = (coeffsRev C.reverse c).reverse := by
  induction c generalizing C with
  | nil => simp [coeffs, coeffsRev]
  | cons s c ih =>
    rw [coeffs, coeffsRev, ih, List.reverse_append, List.reverse_singleton,
      List.singleton_append, atR_reverse, atR_reverse]

theorem coeffs_one (c : List Step) : coeffs [1] c = (coeffsRev [1] c).reverse := by
  simpa using coeffs_eq_rev [1] c

theorem check_append (P : List (ℕ × ℕ)) (c₁ c₂ : List Step) :
    check P (c₁ ++ c₂) = (check P c₁ && check (points P c₁) c₂) := by
  induction c₁ generalizing P with
  | nil => simp [check, points]
  | cons s c ih => simp [check, points, ih, Bool.and_assoc]

theorem points_take_add (P : List (ℕ × ℕ)) (c : List Step) (a k : ℕ) :
    points (points P (c.take a)) ((c.drop a).take k) = points P (c.take (a + k)) := by
  simp [points, List.take_add, List.map_append, List.append_assoc]

/-- A chain checks when each chunk of `k` steps checks against the points of the steps
before it. Each chunk is its own `decide +kernel`, so the kernel's working set is one
chunk's, not the chain's. -/
theorem check_of_chunks (P : List (ℕ × ℕ)) (c : List Step) (k n : ℕ) (hlen : c.length ≤ k * n)
    (h : ∀ i < n, check (points P (c.take (k * i))) ((c.drop (k * i)).take k) = true) :
    check P c = true := by
  suffices ∀ d m, m + d = n → check (points P (c.take (k * m))) (c.drop (k * m)) = true by
    simpa [points] using this n 0 (by omega)
  intro d
  induction d with
  | zero =>
    intro m hm
    subst hm
    rw [List.drop_eq_nil_of_le (by simpa using hlen)]
    rfl
  | succ d ih =>
    intro m hm
    have hsplit : c.drop (k * m) = (c.drop (k * m)).take k ++ c.drop (k * (m + 1)) := by
      rw [Nat.mul_succ, ← List.drop_drop, List.take_append_drop]
    rw [hsplit, check_append, h m (by omega), points_take_add, ← Nat.mul_succ, ih (m + 1) (by omega)]
    rfl

/-- Point `i` of `P` is the point `C_i • G`, with coordinates below `r`. -/
def Multiples (G : GrumpkinPoint) (P : List (ℕ × ℕ)) (C : List ℕ) : Prop :=
  P.length = C.length ∧ ∀ i < P.length, (P.getD i (0, 0)).1 < r ∧ (P.getD i (0, 0)).2 < r ∧
    ∃ h, (some ((P.getD i (0, 0)).1 : ZMod r) (P.getD i (0, 0)).2 h : GrumpkinPoint) =
      C.getD i 0 • G

theorem cast_sub {a b : ℕ} (hb : b < r) : ((sub a b : ℕ) : ZMod r) = a - b := by
  rw [sub, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

theorem cast_eq_of_mod {a b : ℕ} (h : a % r = b % r) : (a : ZMod r) = b :=
  (ZMod.natCast_eq_natCast_iff' a b r).mpr h

theorem getD_append_lt {α : Type*} (l : List α) (x d : α) {i : ℕ} (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_eq {α : Type*} (l : List α) (x d : α) : (l ++ [x]).getD l.length d = x := by
  simp [List.getD_eq_getElem?_getD]

/-- A checked step adds the multiple `C_a + C_b` to the list. -/
theorem stepOk_sound {G : GrumpkinPoint} {P : List (ℕ × ℕ)} {C : List ℕ} (hm : Multiples G P C)
    {s : Step} (hs : stepOk P s = true) :
    Multiples G (P ++ [(s.2.2.1, s.2.2.2)]) (C ++ [C.getD s.1 0 + C.getD s.2.1 0]) := by
  obtain ⟨a, b, x, y⟩ := s
  obtain ⟨hlen, hP⟩ := hm
  simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨ha, hb⟩, hx⟩, hy⟩, hs⟩ := hs
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [getD_append_lt _ _ _ hi, getD_append_lt _ _ _ (hlen ▸ hi)]
    exact hP i hi
  rw [getD_append_eq, hlen, getD_append_eq]
  refine ⟨hx, hy, ?_⟩
  obtain ⟨hxa, hya, ha', hPa⟩ := hP a ha
  obtain ⟨hxb, hyb, hb', hPb⟩ := hP b hb
  generalize P.getD a (0, 0) = pa at *
  generalize P.getD b (0, 0) = pb at *
  obtain ⟨x₁, y₁⟩ := pa
  obtain ⟨x₂, y₂⟩ := pb
  dsimp only at *
  rw [add_nsmul, ← hPa, ← hPb]
  split_ifs at hs with hab
  · subst hab
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hs
    obtain ⟨⟨hy0, h1⟩, h2⟩ := hs
    have hy0' : (y₁ : ZMod r) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; exact hy0 (Nat.eq_zero_of_dvd_of_lt h hya)
    have e1 := cast_eq_of_mod h1
    have e2 := cast_eq_of_mod h2
    push_cast [cast_sub hx] at e1 e2
    set l := 3 * (x₁ : ZMod r) ^ 2 / (2 * y₁)
    have h2y : 2 * (y₁ : ZMod r) ≠ 0 := mul_ne_zero two_ne hy0'
    have hl : l * (2 * y₁) = 3 * (x₁ : ZMod r) ^ 2 := div_mul_cancel₀ _ h2y
    have e : (some (x₂ : ZMod r) y₂ hb' : GrumpkinPoint) = some _ _ ha' := by rw [hPa, hPb]
    rw [e]
    have hx₃ : (x : ZMod r) = l ^ 2 - 2 * x₁ := by
      have : ((x : ZMod r) + 2 * x₁) * (2 * y₁) ^ 2 = (l ^ 2 - 2 * x₁ + 2 * x₁) * (2 * y₁) ^ 2 := by
        rw [sub_add_cancel, ← mul_pow, hl]; linear_combination e1
      have := mul_right_cancel₀ (pow_ne_zero 2 h2y) this
      linear_combination this
    have hy₃ : (y : ZMod r) = l * (x₁ - x) - y₁ := by
      have : ((y : ZMod r) + y₁) * (2 * y₁) = (l * (x₁ - x)) * (2 * y₁) := by
        rw [mul_comm l, mul_assoc, hl]; linear_combination e2
      have := mul_right_cancel₀ h2y this
      linear_combination this
    obtain ⟨h₃, e₃⟩ := dbl_some_eq (h₁ := ha') hy0' hl hx₃ hy₃
    exact ⟨h₃, e₃.symm⟩
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hs
    obtain ⟨⟨hxne, h1⟩, h2⟩ := hs
    have hx' : (x₁ : ZMod r) ≠ x₂ := by
      intro h; exact hxne (by
        have := congrArg ZMod.val h
        rwa [ZMod.val_natCast_of_lt hxa, ZMod.val_natCast_of_lt hxb] at this)
    have e1 := cast_eq_of_mod h1
    have e2 := cast_eq_of_mod h2
    push_cast [cast_sub hxa, cast_sub hya, cast_sub hx] at e1 e2
    have hd : (x₂ : ZMod r) - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx')
    set l := ((y₂ : ZMod r) - y₁) / (x₂ - x₁)
    have hl : l * (x₂ - x₁) = (y₂ : ZMod r) - y₁ := div_mul_cancel₀ _ hd
    have hx₃ : (x : ZMod r) = l ^ 2 - x₁ - x₂ := by
      have : ((x : ZMod r) + x₁ + x₂) * (x₂ - x₁) ^ 2 =
          (l ^ 2 - x₁ - x₂ + x₁ + x₂) * (x₂ - x₁) ^ 2 := by
        rw [show l ^ 2 - x₁ - x₂ + x₁ + x₂ = l ^ 2 by ring, ← mul_pow, hl]; exact e1
      have := mul_right_cancel₀ (pow_ne_zero 2 hd) this
      linear_combination this
    have hy₃ : (y : ZMod r) = l * (x₁ - x) - y₁ := by
      have : ((y : ZMod r) + y₁) * (x₂ - x₁) = (l * (x₁ - x)) * (x₂ - x₁) := by
        rw [mul_comm l, mul_assoc, hl]; linear_combination e2
      have := mul_right_cancel₀ hd this
      linear_combination this
    obtain ⟨h₃, e₃⟩ := add_some_eq (h₁ := ha') (h₂ := hb') hx' hl hx₃ hy₃
    exact ⟨h₃, e₃.symm⟩

/-- **Chain soundness.** If every step of `c` checks, the points after it are the
multiples of `G` that `coeffs` computes. -/
theorem check_sound {G : GrumpkinPoint} :
    ∀ (c : List Step) {P : List (ℕ × ℕ)} {C : List ℕ}, Multiples G P C → check P c = true →
      Multiples G (points P c) (coeffs C c)
  | [], P, C, hm, _ => by simpa [points, coeffs] using hm
  | s :: c, P, C, hm, h => by
    simp only [check, Bool.and_eq_true] at h
    have := check_sound c (stepOk_sound hm h.1) h.2
    simpa [points, coeffs, List.append_assoc] using this

/-- The chain's start: a point `G = (x, y)` with `x, y < r` is `1 • G`. -/
theorem multiples_start {x y : ℕ} (hx : x < r) (hy : y < r)
    (h : grumpkinCurve.Nonsingular (x : ZMod r) y) :
    Multiples (some _ _ h) [(x, y)] [1] :=
  ⟨rfl, fun i hi => by
    obtain rfl : i = 0 := by simpa using hi
    exact ⟨hx, hy, h, by simp⟩⟩

/-- Point `i` of a chain's points, as a group element. -/
theorem multiples_get {G : GrumpkinPoint} {P : List (ℕ × ℕ)} {C : List ℕ} (hm : Multiples G P C)
    {i : ℕ} (hi : i < P.length) :
    ∃ h, (some ((P.getD i (0, 0)).1 : ZMod r) (P.getD i (0, 0)).2 h : GrumpkinPoint) =
      C.getD i 0 • G :=
  (hm.2 i hi).2.2

/-! ## Order -/

/-- **Order `q`.** A nonzero point with `(q − 1)·G = −G` has order `q`. -/
theorem addOrderOf_eq_q {G : GrumpkinPoint} (hG : G ≠ 0) (h : (q - 1) • G = -G) :
    addOrderOf G = q := by
  refine addOrderOf_eq_prime ?_ hG
  have : q = (q - 1) + 1 := by unfold q; norm_num
  rw [this, succ_nsmul, h, neg_add_cancel]

/-- **Distinct multiples, distinct `x`.** For `G` of order `q`, `0 < s ≠ t` and
`s + t < q`: `s·G` and `t·G` are neither equal nor opposite, so their `x` differ. -/
theorem x_ne_of_nsmul {G : GrumpkinPoint} (hG : addOrderOf G = q) {s t : ℕ} (hs : 0 < s)
    (hst : s ≠ t) (hq : s + t < q) {h₁ : grumpkinCurve.Nonsingular x₁ y₁}
    {h₂ : grumpkinCurve.Nonsingular x₂ y₂} (e₁ : some _ _ h₁ = s • G) (e₂ : some _ _ h₂ = t • G) :
    x₁ ≠ x₂ := by
  intro hx
  rcases X_eq_iff.mp hx with h | h
  · rw [e₁, e₂] at h
    exact hst (nsmul_injOn_Iio_addOrderOf (by rw [Set.mem_Iio, hG]; omega)
      (by rw [Set.mem_Iio, hG]; omega) h)
  · rw [e₁, e₂, eq_neg_iff_add_eq_zero, ← add_nsmul] at h
    have := Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero h)
    omega

end Xark.Grumpkin
