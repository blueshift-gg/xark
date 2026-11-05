/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Templates.MultiScalarMul
import Formal.SignedMul

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `xark_grumpkin::multi_scalar_mul`: soundness

The exported template (`Formal/Templates/MultiScalarMul.lean`) reads two scalars
`s₀ = plug 0`, `s₁ = plug 1` and two points `P = (plug 2, plug 3)`, `Q = (plug 4, plug 5)`.
Its rows (`rows_eq`, checked by the kernel) are, in order:

* the on-curve rows of `P` and `Q`;
* `decompose`'s 128 bits of `s₀` (`w6…w133`) and of `s₁` (`w262…w389`);
* the shared table: `x_P ≠ x_Q`, `U = P + Q = (w523, w525 − y_P)`,
  `V = P − Q = (w527 − x_P − x_Q, w528 − y_P)`;
* the fused step `(O + U) + O`, then for bit pairs `127, …, 1` the fused step
  `(A + T) + A` with `T = ±U` (bits equal) or `±V` (bits differ), the sign the bit of `s₀`;
* `q`, the 4-way choice of `corr`, `corr − P`, `corr − Q`, `corr − U` on the two low bits,
  and the output `acc + q`.

`soundness`: with no assumption, the rows force `s₀, s₁ < 2¹²⁸`, `P` and `Q` onto
Grumpkin, and the output to the affine point `s₀·P + s₁·Q`. Every input condition is this
template's own rows (the bits by `decompose`, the points by the on-curve rows,
`x_P ≠ x_Q` by the table's guard, so `P = ±Q` is rejected).
-/

namespace Xark.Templates.MultiScalarMul

open Xark.Template Xark.R1cs Xark.GrumpkinMul Xark.SignedMul Xark.DoubleAdd
  WeierstrassCurve.Affine

/-! ### The rows -/

def ocRows (x y : TVar) (k : ℕ) : List Row :=
  [⟨v1 y, v1 y, ⟨-17, [(1, .wit (k + 1))]⟩⟩, ⟨v1 x, v1 x, v1 (.wit k)⟩,
    ⟨v1 (.wit k), v1 x, v1 (.wit (k + 1))⟩]

def boolRow (k : ℕ) : Row := ⟨v1 (.wit k), v1 (.wit k), v1 (.wit k)⟩

/-- `Σᵢ 2ⁱ·w(k + i) = plug p`. -/
def recompLC (p k : ℕ) : LC :=
  ⟨0, (-1, .plug p) :: (List.range 128).map fun i => (((2 ^ i : ℕ) : F), .wit (k + i))⟩

/-- `decompose`: 128 bits `w(k + i)` of `plug p`. -/
def limbRows (p k : ℕ) : List Row :=
  (List.range 128).map (fun i => boolRow (k + i)) ++ [⟨recompLC p k, ⟨1, []⟩, ⟨0, []⟩⟩]

/-- `x_P ≠ x_Q`, `U = P + Q`, `V = P − Q`. -/
def tableRows : List Row :=
  [⟨⟨0, [(-1, .plug 2), (1, .plug 4)]⟩, v1 (.wit 518), ⟨1, []⟩⟩,
    ⟨⟨0, [(-1, .plug 3), (1, .plug 5)]⟩, v1 (.wit 518), v1 (.wit 520)⟩,
    ⟨v1 (.wit 520), v1 (.wit 520), ⟨0, [(1, .plug 2), (1, .plug 4), (1, .wit 523)]⟩⟩,
    ⟨v1 (.wit 520), ⟨0, [(1, .plug 2), (-1, .wit 523)]⟩, v1 (.wit 525)⟩,
    ⟨⟨0, [(-1, .plug 3), (-1, .plug 5)]⟩, v1 (.wit 518), v1 (.wit 526)⟩,
    ⟨v1 (.wit 526), v1 (.wit 526), v1 (.wit 527)⟩,
    ⟨v1 (.wit 526), ⟨0, [(2, .plug 2), (1, .plug 4), (-1, .wit 527)]⟩, v1 (.wit 528)⟩]

def l2First : LC := ⟨0, [(-1, .wit 531), (2 * oY, .wit 533)]⟩

/-- Step `0`: `(O + U) + O`. -/
def firstRows : List Row :=
  [⟨⟨5, [(-1, .wit 523)]⟩, v1 (.wit 529), ⟨1, []⟩⟩,
    ⟨⟨oY, [(1, .plug 3), (-1, .wit 525)]⟩, v1 (.wit 529), v1 (.wit 531)⟩,
    ⟨v1 (.wit 531), v1 (.wit 531), v1 (.wit 532)⟩,
    ⟨⟨0, [(2 * oY, .wit 533)]⟩, ⟨10, [(1, .wit 523), (-1, .wit 532)]⟩, ⟨2 * oY, []⟩⟩,
    ⟨l2First, l2First, v1 (.wit 535)⟩,
    ⟨l2First, ⟨5, [(-1, .wit 523), (1, .wit 532), (-1, .wit 535)]⟩, ⟨oY, [(1, .wit 538)]⟩⟩]

/-- Step `k`'s addend `x`, and the accumulator after it (`x = s2v − s1v + txv`,
`y = yvv`). Step `j + 1` owns `w(540 + 19j) … w(540 + 19j + 17)`. -/
def txv : ℕ → ℕ
  | 0 => 523
  | j + 1 => 540 + 19 * j + 3
def s1v : ℕ → ℕ
  | 0 => 532
  | j + 1 => 540 + 19 * j + 10
def s2v : ℕ → ℕ
  | 0 => 535
  | j + 1 => 540 + 19 * j + 14
def yvv : ℕ → ℕ
  | 0 => 538
  | j + 1 => 540 + 19 * j + 17

theorem txv_succ (j : ℕ) : txv (j + 1) = 540 + 19 * j + 3 := rfl
theorem s1v_succ (j : ℕ) : s1v (j + 1) = 540 + 19 * j + 10 := rfl
theorem s2v_succ (j : ℕ) : s2v (j + 1) = 540 + 19 * j + 14 := rfl
theorem yvv_succ (j : ℕ) : yvv (j + 1) = 540 + 19 * j + 17 := rfl

/-- `[k₀ = k₁]`, `k₀, k₁` the bits `127 − j` of `s₀`, `s₁`. -/
def sel (j : ℕ) : LC := ⟨1, [(-1, .wit (133 - j)), (-1, .wit (389 - j)), (2, .wit (540 + 19 * j))]⟩

def l2Step (j : ℕ) : LC := ⟨0, [(-1, .wit (540 + 19 * j + 9)), (1, .wit (540 + 19 * j + 12))]⟩

/-- Step `j + 1`: the addend `T = ±U` or `±V`, then `(A + T) + A`. -/
def stepRows (j : ℕ) : List Row :=
  let b := 540 + 19 * j
  let k0 : TVar := .wit (133 - j)
  let k1 : TVar := .wit (389 - j)
  let px : TVar := .wit (txv j)
  let p1 : TVar := .wit (s1v j)
  let p2 : TVar := .wit (s2v j)
  let py : TVar := .wit (yvv j)
  [⟨v1 k0, v1 k1, v1 (.wit b)⟩,
    ⟨sel j, ⟨0, [(1, .plug 2), (1, .plug 4), (1, .wit 523), (-1, .wit 527)]⟩,
      ⟨0, [(1, .plug 2), (1, .plug 4), (-1, .wit 527), (1, .wit (b + 3))]⟩⟩,
    ⟨sel j, ⟨0, [(1, .wit 525), (-1, .wit 528)]⟩, v1 (.wit (b + 5))⟩,
    ⟨⟨-1, [(2, k0)]⟩, ⟨0, [(-1, .plug 3), (1, .wit 528), (1, .wit (b + 5))]⟩, v1 (.wit (b + 6))⟩,
    ⟨⟨0, [(1, px), (-1, p1), (1, p2), (-1, .wit (b + 3))]⟩, v1 (.wit (b + 7)), ⟨1, []⟩⟩,
    ⟨⟨0, [(1, py), (-1, .wit (b + 6))]⟩, v1 (.wit (b + 7)), v1 (.wit (b + 9))⟩,
    ⟨v1 (.wit (b + 9)), v1 (.wit (b + 9)), v1 (.wit (b + 10))⟩,
    ⟨v1 (.wit (b + 12)), ⟨0, [(2, px), (-2, p1), (2, p2), (1, .wit (b + 3)), (-1, .wit (b + 10))]⟩,
      ⟨0, [(2, py)]⟩⟩,
    ⟨l2Step j, l2Step j, v1 (.wit (b + 14))⟩,
    ⟨l2Step j, ⟨0, [(1, px), (-1, p1), (1, p2), (-1, .wit (b + 3)), (1, .wit (b + 10)),
      (-1, .wit (b + 14))]⟩, ⟨0, [(1, py), (1, .wit (b + 17))]⟩⟩]

/-- `q`: `corr − P`, `corr − Q`, `corr − U`, and the choice on the low bits `w6`, `w262`. -/
def qRows : List Row :=
  [⟨⟨-corrX, [(1, .plug 2)]⟩, v1 (.wit 2953), ⟨1, []⟩⟩,
    ⟨⟨-corrY, [(-1, .plug 3)]⟩, v1 (.wit 2953), v1 (.wit 2955)⟩,
    ⟨v1 (.wit 2955), v1 (.wit 2955), v1 (.wit 2956)⟩,
    ⟨v1 (.wit 2955), ⟨2 * corrX, [(1, .plug 2), (-1, .wit 2956)]⟩, v1 (.wit 2957)⟩,
    ⟨v1 (.wit 6), ⟨2 * corrX, [(1, .plug 2), (-1, .wit 2956)]⟩, v1 (.wit 2958)⟩,
    ⟨v1 (.wit 6), ⟨2 * corrY, [(-1, .wit 2957)]⟩, v1 (.wit 2959)⟩,
    ⟨⟨-corrX, [(1, .plug 4)]⟩, v1 (.wit 2960), ⟨1, []⟩⟩,
    ⟨⟨-corrY, [(-1, .plug 5)]⟩, v1 (.wit 2960), v1 (.wit 2962)⟩,
    ⟨v1 (.wit 2962), v1 (.wit 2962), v1 (.wit 2963)⟩,
    ⟨v1 (.wit 2962), ⟨2 * corrX, [(1, .plug 4), (-1, .wit 2963)]⟩, v1 (.wit 2964)⟩,
    ⟨⟨-corrX, [(1, .wit 523)]⟩, v1 (.wit 2965), ⟨1, []⟩⟩,
    ⟨⟨-corrY, [(1, .plug 3), (-1, .wit 525)]⟩, v1 (.wit 2965), v1 (.wit 2967)⟩,
    ⟨v1 (.wit 2967), v1 (.wit 2967), v1 (.wit 2968)⟩,
    ⟨v1 (.wit 2967), ⟨2 * corrX, [(1, .wit 523), (-1, .wit 2968)]⟩, v1 (.wit 2969)⟩,
    ⟨v1 (.wit 6), ⟨0, [(-1, .plug 4), (1, .wit 523), (1, .wit 2963), (-1, .wit 2968)]⟩,
      v1 (.wit 2970)⟩,
    ⟨v1 (.wit 6), ⟨0, [(1, .wit 2964), (-1, .wit 2969)]⟩, v1 (.wit 2971)⟩,
    ⟨v1 (.wit 262), ⟨0, [(-1, .plug 2), (1, .wit 523), (1, .wit 2956), (1, .wit 2958),
      (-1, .wit 2968), (-1, .wit 2970)]⟩, v1 (.wit 2972)⟩,
    ⟨v1 (.wit 262), ⟨0, [(1, .wit 2957), (1, .wit 2959), (-1, .wit 2969), (-1, .wit 2971)]⟩,
      v1 (.wit 2973)⟩]

def outXLC : LC := ⟨-corrX, [(-1, .wit 523), (-1, .wit 2937), (1, .wit 2944), (-1, .wit 2948),
  (1, .wit 2968), (1, .wit 2970), (1, .wit 2972)]⟩
def outLam : LC := ⟨-corrY, [(-1, .wit 2951), (1, .wit 2969), (1, .wit 2971), (1, .wit 2973)]⟩
def outYLC : LC := ⟨-corrX, [(-1, .wit 523), (2, .wit 2937), (-2, .wit 2944), (2, .wit 2948),
  (1, .wit 2968), (1, .wit 2970), (1, .wit 2972), (-1, .wit 2977)]⟩

/-- `acc + q`. -/
def outRows : List Row :=
  [⟨outXLC, v1 (.wit 2974), ⟨1, []⟩⟩, ⟨outLam, v1 (.wit 2974), v1 (.wit 2976)⟩,
    ⟨v1 (.wit 2976), v1 (.wit 2976), v1 (.wit 2977)⟩, ⟨v1 (.wit 2976), outYLC, v1 (.wit 2978)⟩]

def steps : List Row := (List.range 127).flatMap stepRows

theorem rows_eq : template.rows = ocRows (.plug 2) (.plug 3) 1 ++ (ocRows (.plug 4) (.plug 5) 4 ++
    (limbRows 0 6 ++ (limbRows 1 262 ++ (tableRows ++ (firstRows ++ (steps ++
      (qRows ++ outRows))))))) := by
  decide +kernel
theorem inputs_eq : template.inputs = (List.range 6).map fun i => v1 (.plug i) := by
  decide +kernel
theorem outputs_eq : template.outputs =
    [⟨corrX, [(1, .wit 523), (-1, .wit 2937), (1, .wit 2944), (-1, .wit 2948), (-1, .wit 2968),
      (-1, .wit 2970), (-1, .wit 2972), (1, .wit 2977)]⟩, ⟨0, [(-1, .wit 2951), (1, .wit 2978)]⟩] := by
  decide +kernel

/-! ### Spec -/

def Spec (ins outs : List F) : Prop :=
  (ins.getD 0 0).val < 2 ^ 128 ∧ (ins.getD 1 0).val < 2 ^ 128 ∧ ins.getD 2 0 ≠ ins.getD 4 0 ∧
    ∃ (hP : grumpkinCurve.Nonsingular (ins.getD 2 0) (ins.getD 3 0))
      (hQ : grumpkinCurve.Nonsingular (ins.getD 4 0) (ins.getD 5 0))
      (hR : grumpkinCurve.Nonsingular (outs.getD 0 0) (outs.getD 1 0)),
      (Point.some _ _ hR : GrumpkinPoint) =
        (ins.getD 0 0).val • Point.some _ _ hP + (ins.getD 1 0).val • Point.some _ _ hQ

theorem ins_getD (σ : TVar → F) {i : ℕ} (hi : i < 6) :
    (template.ins σ).getD i 0 = σ (.plug i) := by
  simp [Template.ins, inputs_eq, List.getD_eq_getElem?_getD, hi, v1, LC.eval]

/-- The output's coordinates. -/
def outX (σ : TVar → F) : F :=
  corrX + σ (.wit 523) - σ (.wit 2937) + σ (.wit 2944) - σ (.wit 2948) - σ (.wit 2968) -
    σ (.wit 2970) - σ (.wit 2972) + σ (.wit 2977)
def outY (σ : TVar → F) : F := -σ (.wit 2951) + σ (.wit 2978)

theorem outs_eq (σ : TVar → F) : template.outs σ = [outX σ, outY σ] := by
  simp only [Template.outs, outputs_eq, outX, outY, List.map_cons, List.map_nil, LC.eval,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  constructor <;> ring

theorem sat_iff (σ : TVar → F) : template.Sat σ ↔
    (∀ r ∈ ocRows (.plug 2) (.plug 3) 1, r.Sat σ) ∧ (∀ r ∈ ocRows (.plug 4) (.plug 5) 4, r.Sat σ) ∧
      (∀ r ∈ limbRows 0 6, r.Sat σ) ∧ (∀ r ∈ limbRows 1 262, r.Sat σ) ∧
      (∀ r ∈ tableRows, r.Sat σ) ∧ (∀ r ∈ firstRows, r.Sat σ) ∧
      (∀ j < 127, ∀ r ∈ stepRows j, r.Sat σ) ∧ (∀ r ∈ qRows, r.Sat σ) ∧
      ∀ r ∈ outRows, r.Sat σ := by
  rw [Template.Sat, rows_eq]
  simp only [Xark.R1cs.Sat, List.forall_mem_append, steps, List.mem_flatMap, List.mem_range,
    forall_exists_index, and_imp]
  exact ⟨fun ⟨a, b, c, d, e, f, g, i, k⟩ => ⟨a, b, c, d, e, f, fun j hj r hr => g r j hj hr, i, k⟩,
    fun ⟨a, b, c, d, e, f, g, i, k⟩ => ⟨a, b, c, d, e, f, fun r j hj hr => g j hj r hr, i, k⟩⟩

/-! ### Group facts -/

theorem accum_add {G : Type*} [AddCommGroup G] (O : G) (S S' : ℕ → G) (j : ℕ) :
    accum O (fun k => S k + S' k) j + (2 ^ j) • O = accum O S j + accum O S' j := by
  induction j with
  | zero => simp [accum]
  | succ j ih =>
    have e : accum O (fun k => S k + S' k) j = accum O S j + accum O S' j - (2 ^ j) • O :=
      eq_sub_of_add_eq ih
    simp only [accum]
    rw [e, pow_succ]
    module

/-- The last add: `acc₁₂₈ + q = s₀·P + s₁·Q`. -/
theorem final_eq2 {G : Type*} [AddCommGroup G] (O P Q C : G) (n s t : ℕ)
    (hC : C = -((2 ^ n) • O)) :
    (2 ^ n) • O + (2 * (s / 2) + 1) • P + (2 * (t / 2) + 1) • Q +
      (if t % 2 = 1 then (if s % 2 = 1 then C else C + -P)
        else if s % 2 = 1 then C + -Q else C + -(P + Q)) = s • P + t • Q := by
  have hs := Nat.div_add_mod s 2
  have ht := Nat.div_add_mod t 2
  generalize s / 2 = q at hs ⊢
  generalize t / 2 = q' at ht ⊢
  have h2 := Nat.mod_lt s (show 2 > 0 by omega)
  have h2' := Nat.mod_lt t (show 2 > 0 by omega)
  generalize s % 2 = m at hs h2 ⊢
  generalize t % 2 = m' at ht h2' ⊢
  subst hs ht hC
  interval_cases m <;> interval_cases m' <;> simp only [if_true, if_false, zero_ne_one] <;> module

/-! ### Points from rows -/

open Grumpkin in
theorem oc_sound {σ : TVar → F} {x y : TVar} {k : ℕ} (h : ∀ r ∈ ocRows x y k, r.Sat σ) :
    grumpkinCurve.Nonsingular (σ x) (σ y) := by
  have row := fun i (hi : i < (ocRows x y k).length) => h _ (List.getElem_mem hi)
  have r0 := row 0 (by simp [ocRows])
  have r1 := row 1 (by simp [ocRows])
  have r2 := row 2 (by simp [ocRows])
  simp only [ocRows, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.getElem_cons_zero, List.getElem_cons_succ] at r0 r1 r2
  exact nonsingular_iff.mpr (by linear_combination r0 - r2 - σ x * r1)

theorem eval_recomp (p k : ℕ) (σ : TVar → F) : (recompLC p k).eval σ =
    -σ (.plug p) + ∑ i ∈ Finset.range 128, ((2 ^ i : ℕ) : F) * σ (.wit (k + i)) := by
  simp [recompLC, LC.eval, List.map_map, Function.comp_def, Xark.Templates.Add32.sum_map_range]

/-- `decompose`'s rows: 128 bits whose word is the scalar, below `2¹²⁸`. -/
theorem limb_sound {σ : TVar → F} {p k : ℕ} (h : ∀ r ∈ limbRows p k, r.Sat σ) :
    (∀ i < 128, IsBit (σ (.wit (k + i)))) ∧
      (σ (.plug p)).val = ∑ i ∈ Finset.range 128, 2 ^ i * (σ (.wit (k + i))).val := by
  have hbit : ∀ i < 128, IsBit (σ (.wit (k + i))) := fun i hi => by
    have := h _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simp only [boolRow, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, zero_add, add_zero, one_mul] at this
    exact Xark.Templates.Add32.isBit_of_mul_self this
  refine ⟨hbit, ?_⟩
  have hrow := h _ (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [Row.Sat] at hrow
  rw [eval_recomp] at hrow
  simp only [LC.eval, List.map_nil, List.sum_nil, add_zero, mul_one] at hrow
  have hc := Xark.Templates.Add32.cast_sum (fun i => 2 ^ i) (fun i => σ (.wit (k + i)))
    (Finset.range 128)
  rw [hc] at hrow
  have hw := Xark.Templates.Add32.word_lt (fun i => (σ (.wit (k + i))).val) 128
    fun i hi => Xark.Templates.Add32.isBit_val (hbit i hi)
  have hlt : ∑ i ∈ Finset.range 128, 2 ^ i * (σ (.wit (k + i))).val < r :=
    lt_trans hw (by unfold r; norm_num)
  rw [show σ (.plug p) = ((∑ i ∈ Finset.range 128, 2 ^ i * (σ (.wit (k + i))).val : ℕ) : F) by
    linear_combination -hrow, ZMod.val_natCast_of_lt hlt]

/-- `U = P + Q` at `(w523, w525 − y_P)`. -/
def NsU (σ : TVar → F) : Prop := grumpkinCurve.Nonsingular (σ (.wit 523)) (σ (.wit 525) - σ (.plug 3))
/-- `V = P − Q` at `(w527 − x_P − x_Q, w528 − y_P)`. -/
def NsV (σ : TVar → F) : Prop :=
  grumpkinCurve.Nonsingular (σ (.wit 527) - σ (.plug 2) - σ (.plug 4)) (σ (.wit 528) - σ (.plug 3))

theorem table_sound {σ : TVar → F} (hP : grumpkinCurve.Nonsingular (σ (.plug 2)) (σ (.plug 3)))
    (hQ : grumpkinCurve.Nonsingular (σ (.plug 4)) (σ (.plug 5))) (h : ∀ r ∈ tableRows, r.Sat σ) :
    σ (.plug 2) ≠ σ (.plug 4) ∧
      (∃ hU : NsU σ, (Point.some _ _ hU : GrumpkinPoint) = Point.some _ _ hP + Point.some _ _ hQ) ∧
      ∃ hV : NsV σ, (Point.some _ _ hV : GrumpkinPoint) = Point.some _ _ hP + -Point.some _ _ hQ := by
  have row := fun i (hi : i < tableRows.length) => h _ (List.getElem_mem hi)
  have t0 := row 0 (by simp [tableRows])
  have t1 := row 1 (by simp [tableRows])
  have t2 := row 2 (by simp [tableRows])
  have t3 := row 3 (by simp [tableRows])
  have t4 := row 4 (by simp [tableRows])
  have t5 := row 5 (by simp [tableRows])
  have t6 := row 6 (by simp [tableRows])
  simp only [tableRows, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getElem_cons_zero, List.getElem_cons_succ] at t0 t1 t2 t3 t4 t5 t6
  have hx : σ (.plug 2) ≠ σ (.plug 4) := fun e => by
    rw [e] at t0; exact zero_ne_one (by linear_combination t0)
  refine ⟨hx, ?_, ?_⟩
  · obtain ⟨hU, eU⟩ := add_of_slope (x₃ := σ (.wit 523)) (y₃ := σ (.wit 525) - σ (.plug 3))
      (l := σ (.wit 520)) short hP hQ hx
      (by linear_combination -(σ (.plug 2) - σ (.plug 4)) * t1 -
        (σ (.plug 5) - σ (.plug 3)) * t0)
      (by linear_combination -t2) (by linear_combination -t3)
    exact ⟨hU, eU.symm⟩
  · rw [neg_some hQ (neg_ns hQ)]
    obtain ⟨hV, eV⟩ := add_of_slope (x₃ := σ (.wit 527) - σ (.plug 2) - σ (.plug 4))
      (y₃ := σ (.wit 528) - σ (.plug 3)) (l := σ (.wit 526)) short hP (neg_ns hQ) hx
      (by linear_combination -(σ (.plug 2) - σ (.plug 4)) * t4 -
        (-σ (.plug 3) - σ (.plug 5)) * t0)
      (by linear_combination -t5) (by linear_combination -t6)
    exact ⟨hV, eV.symm⟩

/-- `C − P` from one incomplete add's rows. -/
theorem sub_point {cx cy x y w l s t : F} (hC : grumpkinCurve.Nonsingular cx cy)
    (hP : grumpkinCurve.Nonsingular x y) (g : (-cx + x) * w = 1) (hl : (-cy - y) * w = l)
    (hs : l * l = s) (ht : l * (2 * cx + x - s) = t) :
    ∃ h : grumpkinCurve.Nonsingular (s - cx - x) (t - cy),
      (Point.some _ _ h : GrumpkinPoint) = Point.some _ _ hC + -Point.some _ _ hP := by
  have hx : cx ≠ x := fun e => by
    rw [e] at g; exact zero_ne_one (by linear_combination g)
  obtain ⟨h3, e3⟩ := add_of_slope (x₃ := s - cx - x) (y₃ := t - cy) (l := l) short hC (neg_ns hP)
    hx (by linear_combination (-(cx - x)) * hl + (cy + y) * g)
    (by linear_combination -hs) (by linear_combination -ht)
  exact ⟨h3, by rw [neg_some hP (neg_ns hP), e3]⟩

/-- `a ? A : B` for a bit `a`, as `B + a·(A − B)` coordinatewise. -/
theorem mux_point {a xa ya xb yb x y : F} (ha : IsBit a) (hA : grumpkinCurve.Nonsingular xa ya)
    (hB : grumpkinCurve.Nonsingular xb yb) (hx : x = xb + a * (xa - xb))
    (hy : y = yb + a * (ya - yb)) :
    ∃ h : grumpkinCurve.Nonsingular x y, (Point.some _ _ h : GrumpkinPoint) =
      if a.val = 1 then Point.some _ _ hA else Point.some _ _ hB := by
  rcases ha with rfl | rfl
  · rw [if_neg (by simp)]
    exact exists_some hB (by rw [hx]; ring) (by rw [hy]; ring)
  · rw [if_pos (by simp [ZMod.val_one])]
    exact exists_some hA (by rw [hx]; ring) (by rw [hy]; ring)

def qX (σ : TVar → F) : F := σ (.wit 2968) - corrX - σ (.wit 523) + σ (.wit 2970) + σ (.wit 2972)
def qY (σ : TVar → F) : F := σ (.wit 2969) - corrY + σ (.wit 2971) + σ (.wit 2973)

/-- The point `q` the low bits `a = w6`, `b = w262` choose. -/
noncomputable def qPt (a b : ℕ) (C P Q : GrumpkinPoint) : GrumpkinPoint :=
  if b = 1 then (if a = 1 then C else C + -P) else if a = 1 then C + -Q else C + -(P + Q)

theorem q_sound {σ : TVar → F} (hP : grumpkinCurve.Nonsingular (σ (.plug 2)) (σ (.plug 3)))
    (hQ : grumpkinCurve.Nonsingular (σ (.plug 4)) (σ (.plug 5))) (hU : NsU σ)
    (hUeq : (Point.some _ _ hU : GrumpkinPoint) = Point.some _ _ hP + Point.some _ _ hQ)
    (ha : IsBit (σ (.wit 6))) (hb : IsBit (σ (.wit 262))) (h : ∀ r ∈ qRows, r.Sat σ) :
    ∃ hq : grumpkinCurve.Nonsingular (qX σ) (qY σ), (Point.some _ _ hq : GrumpkinPoint) =
      qPt (σ (.wit 6)).val (σ (.wit 262)).val (Point.some _ _ corrNs) (Point.some _ _ hP)
        (Point.some _ _ hQ) := by
  have row := fun i (hi : i < qRows.length) => h _ (List.getElem_mem hi)
  have f0 := row 0 (by simp [qRows])
  have f1 := row 1 (by simp [qRows])
  have f2 := row 2 (by simp [qRows])
  have f3 := row 3 (by simp [qRows])
  have f4 := row 4 (by simp [qRows])
  have f5 := row 5 (by simp [qRows])
  have f6 := row 6 (by simp [qRows])
  have f7 := row 7 (by simp [qRows])
  have f8 := row 8 (by simp [qRows])
  have f9 := row 9 (by simp [qRows])
  have f10 := row 10 (by simp [qRows])
  have f11 := row 11 (by simp [qRows])
  have f12 := row 12 (by simp [qRows])
  have f13 := row 13 (by simp [qRows])
  have f14 := row 14 (by simp [qRows])
  have f15 := row 15 (by simp [qRows])
  have f16 := row 16 (by simp [qRows])
  have f17 := row 17 (by simp [qRows])
  simp only [qRows, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getElem_cons_zero, List.getElem_cons_succ] at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
  obtain ⟨hCP, eCP⟩ := sub_point corrNs hP (w := σ (.wit 2953)) (l := σ (.wit 2955))
    (s := σ (.wit 2956)) (t := σ (.wit 2957)) (by linear_combination f0) (by linear_combination f1)
    (by linear_combination f2) (by linear_combination f3)
  obtain ⟨hCQ, eCQ⟩ := sub_point corrNs hQ (w := σ (.wit 2960)) (l := σ (.wit 2962))
    (s := σ (.wit 2963)) (t := σ (.wit 2964)) (by linear_combination f6) (by linear_combination f7)
    (by linear_combination f8) (by linear_combination f9)
  obtain ⟨hCU, eCU⟩ := sub_point corrNs hU (w := σ (.wit 2965)) (l := σ (.wit 2967))
    (s := σ (.wit 2968)) (t := σ (.wit 2969)) (by linear_combination f10) (by linear_combination f11)
    (by linear_combination f12) (by linear_combination f13)
  obtain ⟨h1, e1⟩ := mux_point ha corrNs hCP (x := σ (.wit 2956) - corrX - σ (.plug 2) + σ (.wit 2958))
    (y := σ (.wit 2957) - corrY + σ (.wit 2959)) (by linear_combination -f4) (by linear_combination -f5)
  obtain ⟨h2, e2⟩ := mux_point ha hCQ hCU (x := σ (.wit 2968) - corrX - σ (.wit 523) + σ (.wit 2970))
    (y := σ (.wit 2969) - corrY + σ (.wit 2971)) (by linear_combination -f14)
    (by linear_combination -f15)
  obtain ⟨hq, eq⟩ := mux_point hb h1 h2 (x := qX σ) (y := qY σ)
    (by rw [qX]; linear_combination -f16) (by rw [qY]; linear_combination -f17)
  refine ⟨hq, ?_⟩
  rw [eq, e1, e2, eCP, eCQ, eCU, hUeq, qPt]

/-- The accumulator after 128 steps, plus `q`. -/
theorem out_sound {σ : TVar → F}
    (hA : grumpkinCurve.Nonsingular (σ (.wit 2948) - σ (.wit 2944) + σ (.wit 2937)) (σ (.wit 2951)))
    (hq : grumpkinCurve.Nonsingular (qX σ) (qY σ)) (h : ∀ r ∈ outRows, r.Sat σ) :
    ∃ hR : grumpkinCurve.Nonsingular (outX σ) (outY σ),
      (Point.some _ _ hR : GrumpkinPoint) = Point.some _ _ hA + Point.some _ _ hq := by
  have row := fun i (hi : i < outRows.length) => h _ (List.getElem_mem hi)
  have o0 := row 0 (by simp [outRows])
  have o1 := row 1 (by simp [outRows])
  have o2 := row 2 (by simp [outRows])
  have o3 := row 3 (by simp [outRows])
  simp only [outRows, outXLC, outLam, outYLC, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.getElem_cons_zero, List.getElem_cons_succ] at o0 o1 o2 o3
  have g : (qX σ - (σ (.wit 2948) - σ (.wit 2944) + σ (.wit 2937))) * σ (.wit 2974) = 1 := by
    rw [qX]; linear_combination o0
  have hx : σ (.wit 2948) - σ (.wit 2944) + σ (.wit 2937) ≠ qX σ := fun e => by
    rw [e, sub_self, zero_mul] at g; exact zero_ne_one g
  obtain ⟨hR, eR⟩ := add_of_slope (x₃ := outX σ) (y₃ := outY σ) (l := σ (.wit 2976)) short hA hq hx
    (by
      linear_combination (norm := (simp only [qX, qY]; ring1))
        -(σ (.wit 2948) - σ (.wit 2944) + σ (.wit 2937) - qX σ) * o1 -
          (qY σ - σ (.wit 2951)) * o0)
    (by linear_combination (norm := (simp only [outX, qX]; ring1)) -o2)
    (by linear_combination (norm := (simp only [outX, outY]; ring1)) -o3)
  exact ⟨hR, eR.symm⟩

/-! ### The steps -/

/-- The accumulator after `k` steps. -/
def xA (σ : TVar → F) : ℕ → F
  | 0 => oX
  | k + 1 => σ (.wit (s2v k)) - σ (.wit (s1v k)) + σ (.wit (txv k))

def yA (σ : TVar → F) : ℕ → F
  | 0 => oY
  | k + 1 => σ (.wit (yvv k))

/-- Step `k`'s addend: `U`, then `T = ±U` or `±V`. -/
def xS (σ : TVar → F) (k : ℕ) : F := σ (.wit (txv k))

def yS (σ : TVar → F) : ℕ → F
  | 0 => σ (.wit 525) - σ (.plug 3)
  | j + 1 => σ (.wit (540 + 19 * j + 6))

theorem step_eqs {σ : TVar → F} (hf : ∀ r ∈ firstRows, r.Sat σ)
    (hs : ∀ j < 127, ∀ r ∈ stepRows j, r.Sat σ) (k : ℕ) (hk : k < 128) :
    StepEqs (xA σ k) (yA σ k) (xS σ k) (yS σ k) (xA σ (k + 1)) (yA σ (k + 1)) := by
  cases k with
  | zero =>
    have row := fun i (hi : i < firstRows.length) => hf _ (List.getElem_mem hi)
    have r1 := row 0 (by simp [firstRows])
    have r2 := row 1 (by simp [firstRows])
    have r3 := row 2 (by simp [firstRows])
    have r4 := row 3 (by simp [firstRows])
    have r5 := row 4 (by simp [firstRows])
    have r6 := row 5 (by simp [firstRows])
    simp only [firstRows, l2First, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.getElem_cons_zero,
      List.getElem_cons_succ] at r1 r2 r3 r4 r5 r6
    refine ⟨σ (.wit 529), σ (.wit 531), 2 * oY * σ (.wit 533) - σ (.wit 531),
      σ (.wit 532) - oX - σ (.wit 523), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [xA, xS, txv, oX]; linear_combination r1
    · simp only [yA, yS]; linear_combination r2
    · simp only [xA, xS, txv]; linear_combination -r3
    · simp only [xA, yA, oX]; linear_combination r4
    · simp only [xA, s1v, s2v, txv, oX]; linear_combination -r5
    · simp only [xA, yA, s1v, s2v, txv, yvv, oX]; linear_combination r6
  | succ j =>
    have hj : j < 127 := by omega
    have row := fun i (hi : i < (stepRows j).length) => hs j hj _ (List.getElem_mem hi)
    have r4 := row 4 (by simp [stepRows])
    have r5 := row 5 (by simp [stepRows])
    have r6 := row 6 (by simp [stepRows])
    have r7 := row 7 (by simp [stepRows])
    have r8 := row 8 (by simp [stepRows])
    have r9 := row 9 (by simp [stepRows])
    simp only [stepRows, l2Step, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.getElem_cons_zero, List.getElem_cons_succ] at r4 r5 r6 r7 r8 r9
    refine ⟨σ (.wit (540 + 19 * j + 7)), σ (.wit (540 + 19 * j + 9)),
      σ (.wit (540 + 19 * j + 12)) - σ (.wit (540 + 19 * j + 9)),
      σ (.wit (540 + 19 * j + 10)) - xA σ (j + 1) - xS σ (j + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [xA, xS, txv_succ]; linear_combination r4
    · simp only [yA, yS]; linear_combination r5
    · linear_combination -r6
    · simp only [xA, yA, xS, txv_succ]; linear_combination r7
    · simp only [xA, xS, s1v_succ, s2v_succ, txv_succ]; linear_combination -r8
    · simp only [xA, yA, s1v, s2v, txv, yvv] at r9 ⊢; linear_combination r9

/-- The signed table entry `(2a − 1)·(b = a ? U : V)`, as the rows compute it, is
`±P ± Q` with the signs of the bits `a`, `b`. -/
theorem signed_table {a b x y xU yU xV yV : F} {P Q : GrumpkinPoint}
    (hU : grumpkinCurve.Nonsingular xU yU) (hV : grumpkinCurve.Nonsingular xV yV)
    (hUeq : (Point.some _ _ hU : GrumpkinPoint) = P + Q)
    (hVeq : (Point.some _ _ hV : GrumpkinPoint) = P + -Q) (ha : IsBit a) (hb : IsBit b)
    (hx : x = xV + (1 - a - b + 2 * a * b) * (xU - xV))
    (hy : y = (2 * a - 1) * (yV + (1 - a - b + 2 * a * b) * (yU - yV))) :
    ∃ h : grumpkinCurve.Nonsingular x y, (Point.some _ _ h : GrumpkinPoint) =
      (if a.val = 1 then P else -P) + (if b.val = 1 then Q else -Q) := by
  have n0 : ¬(0 : F).val = 1 := by simp
  have n1 : (1 : F).val = 1 := ZMod.val_one _
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [if_neg n0, if_neg n0, ← neg_add, ← hUeq, neg_some hU (neg_ns hU)]
    exact exists_some _ (by rw [hx]; ring) (by rw [hy]; ring)
  · rw [if_neg n0, if_pos n1, show -P + Q = -(P + -Q) by abel, ← hVeq, neg_some hV (neg_ns hV)]
    exact exists_some _ (by rw [hx]; ring) (by rw [hy]; ring)
  · rw [if_pos n1, if_neg n0, ← hVeq]
    exact exists_some _ (by rw [hx]; ring) (by rw [hy]; ring)
  · rw [if_pos n1, if_pos n1, ← hUeq]
    exact exists_some _ (by rw [hx]; ring) (by rw [hy]; ring)

/-- Step `j + 1`'s addend rows make it `±P ± Q`, the signs bits `127 − j` of `s₀`, `s₁`. -/
theorem addend_sound {σ : TVar → F} (hP : grumpkinCurve.Nonsingular (σ (.plug 2)) (σ (.plug 3)))
    (hQ : grumpkinCurve.Nonsingular (σ (.plug 4)) (σ (.plug 5))) (hU : NsU σ) (hV : NsV σ)
    (hUeq : (Point.some _ _ hU : GrumpkinPoint) = Point.some _ _ hP + Point.some _ _ hQ)
    (hVeq : (Point.some _ _ hV : GrumpkinPoint) = Point.some _ _ hP + -Point.some _ _ hQ)
    {j : ℕ} (h : ∀ i (hi : i < (stepRows j).length), i < 4 → Row.Sat (stepRows j)[i] σ)
    (ha : IsBit (σ (.wit (133 - j))))
    (hb : IsBit (σ (.wit (389 - j)))) :
    ∃ hS : grumpkinCurve.Nonsingular (σ (.wit (540 + 19 * j + 3))) (σ (.wit (540 + 19 * j + 6))),
      (Point.some _ _ hS : GrumpkinPoint) =
        (if (σ (.wit (133 - j))).val = 1 then Point.some _ _ hP else -Point.some _ _ hP) +
          (if (σ (.wit (389 - j))).val = 1 then Point.some _ _ hQ else -Point.some _ _ hQ) := by
  have r0 := h 0 (by simp [stepRows]) (by norm_num)
  have r1 := h 1 (by simp [stepRows]) (by norm_num)
  have r2 := h 2 (by simp [stepRows]) (by norm_num)
  have r3 := h 3 (by simp [stepRows]) (by norm_num)
  simp only [stepRows, sel, v1, Row.Sat, LC.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.getElem_cons_zero, List.getElem_cons_succ] at r0 r1 r2 r3
  exact signed_table hU hV hUeq hVeq ha hb
    (by linear_combination -r1 - 2 * (σ (.wit 523) - (σ (.wit 527) - σ (.plug 2) - σ (.plug 4))) * r0)
    (by linear_combination -r3 - (2 * σ (.wit (133 - j)) - 1) * r2 -
      2 * (2 * σ (.wit (133 - j)) - 1) * (σ (.wit 525) - σ (.wit 528)) * r0)

/-! ### Soundness -/

/-- The values of the 128 bits `w(k + i)`. -/
def bits (σ : TVar → F) (k i : ℕ) : ℕ := (σ (.wit (k + i))).val

/-- **Soundness.** Any assignment satisfying the exported rows has scalars below `2¹²⁸`,
`P`, `Q` on Grumpkin with `x_P ≠ x_Q`, and outputs the affine point `s₀·P + s₁·Q`. -/
theorem soundness (σ : TVar → F) (h : template.Sat σ) :
    Spec (template.ins σ) (template.outs σ) := by
  obtain ⟨hoP, hoQ, hl0, hl1, ht, hf, hs, hqr, ho⟩ := (sat_iff σ).mp h
  have hP := oc_sound hoP
  have hQ := oc_sound hoQ
  obtain ⟨hb0, e0⟩ := limb_sound hl0
  obtain ⟨hb1, e1⟩ := limb_sound hl1
  have e0' : (σ (.plug 0)).val = ∑ i ∈ Finset.range 128, 2 ^ i * bits σ 6 i := e0
  have e1' : (σ (.plug 1)).val = ∑ i ∈ Finset.range 128, 2 ^ i * bits σ 262 i := e1
  have hle0 : ∀ i < 128, bits σ 6 i ≤ 1 := fun i hi => Xark.Templates.Add32.isBit_val (hb0 i hi)
  have hle1 : ∀ i < 128, bits σ 262 i ≤ 1 := fun i hi => Xark.Templates.Add32.isBit_val (hb1 i hi)
  obtain ⟨hx, ⟨hU, hUeq⟩, ⟨hV, hVeq⟩⟩ := table_sound hP hQ ht
  set P : GrumpkinPoint := Point.some _ _ hP with hPdef
  set Q : GrumpkinPoint := Point.some _ _ hQ with hQdef
  let S : ℕ → GrumpkinPoint := fun k => addend 128 P (bits σ 6) k + addend 128 Q (bits σ 262) k
  have hS : ∀ j < 128, ∃ h : grumpkinCurve.Nonsingular (xS σ j) (yS σ j),
      Point.some _ _ h = S j := by
    intro j hj
    cases j with
    | zero =>
      refine ⟨hU, ?_⟩
      change _ = addend 128 P (bits σ 6) 0 + addend 128 Q (bits σ 262) 0
      rw [addend, addend, if_pos rfl, if_pos rfl]; exact hUeq
    | succ k =>
      obtain ⟨hS', e⟩ := addend_sound hP hQ hU hV hUeq hVeq
        (fun i hi _ => hs k (by omega) _ (List.getElem_mem hi))
        (by have := hb0 (127 - k) (by omega); rwa [show 6 + (127 - k) = 133 - k by omega] at this)
        (by have := hb1 (127 - k) (by omega); rwa [show 262 + (127 - k) = 389 - k by omega] at this)
      refine ⟨hS', e.trans ?_⟩
      change _ = addend 128 P (bits σ 6) (k + 1) + addend 128 Q (bits σ 262) (k + 1)
      rw [addend, addend, if_neg (Nat.succ_ne_zero k), if_neg (Nat.succ_ne_zero k),
        show 128 - (k + 1) = 127 - k by omega, bits, bits, show 6 + (127 - k) = 133 - k by omega,
        show 262 + (127 - k) = 389 - k by omega]
  have h0 : grumpkinCurve.Nonsingular (xA σ 0) (yA σ 0) := oNs
  obtain ⟨hA, hAeq⟩ := DoubleAdd.chain_sound short (xA := xA σ) (yA := yA σ) (xS := xS σ)
    (yS := yS σ) (S := S) 128 h0 hS (fun j hj => step_eqs hf hs j hj)
  rw [show (Point.some _ _ h0 : GrumpkinPoint) = O from rfl] at hAeq
  have acc0 := accum_digits O P 128 (bits σ 6) hle0 _ e0' (addend 128 P (bits σ 6))
    (by rw [addend, if_pos rfl]) (fun j hj1 _ => by rw [addend, if_neg (by omega)]) 128
    (by norm_num) le_rfl
  have acc1 := accum_digits O Q 128 (bits σ 262) hle1 _ e1' (addend 128 Q (bits σ 262))
    (by rw [addend, if_pos rfl]) (fun j hj1 _ => by rw [addend, if_neg (by omega)]) 128
    (by norm_num) le_rfl
  rw [show 128 + 1 - 128 = 1 from rfl, pow_one] at acc0 acc1
  have hacc : accum O S 128 = (2 ^ 128) • O + (2 * ((σ (.plug 0)).val / 2) + 1) • P +
      (2 * ((σ (.plug 1)).val / 2) + 1) • Q := by
    have e := accum_add O (addend 128 P (bits σ 6)) (addend 128 Q (bits σ 262)) 128
    rw [acc0, acc1] at e
    rw [eq_sub_of_add_eq e]
    module
  have hmod : ∀ k p, (σ (.plug p)).val = ∑ i ∈ Finset.range 128, 2 ^ i * bits σ k i →
      (∀ i < 128, bits σ k i ≤ 1) → (σ (.plug p)).val % 2 = (σ (.wit k)).val := fun k p e hle => by
    have := word_div_mod (bits σ k) 128 hle 0 (by norm_num)
    rw [← e] at this
    simpa [bits] using this
  have hb6 : IsBit (σ (.wit 6)) := hb0 0 (by norm_num)
  have hb262 : IsBit (σ (.wit 262)) := hb1 0 (by norm_num)
  obtain ⟨hq, eq⟩ := q_sound hP hQ hU hUeq hb6 hb262 hqr
  have hA' : grumpkinCurve.Nonsingular (σ (.wit 2948) - σ (.wit 2944) + σ (.wit 2937))
      (σ (.wit 2951)) := hA
  obtain ⟨hR, eR⟩ := out_sound hA' hq ho
  have wlt : ∀ k p, (σ (.plug p)).val = ∑ i ∈ Finset.range 128, 2 ^ i * bits σ k i →
      (∀ i < 128, bits σ k i ≤ 1) → (σ (.plug p)).val < 2 ^ 128 := fun k p e hle => by
    rw [e]; exact Xark.Templates.Add32.word_lt _ 128 hle
  rw [Spec, ins_getD σ (show 0 < 6 by norm_num), ins_getD σ (show 1 < 6 by norm_num),
    ins_getD σ (show 2 < 6 by norm_num), ins_getD σ (show 3 < 6 by norm_num),
    ins_getD σ (show 4 < 6 by norm_num), ins_getD σ (show 5 < 6 by norm_num), outs_eq]
  refine ⟨wlt 6 0 e0' hle0, wlt 262 1 e1' hle1, hx, hP, hQ, hR, ?_⟩
  change (Point.some (outX σ) (outY σ) hR : GrumpkinPoint) = (σ (.plug 0)).val • P + (σ (.plug 1)).val • Q
  rw [eR, eq, show (Point.some _ _ hA' : GrumpkinPoint) = Point.some _ _ hA from rfl, hAeq, hacc,
    qPt, ← hmod 6 0 e0' hle0, ← hmod 262 1 e1' hle1]
  exact final_eq2 O P Q _ 128 _ _ corr_eq

end Xark.Templates.MultiScalarMul
