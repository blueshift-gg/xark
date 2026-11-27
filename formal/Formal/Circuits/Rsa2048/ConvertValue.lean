import Formal.Circuits.Rsa2048.ConvertBounds
set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace Xark.Circuits.Rsa2048
open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

theorem geom_lt (y : ℕ → ℤ) (k : ℕ) (h0 : ∀ j < k, 0 ≤ y j) (h : ∀ j < k, y j < W) :
    (∑ j ∈ Finset.range k, y j * W ^ j) < W ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ih' := ih (fun j hj => h0 j (by omega)) (fun j hj => h j (by omega))
    have hyk := h k (by omega)
    have hWpos : (0 : ℤ) < W := by rw [show W = 2 ^ 82 from rfl]; positivity
    have hstep : y k * W ^ k < W * W ^ k :=
      mul_lt_mul_of_pos_right hyk (by positivity)
    have hpow : W ^ (k + 1) = W ^ k * W := by rw [pow_succ]
    rw [hpow]
    nlinarith [ih', hstep]

theorem n_val_lt (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (∑ j ∈ Finset.range 25, yN σ j * (W : ℤ) ^ j) < 2 ^ 2048 := by
  have h24 := geom_lt (fun j => yN σ j) 24 (fun j hj => by unfold yN; positivity)
    (fun j hj => by
      have := n_limb_lt82 σ h j (by omega)
      rw [show yN σ j = ((σ (nLimb.getD j 0)).val : ℤ) from rfl]
      rw [show (W : ℤ) = 2 ^ 82 from rfl]
      exact_mod_cast this)
  have hy24 : yN σ 24 < 2 ^ 80 := by
    rw [show yN σ 24 = ((σ (nLimb.getD 24 0)).val : ℤ) from rfl]
    have := n_limb_bnd24 σ h
    exact_mod_cast this
  rw [Finset.sum_range_succ]
  have hW : (W : ℤ) = 2 ^ 82 := rfl
  have hpow : (2 : ℤ) ^ 80 * W ^ 24 = 2 ^ 2048 := by
    rw [hW, ← pow_mul, ← pow_add]
  have hW24 : (0 : ℤ) ≤ W ^ 24 := by positivity
  nlinarith [h24, hy24, hpow, hW24]


theorem s_val_lt (σ : ℕ → F) (h : Sat Rsa2048Words.circuit σ) :
    (∑ j ∈ Finset.range 25, yS σ j * (W : ℤ) ^ j) < 2 ^ 2048 := by
  have h24 := geom_lt (fun j => yS σ j) 24 (fun j hj => by unfold yS; positivity)
    (fun j hj => by
      have := s_limb_lt82 σ h j (by omega)
      rw [show yS σ j = ((σ (sLimb.getD j 0)).val : ℤ) from rfl]
      rw [show (W : ℤ) = 2 ^ 82 from rfl]
      exact_mod_cast this)
  have hy24 : yS σ 24 < 2 ^ 80 := by
    rw [show yS σ 24 = ((σ (sLimb.getD 24 0)).val : ℤ) from rfl]
    have := s_limb_bnd24 σ h
    exact_mod_cast this
  rw [Finset.sum_range_succ]
  have hW : (W : ℤ) = 2 ^ 82 := rfl
  have hpow : (2 : ℤ) ^ 80 * W ^ 24 = 2 ^ 2048 := by
    rw [hW, ← pow_mul, ← pow_add]
  have hW24 : (0 : ℤ) ≤ W ^ 24 := by positivity
  nlinarith [h24, hy24, hpow, hW24]

end Xark.Circuits.Rsa2048

