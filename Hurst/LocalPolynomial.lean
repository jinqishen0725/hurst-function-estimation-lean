import Hurst.Basic

/-! Finite-design algebra behind (2.7), (8.7), Lemma 8.4 and Theorem 3.2.
Moment conditions are explicit hypotheses; invertibility and uniform bounds
for the paper's actual design matrices are not proved here. -/
noncomputable section
open scoped BigOperators
namespace Hurst

variable {ι : Type*} [Fintype ι]

def smooth (w y : ι → ℝ) : ℝ := ∑ i, w i * y i

theorem smooth_constant (w : ι → ℝ) (c : ℝ) (hw : ∑ i, w i = 1) :
    smooth w (fun _ => c) = c := by
  unfold smooth
  rw [← Finset.sum_mul, hw, one_mul]

theorem smooth_add (w x y : ι → ℝ) : smooth w (fun i => x i+y i) = smooth w x+smooth w y := by
  simp [smooth, mul_add, Finset.sum_add_distrib]

theorem smooth_scale (w x : ι → ℝ) (a : ℝ) : smooth w (fun i => a*x i) = a*smooth w x := by
  simp only [smooth, mul_left_comm (w _) a, Finset.mul_sum]

theorem smooth_error (w y : ι → ℝ) (c : ℝ) (hw : ∑ i, w i = 1) :
    smooth w y-c = smooth w (fun i => y i-c) := by
  simp [smooth, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw]

/-- Equation (8.7), including the partition-of-unity assumption on local weights. -/
theorem log_estimator_decomposition (w H z : ι → ℝ) (L c : ℝ)
    (hw : ∑ i, w i = 1) :
    smooth w (fun i => -2*L*H i+z i+c) = -2*L*smooth w H+smooth w z+c := by
  rw [smooth_add, smooth_add, smooth_scale, smooth_constant w c hw]

/-- Reproduction for the selected polynomial basis A; the first basis function is 1. -/
theorem polynomial_reproduction {κ : Type*} [Fintype κ] [DecidableEq κ]
    (zeroIndex : κ) (w : ι → ℝ) (A : ι → κ → ℝ) (β : κ → ℝ)
    (hMom : ∀ k, (∑ i, w i * A i k) = if k = zeroIndex then 1 else 0) :
    smooth w (fun i => ∑ k, β k*A i k) = β zeroIndex := by
  unfold smooth
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (w _) (β _), ← Finset.mul_sum, hMom]
  simp

/-- Taylor residual control: valid even when the local polynomial weights are negative. -/
theorem smooth_residual_bound (w r : ι → ℝ) (B : ℝ)
    (hr : ∀ i, |r i| ≤ B) : |smooth w r| ≤ (∑ i, |w i|)*B := by
  calc
    |smooth w r| ≤ ∑ i, |w i*r i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| *B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hr i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Error introduced by estimating the nuisance log variance (4.3). -/
theorem backfitting_error_decomposition (Ghat Gtrue σhat σtrue : ℝ) :
    (Ghat-σhat)-(Gtrue-σtrue) = (Ghat-Gtrue)-(σhat-σtrue) := by ring

/-- Cancellation of the unknown scale in the pilot (4.1). -/
theorem pilot_scale_cancels (H L c logTwo : ℝ) (h : logTwo ≠ 0) :
    ((-2*H*L+c+2*H*logTwo)-(-2*H*L+c))/(2*logTwo) = H := by
  field_simp; ring

/-- In the critical double sum, a small gap localizes j near i, not i near 0.
This exact diagonal identity explains the missing integral of f² in S.3.2. -/
theorem diagonal_weight_product (f : ι → ℝ) :
    (∑ i, f i*f i) = ∑ i, (f i)^2 := by simp [pow_two]

theorem diagonal_not_center_value :
    (∑ i : Fin 3, ((i.val : ℝ)-1)^2) ≠ (3:ℝ) * (((1:ℝ)-1)^2) := by
  norm_num [Fin.sum_univ_succ]

end Hurst
