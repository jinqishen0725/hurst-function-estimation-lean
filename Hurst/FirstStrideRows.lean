import Hurst.FirstStrideDecay
import Hurst.GridCorrelationRows

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem first_stride_rows_of_covariance (a b C : ℝ) (d : ℕ) (hd : 0 < d)
    (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hC : 0 ≤ C) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ n →
      ∀ H : Fin m → Ioo (0:ℝ) 1, (∀ i, (H i:ℝ) ∈ Icc a b) →
      ∀ W : Fin m → Lp ℂ 2 (volume : Measure ℝ),
      (∀ i j, |⟪W i,W j⟫-⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d:ℝ)/n),
        normalizedFrozenIncrement (H j) (grid n j.val) ((d:ℝ)/n)⟫| ≤ gridCovarianceError b C n) →
      (∀ i, W i ≠ 0) ∧ ∀ i, (∑ j, vectorCorrelation (W i) (W j)^2) ≤ R := by
  obtain ⟨A,hA,hdec⟩ := frozen_stride_first_grid_decay a b ha hb hab d hd
  let S := ∑' k, strideFirstDecay b d k^2
  refine ⟨64*A^2*S+32, by dsimp [S]; positivity, ?_⟩
  have he := (gridCovarianceError_tendsto b C (by linarith)).eventually_le_const (by norm_num : (0:ℝ) < 1/2)
  have he2 := (gridCovarianceError_square_row_tendsto b C hb).eventually_le_const zero_lt_one
  filter_upwards [eventually_ge_atTop 1,he,he2] with n hn hsmall hsquare
  intro m hmn H hH W hp
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  let e := gridCovarianceError b C n
  have he0 : 0 ≤ e := by
    dsimp [e,gridCovarianceError]
    have := Real.log_nonneg (show (1:ℝ) ≤ 2*n by linarith)
    positivity
  have hfloor : ∀ i, (1/2:ℝ) ≤ ‖W i‖ := by
    intro i
    have hh := hp i i
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hh
    have he := (abs_le.mp hh).1
    nlinarith [norm_nonneg (W i)]
  refine ⟨?_,?_⟩
  · intro i hz
    have he := hfloor i
    rw [hz,norm_zero] at he
    norm_num at he
  · intro i
    have hcorr : ∀ i j, |vectorCorrelation (W i) (W j)| ≤ 4*A*strideFirstDecay b d (Nat.dist j.val i.val)+4*e := by
      intro i j
      have hf := hdec n m (by omega) H hH i j
      have he := hp i j
      have ht := abs_add_le (⟪W i,W j⟫-⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d:ℝ)/n),normalizedFrozenIncrement (H j) (grid n j.val) ((d:ℝ)/n)⟫)
        ⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d:ℝ)/n),normalizedFrozenIncrement (H j) (grid n j.val) ((d:ℝ)/n)⟫
      rw [sub_add_cancel] at ht
      have hc := vectorCorrelation_bound_of_norm_floor (W i) (W j) (hfloor i) (hfloor j)
      dsimp only [e]
      linarith
    have hs := stride_first_correlation_square_row_bound b (4*A) (4*e) d hd hb (by linarith) (by positivity)
      m (fun i j => vectorCorrelation (W i) (W j)) hcorr i
    have hm : (m:ℝ) ≤ n := by exact_mod_cast hmn
    have hm2 := mul_le_mul_of_nonneg_right hm (sq_nonneg e)
    change (n:ℝ)*e^2 ≤ 1 at hsquare
    dsimp only [S]
    nlinarith

end Hurst
