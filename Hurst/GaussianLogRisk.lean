import Hurst.GaussianLogCovariance

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def featureCorrelation (v : ι → E) (a b : EuclideanSpace ℝ ι) : ℝ :=
  ⟪∑ i, a i • v i, ∑ i, b i • v i⟫ / (‖∑ i, a i • v i‖ * ‖∑ i, b i • v i‖)

theorem featureGaussian_log_covariance_bound (v : ι → E) (a b : EuclideanSpace ℝ ι)
    (ha : ∑ i, a i • v i ≠ 0) (hb : ∑ i, b i • v i ≠ 0) :
    |cov[fun x => Real.log (⟪a, x⟫ ^ 2), fun x => Real.log (⟪b, x⟫ ^ 2); featureGaussian v]| ≤
      4 * gaussianLogSquareVariance * (featureCorrelation v a b) ^ 2 := by
  have hpair : HasGaussianLaw (fun x => (⟪a, x⟫, ⟪b, x⟫)) (featureGaussian v) :=
    IsGaussian.hasGaussianLaw_id.map_fun ((innerSL ℝ a).prod (innerSL ℝ b))
  have h := gaussian_log_square_covariance_bound_general (featureGaussian v)
    (fun x => ⟪a, x⟫) (fun x => ⟪b, x⟫) (by fun_prop) (by fun_prop) hpair
    (featureGaussian_linear_mean v a) (featureGaussian_linear_mean v b)
    (featureGaussian_linear_variance_pos v a ha) (featureGaussian_linear_variance_pos v b hb)
  simpa only [featureGaussian_linear_covariance, featureGaussian_linear_variance,
    featureCorrelation, div_pow, mul_pow] using h

theorem gaussianLogStatistic_variance_correlation_bound {κ : Type*} [Fintype κ]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) :
    Var[gaussianLogStatistic w a; featureGaussian v] ≤
      4 * gaussianLogSquareVariance * ∑ j, ∑ k, |w j| * |w k| * (featureCorrelation v (a j) (a k)) ^ 2 := by
  rw [gaussianLogStatistic_variance v w a h]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  have hc := featureGaussian_log_covariance_bound v (a j) (a k) (h j) (h k)
  calc
    _ ≤ |w j * w k * cov[fun x => Real.log (⟪a j, x⟫ ^ 2), fun x => Real.log (⟪a k, x⟫ ^ 2); featureGaussian v]| := le_abs_self _
    _ = |w j| * |w k| * |cov[fun x => Real.log (⟪a j, x⟫ ^ 2), fun x => Real.log (⟪a k, x⟫ ^ 2); featureGaussian v]| := by simp only [abs_mul]
    _ ≤ |w j| * |w k| * (4 * gaussianLogSquareVariance * (featureCorrelation v (a j) (a k)) ^ 2) :=
      mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

theorem gaussianLogStatistic_variance_row_bound {κ : Type*} [Fintype κ]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) (W L R : ℝ)
    (hW : 0 ≤ W) (hR : 0 ≤ R) (hw : ∀ j, |w j| ≤ W)
    (hL : ∑ j, |w j| ≤ L)
    (hrow : ∀ j, ∑ k, (featureCorrelation v (a j) (a k)) ^ 2 ≤ R) :
    Var[gaussianLogStatistic w a; featureGaussian v] ≤ 4 * gaussianLogSquareVariance * (L * W * R) := by
  apply (gaussianLogStatistic_variance_correlation_bound v w a h).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg)
  calc
    _ ≤ ∑ j, |w j| * (W * R) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ k, |w j| * W * (featureCorrelation v (a j) (a k)) ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw k) (abs_nonneg _)) (sq_nonneg _)
        _ = |w j| * W * ∑ k, (featureCorrelation v (a j) (a k)) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ |w j| * W * R := mul_le_mul_of_nonneg_left (hrow j) (mul_nonneg (abs_nonneg _) hW)
        _ = _ := by ring
    _ = (∑ j, |w j|) * (W * R) := by rw [Finset.sum_mul]
    _ ≤ L * (W * R) := mul_le_mul_of_nonneg_right hL (mul_nonneg hW hR)
    _ = _ := by ring

end Hurst
