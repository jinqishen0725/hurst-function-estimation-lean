import Hurst.FeatureHermiteApproximation
import Hurst.L2TestApproximation
import Hurst.GaussianPolynomialLaw

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst
variable {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gaussianLogTruncationStatistic_memLp_two (v : ι → E) (w : κ → ℝ)
    (a : κ → EuclideanSpace ℝ ι) (K : ℕ) :
    MemLp (gaussianLogTruncationStatistic v w a K) 2 (featureGaussian v) := by
  apply memLp_finsetSum
  intro i _
  exact (gaussianLaw_polynomial_memLp_two
    (standardizedFeatureObservation_pair v (a i) (a i)).fst
    (hermiteTruncationPolynomial gaussianLogLp K)).const_mul (w i)

theorem featureGaussian_log_truncation_test_bound (v : ι → E) (w : κ → ℝ)
    (a : κ → EuclideanSpace ℝ ι) (ha : ∀ j,∑ i,a j i • v i≠0)
    (B : ℝ) (hrow : ∀ i,∑ j,featureCorrelation v (a i) (a j)^2≤B)
    (K : ℕ) (c : ℝ) (φ : ℝ → ℝ) (hφ : LipschitzWith 1 φ) (hb : ∀ x,|φ x|≤1) :
    |(∫ x,φ (c*(gaussianLogStatistic w a x-
        (∫ y,gaussianLogStatistic w a y ∂featureGaussian v))) ∂featureGaussian v)-
      (∫ x,φ (c*gaussianLogTruncationStatistic v w a K x) ∂featureGaussian v)| ≤
      Real.sqrt (c^2*(‖hermiteTail gaussianLogLp K‖^2*B*∑ i,w i^2)) := by
  have hX := ((gaussianLogStatistic_memLp_two v w a ha).sub (memLp_const
    (∫ y,gaussianLogStatistic w a y ∂featureGaussian v))).const_mul c
  have hY := (gaussianLogTruncationStatistic_memLp_two v w a K).const_mul c
  have he := bounded_lipschitz_integral_L2_bound (featureGaussian v) _ _ hX hY φ hφ hb
  have hid : (∫ x,(c*(gaussianLogStatistic w a x-
        (∫ y,gaussianLogStatistic w a y ∂featureGaussian v))-
      c*gaussianLogTruncationStatistic v w a K x)^2 ∂featureGaussian v) =
      c^2*(∫ x,(gaussianLogStatistic w a x-
        (∫ y,gaussianLogStatistic w a y ∂featureGaussian v)-
      gaussianLogTruncationStatistic v w a K x)^2 ∂featureGaussian v) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  apply he.trans
  apply Real.sqrt_le_sqrt
  change (∫ x,(c*(gaussianLogStatistic w a x-
        (∫ y,gaussianLogStatistic w a y ∂featureGaussian v))-
      c*gaussianLogTruncationStatistic v w a K x)^2 ∂featureGaussian v) ≤ _
  rw [hid]
  exact mul_le_mul_of_nonneg_left (featureGaussian_log_truncation_error v w a ha B hrow K) (sq_nonneg c)

end Hurst
