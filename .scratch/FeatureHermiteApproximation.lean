import Hurst.FeatureStandardGaussian
import Hurst.GaussianArrayApproximation

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst
variable {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussianLogTruncationStatistic (v : ι → E) (w : κ → ℝ)
    (a : κ → EuclideanSpace ℝ ι) (M : ℕ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i,w i*(hermiteTruncationPolynomial gaussianLogLp M).eval (standardizedFeatureObservation v (a i) x)

theorem standardizedFeatureObservation_centered_log (v : ι → E) (a : EuclideanSpace ℝ ι)
    (ha : ∑ i,a i • v i≠0) :
    (fun x => centeredGaussianLog (standardizedFeatureObservation v a x)) =ᵐ[featureGaussian v]
      fun x => Real.log (⟪a,x⟫^2)-(∫ y,Real.log (⟪a,y⟫^2) ∂featureGaussian v) := by
  filter_upwards [featureGaussian_linear_ae_ne_zero v a ha] with x hx
  have hs : ‖∑ i,a i • v i‖≠0 := norm_ne_zero_iff.mpr ha
  rw [featureGaussian_expected_log_square v a ha]
  unfold centeredGaussianLog standardizedFeatureObservation
  rw [div_pow,Real.log_div (pow_ne_zero 2 hx) (pow_ne_zero 2 hs)]
  ring

theorem gaussianLogStatistic_centered_standardized (v : ι → E) (w : κ → ℝ)
    (a : κ → EuclideanSpace ℝ ι) (ha : ∀ j,∑ i,a j i • v i≠0) :
    (fun x => gaussianLogStatistic w a x-(∫ y,gaussianLogStatistic w a y ∂featureGaussian v)) =ᵐ[featureGaussian v]
      fun x => ∑ i,w i*centeredGaussianLog (standardizedFeatureObservation v (a i) x) := by
  have hi (i : κ) : Integrable (fun y => w i*Real.log (⟪a i,y⟫^2)) (featureGaussian v) :=
    ((featureGaussian_log_square_memLp_two v (a i) (ha i)).integrable (by norm_num)).const_mul _
  filter_upwards [ae_all_iff.mpr (fun i => standardizedFeatureObservation_centered_log v (a i) (ha i))]
    with x hx
  unfold gaussianLogStatistic
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [integral_const_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hx i]
  ring

theorem featureGaussian_log_truncation_error (v : ι → E) (w : κ → ℝ)
    (a : κ → EuclideanSpace ℝ ι) (ha : ∀ j,∑ i,a j i • v i≠0)
    (B : ℝ) (hrow : ∀ i,∑ j,featureCorrelation v (a i) (a j)^2≤B) (M : ℕ) :
    (∫ x,(gaussianLogStatistic w a x-(∫ y,gaussianLogStatistic w a y ∂featureGaussian v)-
      gaussianLogTruncationStatistic v w a M x)^2 ∂featureGaussian v) ≤
        ‖hermiteTail gaussianLogLp M‖^2*B*∑ i,w i^2 := by
  have he := gaussian_array_log_polynomial_error (featureGaussian v)
    (fun i => standardizedFeatureObservation v (a i)) (fun i => standardizedFeatureObservation_law v (a i) (ha i))
    (fun i j => standardizedFeatureObservation_pair v (a i) (a j)) w B
    (by simpa only [standardizedFeatureObservation_covariance] using hrow) M
  have hid : (∫ x,(gaussianLogStatistic w a x-(∫ y,gaussianLogStatistic w a y ∂featureGaussian v)-
      gaussianLogTruncationStatistic v w a M x)^2 ∂featureGaussian v) =
      ∫ x,(∑ i,w i*(centeredGaussianLog (standardizedFeatureObservation v (a i) x)-
        (hermiteTruncationPolynomial gaussianLogLp M).eval (standardizedFeatureObservation v (a i) x)))^2
          ∂featureGaussian v := by
    apply integral_congr_ae
    filter_upwards [gaussianLogStatistic_centered_standardized v w a ha] with x hx
    rw [hx,gaussianLogTruncationStatistic,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [hid]

end Hurst
