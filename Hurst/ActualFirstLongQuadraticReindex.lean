import Hurst.ActiveSetReindex
import Hurst.FirstStrideActualRows
import Hurst.FeatureQuadraticLimit

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- The quadratic Hermite statistic is unchanged when zero local weights are
deleted and the remaining indices are listed in increasing order. -/
theorem gaussianLogQuadraticStatistic_local_active
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n q : ℕ) (δ t : ℝ) (v : Fin n → E)
    (a : Fin (n - q) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianLogQuadraticStatistic v (localPolynomialWeights r n q δ t) a x =
      ∑ j, localPolynomialWeights r n q δ t
          (localWeightActiveIndex n q δ t j) *
        ((standardizedFeatureObservation v
            (a (localWeightActiveIndex n q δ t j)) x) ^ 2 - 1) := by
  exact localPolynomialWeights_sum_active r n q δ t
    (fun i => (standardizedFeatureObservation v (a i) x) ^ 2 - 1)

/-- On the actual q=1 model, the covariance matrix of the standardized
observations on the active local window is exactly the correlation matrix of
the normalized varying-Hurst increments. -/
theorem q1_active_standardized_covariance_eq_actual_correlation
    (n : ℕ) (hn : 0 < n) (H : Fin n → Ioo (0 : ℝ) 1)
    (r : ℕ) (δ t : ℝ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) :
    cov[
      standardizedFeatureObservation (gridObservationFeatures n H)
        (gridDifferenceCoefficients n (localWeightActiveIndex n 1 δ t i)),
      standardizedFeatureObservation (gridObservationFeatures n H)
        (gridDifferenceCoefficients n (localWeightActiveIndex n 1 δ t j));
      featureGaussian (gridObservationFeatures n H)] =
      vectorCorrelation
        (gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t i))
        (gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j)) := by
  rw [standardizedFeatureObservation_covariance]
  exact gridStrideFirst_correlation_identity n 1 hn (by norm_num) H _ _

/-- Exact active-window form of the actual q=1 long-memory quadratic term.
This is the finite Gaussian quadratic form to which the second-chaos theorem
is applied; no distributional or asymptotic input is used here. -/
theorem q1_actual_quadraticStatistic_active
    (r n : ℕ) (δ t : ℝ)
    (H : Fin n → Ioo (0 : ℝ) 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianLogQuadraticStatistic
        (gridObservationFeatures n H)
        (localPolynomialWeights r n 1 δ t)
        (gridDifferenceCoefficients n) x =
      ∑ j, localPolynomialWeights r n 1 δ t
          (localWeightActiveIndex n 1 δ t j) *
        ((standardizedFeatureObservation (gridObservationFeatures n H)
            (gridDifferenceCoefficients n
              (localWeightActiveIndex n 1 δ t j)) x) ^ 2 - 1) := by
  exact gaussianLogQuadraticStatistic_local_active r n 1 δ t
    (gridObservationFeatures n H) (gridDifferenceCoefficients n) x

end Hurst
