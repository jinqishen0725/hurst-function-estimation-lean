import Hurst.ActiveBSPolynomialConditions
import Hurst.FeatureObservationMap

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- Exact law bridge from the original local finite-Hermite statistic to the
active-row polynomial statistic with B&S normalization.  This combines zero
weight deletion, standardized-feature pushforward, and the active-card scaling
identity; it contains no asymptotic or external premise. -/
theorem gaussianLogTruncationStatistic_activeBS_identDistrib
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n q M : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (v : Fin n → E)
    (a : Fin (n - q) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) :
    IdentDistrib
      (fun x => Real.sqrt ((n : ℝ) * δ) *
        gaussianLogTruncationStatistic v
          (localPolynomialWeights r n q δ t) a M x)
      (fun x =>
        (Real.sqrt ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
          ∑ j, (activeBSPolynomial r n q δ t
            (hermiteTruncationPolynomial gaussianLogLp M) j).eval
              (standardizedFeatureObservation
                (fun k => standardizedFeatureVector v
                  (a (localWeightActiveIndex n q δ t k)))
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n q δ t).card) ℝ j) x))
      (featureGaussian v)
      (featureGaussian (fun k => standardizedFeatureVector v
        (a (localWeightActiveIndex n q δ t k)))) := by
  let w : Fin (localWeightActiveSet n q δ t).card → ℝ := fun j =>
    localPolynomialWeights r n q δ t (localWeightActiveIndex n q δ t j)
  let a' : Fin (localWeightActiveSet n q δ t).card →
      EuclideanSpace ℝ (Fin n) := fun j =>
    a (localWeightActiveIndex n q δ t j)
  let u : Fin (localWeightActiveSet n q δ t).card → E := fun j =>
    standardizedFeatureVector v (a' j)
  have ha' : ∀ j, ∑ i, a' j i • v i ≠ 0 := fun j =>
    ha (localWeightActiveIndex n q δ t j)
  have hu : ∀ j, ‖u j‖ = 1 := fun j =>
    norm_standardizedFeatureVector v (a' j) (ha' j)
  have hid := gaussianLogTruncationStatistic_identDistrib_normalizedFeatures
    v w a' ha' M
  have hscaled := hid.const_mul (Real.sqrt ((n : ℝ) * δ))
  convert hscaled using 1
  · funext x
    rw [gaussianLogTruncationStatistic_local_active]
    rfl
  · funext x
    rw [gaussianLogTruncationStatistic_basis_normalized u hu w M x]
    change (Real.sqrt ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
        ∑ j, (activeBSPolynomial r n q δ t
          (hermiteTruncationPolynomial gaussianLogLp M) j).eval
            (standardizedFeatureObservation u
              (EuclideanSpace.basisFun
                (Fin (localWeightActiveSet n q δ t).card) ℝ j) x) =
      Real.sqrt ((n : ℝ) * δ) *
        ∑ k, w k * (hermiteTruncationPolynomial gaussianLogLp M).eval (x k)
    rw [show (∑ j, (activeBSPolynomial r n q δ t
        (hermiteTruncationPolynomial gaussianLogLp M) j).eval
          (standardizedFeatureObservation u
            (EuclideanSpace.basisFun
              (Fin (localWeightActiveSet n q δ t).card) ℝ j) x)) =
      ∑ j, (activeBSPolynomial r n q δ t
        (hermiteTruncationPolynomial gaussianLogLp M) j).eval (x j) by
          apply Finset.sum_congr rfl
          intro j hj
          rw [standardizedFeatureObservation_basis_normalized u hu x j]]
    exact activeBSPolynomial_normalized_sum r n q hn δ t hδ
      (hermiteTruncationPolynomial gaussianLogLp M) hcard x

theorem gaussianLogTruncationStatistic_activeBS_variance_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n q M : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (v : Fin n → E)
    (a : Fin (n - q) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) :
    Var[fun x => Real.sqrt ((n : ℝ) * δ) *
      gaussianLogTruncationStatistic v
        (localPolynomialWeights r n q δ t) a M x; featureGaussian v] =
    Var[fun x =>
      (Real.sqrt ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
        ∑ j, (activeBSPolynomial r n q δ t
          (hermiteTruncationPolynomial gaussianLogLp M) j).eval
            (standardizedFeatureObservation
              (fun k => standardizedFeatureVector v
                (a (localWeightActiveIndex n q δ t k)))
              (EuclideanSpace.basisFun
                (Fin (localWeightActiveSet n q δ t).card) ℝ j) x);
      featureGaussian (fun k => standardizedFeatureVector v
        (a (localWeightActiveIndex n q δ t k)))] :=
  (gaussianLogTruncationStatistic_activeBS_identDistrib
    r n q M hn δ t hδ hcard v a ha).variance_eq

end Hurst
