import Hurst.VariableRowBSCLT
import Hurst.SafeStandardizedFeatureRow
import Hurst.ActiveBSApplicability
import Hurst.ActiveStatisticLaw
import Hurst.ActualFullTruncatedVarianceLimit
import Hurst.OptimalActiveRowDensity

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace Hurst

def activeBSCoefficient (r n q : ℕ) (δ t : ℝ)
    (j : Fin (localWeightActiveSet n q δ t).card) : ℝ :=
  Real.sqrt (((localWeightActiveSet n q δ t).card : ℝ) /
      ((n : ℝ) * δ)) *
    (((n : ℝ) * δ) * localPolynomialWeights r n q δ t
      (localWeightActiveIndex n q δ t j))

def safeActiveFeatureRow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n q : ℕ) (δ t : ℝ) (v : Fin n → E)
    (a : Fin (n - q) → EuclideanSpace ℝ (Fin n)) :=
  safeStandardizedFeatureRow v
    (fun j : Fin (localWeightActiveSet n q δ t).card =>
      a (localWeightActiveIndex n q δ t j))

theorem safeActiveFeatureRow_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n q : ℕ) (δ t : ℝ) (v : Fin n → E)
    (a : Fin (n - q) → EuclideanSpace ℝ (Fin n)) :
    ∀ j, ‖safeActiveFeatureRow n q δ t v a j‖ = 1 :=
  safeStandardizedFeatureRow_norm v _

theorem safeActiveFeatureRow_correlation_of_nonzero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n q : ℕ) (δ t : ℝ) (v : Fin n → E)
    (a : Fin (n - q) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) (i j) :
    featureCorrelation (safeActiveFeatureRow n q δ t v a)
      (EuclideanSpace.basisFun
        (Fin (localWeightActiveSet n q δ t).card) ℝ i)
      (EuclideanSpace.basisFun
        (Fin (localWeightActiveSet n q δ t).card) ℝ j) =
      featureCorrelation v
        (a (localWeightActiveIndex n q δ t i))
        (a (localWeightActiveIndex n q δ t j)) := by
  exact safeStandardizedFeatureRow_correlation_of_nonzero v _
    (fun k => ha (localWeightActiveIndex n q δ t k)) i j

/-- The safe active-row normalized finite-Hermite variance agrees with the
original local statistic whenever the actual observations are nondegenerate. -/
theorem safeActiveFeatureRow_normalized_variance_eq_original
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n q K : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (v : Fin n → E) (a : Fin (n - q) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) :
    Var[fun x => (Real.sqrt
        ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (safeActiveFeatureRow n q δ t v a)
        (activeBSCoefficient r n q δ t)
        (fun i => EuclideanSpace.basisFun
          (Fin (localWeightActiveSet n q δ t).card) ℝ i) K x;
      featureGaussian (safeActiveFeatureRow n q δ t v a)] =
    Var[fun x => Real.sqrt ((n : ℝ) * δ) *
      gaussianLogTruncationStatistic v
        (localPolynomialWeights r n q δ t) a K x;
      featureGaussian v] := by
  have hsafeMeasure : featureGaussian (safeActiveFeatureRow n q δ t v a) =
      featureGaussian (fun k => standardizedFeatureVector v
        (a (localWeightActiveIndex n q δ t k))) := by
    exact safeStandardizedFeatureRow_gaussian_eq_of_nonzero v _
      (fun k => ha (localWeightActiveIndex n q δ t k))
  have hfun : (fun x => (Real.sqrt
        ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (safeActiveFeatureRow n q δ t v a)
        (activeBSCoefficient r n q δ t)
        (fun i => EuclideanSpace.basisFun
          (Fin (localWeightActiveSet n q δ t).card) ℝ i) K x) =
      (fun x => (Real.sqrt
        ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
        ∑ j, (activeBSPolynomial r n q δ t
          (hermiteTruncationPolynomial gaussianLogLp K) j).eval
            (standardizedFeatureObservation
              (fun k => standardizedFeatureVector v
                (a (localWeightActiveIndex n q δ t k)))
              (EuclideanSpace.basisFun
                (Fin (localWeightActiveSet n q δ t).card) ℝ j) x)) := by
    funext x
    rw [gaussianLogTruncationStatistic_basis_normalized
      (safeActiveFeatureRow n q δ t v a)
      (safeActiveFeatureRow_norm n q δ t v a)]
    apply congrArg ((Real.sqrt
      ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro j _
    rw [standardizedFeatureObservation_basis_normalized _
      (fun k => norm_standardizedFeatureVector v _
        (ha (localWeightActiveIndex n q δ t k)))]
    simp [activeBSPolynomial, activeBSCoefficient]
  rw [hsafeMeasure, hfun]
  exact (gaussianLogTruncationStatistic_activeBS_variance_eq
    r n q K hn δ t hδ hcard v a ha).symm

end Hurst
