import Hurst.FeatureQuadraticSpectral
import Hurst.FiniteGaussianSpectralConvergence
import Hurst.DistributionVaryingLawTransfer

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Convergence criterion for actual finite feature-Gaussian quadratic
statistics, expressed only through deterministic spectral data of the
symmetric weighted covariance matrices. -/
theorem gaussianLogQuadraticStatistic_tendsto_secondChaos_of_spectral_data
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m d : ℕ → ℕ)
    (v : ∀ n, Fin (d n) → E)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ (Fin (d n)))
    (w : ∀ n, Fin (m n) → ℝ)
    (ha : ∀ n k, ∑ i, a n k i • v n i ≠ 0)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦
      let hA := weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)
      if hj : j < m n then hA.eigenvalues ⟨j, hj⟩ else 0)
      atTop (𝓝 (lambda j)))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (htail : ∀ K, ∀ᶠ n in atTop,
      let hA := weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)
      2 * (∑ i : Fin (m n),
        if K ≤ i.val then hA.eigenvalues i ^ 2 else 0) ≤ e K) :
    TendstoInDistribution
      (fun n ↦ gaussianLogQuadraticStatistic (v n) (w n) (a n))
      atTop Q (fun n ↦ featureGaussian (v n)) P' := by
  let A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ := fun n ↦
    weightedFeatureQuadraticMatrix (v n) (a n) (w n)
  let hA : ∀ n, (A n).IsHermitian := fun n ↦
    weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)
  have hmatrix := centeredMatrixQuadratic_tendsto_secondChaos_of_spectral_data
    m A hA P' Q lambda hQ hm (by
      intro j
      simpa only [A, hA] using hcoeff j) e he (by
      intro K
      simpa only [A, hA] using htail K)
  apply tendstoInDistribution_of_identDistrib_rows_varying
    (fun n ↦ featureGaussian (v n))
    (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
    (fun n ↦ gaussianLogQuadraticStatistic (v n) (w n) (a n))
    (fun n ↦ centeredMatrixQuadratic (A n)) Q atTop
  · intro n
    exact (gaussianLogQuadraticStatistic_identDistrib_normalizedCoordinates
      (v n) (a n) (w n)).trans
        (centeredSpectralSquares_featureGaussian_identDistrib_centeredMatrixQuadratic
          (v n) (a n) (w n) (ha n))
  · exact hmatrix

end Hurst
