import Hurst.SpectralMatchingSort
import Hurst.SpectralMatchingTail
import Hurst.FiniteSpectralArrayConvergence
import Hurst.ExternalSecondChaosLimit
import Hurst.FeatureQuadraticSpectral

/-!
# Deterministic supply-side interface for the permuted spectral-data theorem

This file packages the deterministic supply side that feeds
`centeredMatrixQuadratic_tendsto_secondChaos_of_permuted_spectral_data`:

* the canonical decreasing permutation `decreasingSpectralPerm` from
  `Hurst/SpectralMatchingSort.lean` supplies the rowwise permutations;
* `spectralTailBound_of_padded_coefficient_convergence` from
  `Hurst/SpectralMatchingTail.lean` shows the uniform `ℓ²` tail hypothesis is
  a consequence of padded coefficient convergence plus convergence of the
  eigenvalue-square sum (the trace of the square), so it is not an
  independent input;
* the remaining genuinely open deterministic input is spectral matching: that
  the decreasingly rearranged eigenvalues of the actual matrix array converge
  coefficientwise to a fixed square-summable sequence.  It enters here only
  through the hypothesis `hcoeff` and through the named target
  `WeightedKernelSpectralOrderingInput`.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Everything downstream of an explicit eigenvalue ordering theorem: given
that the *canonically decreasingly permuted* eigenvalues of a Hermitian array
converge coefficientwise to a square-summable sequence realizing the stated
second-chaos law, and that the eigenvalue-square sums converge to the series,
the centered matrix quadratics converge in distribution. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching
    (m : ℕ → ℕ) (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then
        (hA n).eigenvalues
          ((decreasingSpectralPerm (hA n).eigenvalues) ⟨j, hj⟩) else 0)
      atTop (𝓝 (lambda j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), (hA n).eigenvalues i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lambda j ^ 2))) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  have htr2perm : Tendsto (fun n ↦ ∑ i : Fin (m n),
      (hA n).eigenvalues ((decreasingSpectralPerm (hA n).eigenvalues) i) ^ 2)
    atTop (𝓝 (∑' j : ℕ, lambda j ^ 2)) := by
    refine Tendsto.congr (fun n => ?_) htr2
    exact (Equiv.sum_comp (decreasingSpectralPerm (hA n).eigenvalues)
      (fun i => (hA n).eigenvalues i ^ 2)).symm
  obtain ⟨e, he, htail⟩ := spectralTailBound_of_padded_coefficient_convergence m
    (fun n i => (hA n).eigenvalues ((decreasingSpectralPerm (hA n).eigenvalues) i))
    lambda hQ.2.1 hm hcoeff htr2perm
  exact centeredMatrixQuadratic_tendsto_secondChaos_of_permuted_spectral_data
    m A hA (fun n => decreasingSpectralPerm (hA n).eigenvalues) P' Q lambda hQ hm
    hcoeff e he htail

/-- Ordering theorems are often stated through some permutation with an
antitone rearrangement.  This version accepts any such data and transports it
to the canonical decreasing permutation via the uniqueness of the decreasing
rearrangement. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_antitone_matching
    (m : ℕ → ℕ) (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (g : ∀ n, Fin (m n) → ℝ) (hg : ∀ n, Antitone (g n))
    (tau : ∀ n, Equiv.Perm (Fin (m n)))
    (hgval : ∀ (n : ℕ) (i : Fin (m n)), g n i = (hA n).eigenvalues (tau n i))
    (hgcoeff : ∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then g n ⟨j, hj⟩ else 0)
      atTop (𝓝 (lambda j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), (hA n).eigenvalues i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lambda j ^ 2))) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  have hcoeff : ∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then
      (hA n).eigenvalues
        ((decreasingSpectralPerm (hA n).eigenvalues) ⟨j, hj⟩) else 0)
    atTop (𝓝 (lambda j)) := by
    intro j
    have heq : (fun n ↦ if hj : j < m n then
        (hA n).eigenvalues
          ((decreasingSpectralPerm (hA n).eigenvalues) ⟨j, hj⟩) else 0)
        = (fun n ↦ if hj : j < m n then g n ⟨j, hj⟩ else 0) := by
      funext n
      by_cases hj : j < m n
      · rw [dif_pos hj, dif_pos hj,
          eq_decreasingSpectralPerm_of_antitone_rearrangement (hg n) (tau n)
            (hgval n) ⟨j, hj⟩]
      · rw [dif_neg hj, dif_neg hj]
    rw [heq]
    exact hgcoeff j
  exact centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching
    m A hA P' Q lambda hQ hm hcoeff htr2

/-- The trace-square hypothesis may be stated as the trace of the square. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching_trace
    (m : ℕ → ℕ) (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then
        (hA n).eigenvalues
          ((decreasingSpectralPerm (hA n).eigenvalues) ⟨j, hj⟩) else 0)
      atTop (𝓝 (lambda j)))
    (htr2 : Tendsto (fun n ↦ ((A n) * (A n)).trace)
      atTop (𝓝 (∑' j : ℕ, lambda j ^ 2))) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  refine centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching
    m A hA P' Q lambda hQ hm hcoeff ?_
  refine Tendsto.congr (fun n => ?_) htr2
  exact hermitian_trace_square_eq_sum_eigenvalues_sq (hA n)

/-- The named deterministic target that remains open on the actual-model
side: for every Hermitian array of the intended shape, the canonically
decreasingly permuted eigenvalues converge coefficientwise to the fixed
square-summable sequence `lambda`, and the eigenvalue-square sums converge to
the series.  Together with a second-chaos law for `lambda` this is exactly
what the previous theorem consumes. -/
def WeightedKernelSpectralOrderingInput (lambda : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ → ℕ) (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian),
    (∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then
        (hA n).eigenvalues
          ((decreasingSpectralPerm (hA n).eigenvalues) ⟨j, hj⟩) else 0)
      atTop (𝓝 (lambda j))) ∧
    Tendsto (fun n ↦ ∑ i : Fin (m n), (hA n).eigenvalues i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lambda j ^ 2))

/-- The packaged reduction from the ordering target to the second-chaos
endpoint. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_spectral_ordering_input
    {lambda : ℕ → ℝ} (hInput : WeightedKernelSpectralOrderingInput lambda)
    (m : ℕ → ℕ) (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' :=
  centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching m A hA P'
    Q lambda hQ hm (hInput m A hA).1 (hInput m A hA).2

section WeightedFeature

variable {iota kappa E : Type*} [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The eigenvalue-square sum of the symmetric weighted covariance matrix is
exactly the signed weighted correlation energy.  This is the form in which the
trace-square hypothesis must be supplied by the actual weighted-kernel
convergence. -/
theorem weightedFeatureQuadraticMatrix_sum_eigenvalues_sq
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota) (w : kappa → ℝ) :
    (∑ i : kappa,
        (weightedFeatureQuadraticMatrix_isHermitian v a w).eigenvalues i ^ 2)
      = ∑ i : kappa, ∑ j : kappa,
          w i * w j * (featureCorrelation v (a i) (a j)) ^ 2 := by
  rw [← hermitian_trace_square_eq_sum_eigenvalues_sq
    (weightedFeatureQuadraticMatrix_isHermitian v a w)]
  exact weightedFeatureQuadraticMatrix_trace_square v a w

/-- The actual-statistic interface: for weighted feature quadratic statistics
whose symmetric weighted covariance matrices satisfy the decreasing matching
and trace-square inputs, the statistics converge in distribution to the
second-chaos law.  The weights may absorb any deterministic normalization
(for example a factor `S ^ (psi - 1)`) by scaling `w` itself, since
`weightedFeatureQuadraticMatrix` is linear in `w`. -/
theorem gaussianLogQuadraticStatistic_tendsto_secondChaos_of_decreasing_matching
    (m : ℕ → ℕ)
    (v : ℕ → iota → E) (w : ∀ n, Fin (m n) → ℝ)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    (ha : ∀ (n : ℕ) (k : Fin (m n)), ∑ i, a n k i • v n i ≠ 0)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then
        (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues
          ((decreasingSpectralPerm
            (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues)
          ⟨j, hj⟩) else 0)
      atTop (𝓝 (lambda j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), ∑ j : Fin (m n),
        w n i * w n j * (featureCorrelation (v n) (a n i) (a n j)) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lambda j ^ 2))) :
    TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogQuadraticStatistic (v n) (w n) (a n) x)
      atTop Q (fun n => featureGaussian (v n)) P' := by
  have hA : ∀ n, (weightedFeatureQuadraticMatrix (v n) (a n) (w n)).IsHermitian :=
    fun n => weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)
  have htr2' : Tendsto (fun n ↦ ∑ i : Fin (m n),
      (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lambda j ^ 2)) := by
    refine Tendsto.congr (fun n => ?_) htr2
    exact (weightedFeatureQuadraticMatrix_sum_eigenvalues_sq (v n) (a n) (w n)).symm
  refine tendstoInDistribution_of_identDistrib_rows_varying
    (fun n => featureGaussian (v n))
    (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
    (fun n x => gaussianLogQuadraticStatistic (v n) (w n) (a n) x)
    (fun n => centeredMatrixQuadratic (weightedFeatureQuadraticMatrix (v n) (a n) (w n)))
    Q atTop ?_
    (centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching m
      (fun n => weightedFeatureQuadraticMatrix (v n) (a n) (w n))
      hA P' Q lambda hQ hm hcoeff htr2')
  intro n
  exact (gaussianLogQuadraticStatistic_identDistrib_normalizedCoordinates
      (v n) (a n) (w n)).trans
    (centeredSpectralSquares_featureGaussian_identDistrib_centeredMatrixQuadratic
      (v n) (a n) (w n) (ha n))

end WeightedFeature

end Hurst
