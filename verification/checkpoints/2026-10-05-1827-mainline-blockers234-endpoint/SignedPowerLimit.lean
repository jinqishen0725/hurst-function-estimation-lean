import Hurst.GeneralSignedPowerMatching
import Hurst.SignedInterleavedLaw
import Hurst.P4GaussianSeriesLaw

/-!
# General signed power sums give a constructed second-chaos limit

The target order is constructed by separately sorting positive and negative
coefficients. Its signed power sums agree with the supplied spectrum. Finite
rows retain their original order and their original Gaussian probability space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem IsWeightedRieszSpectrum.signedSorted {psi c : ℝ} {omega : ℝ → ℝ}
    {lam : ℕ → ℝ} (h : IsWeightedRieszSpectrum psi c omega lam) :
    IsWeightedRieszSpectrum psi c omega (signedSortedSpectrum lam) := by
  refine ⟨(signedSortedSpectrum_hasSum_sq h.1).summable, ?_⟩
  intro k hk
  simpa only [(h.2 k hk).tsum_eq] using signedSortedSpectrum_hasSum_pow h.1 hk

theorem centeredSpectralSquares_tendsto_of_signed_powerSums
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k)))
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (hQ : IsSecondChaosSeriesLaw P' Q (signedSortedSpectrum lam)) :
    TendstoInDistribution (fun n => centeredSpectralSquares (a n)) atTop Q
      (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  exact tendstoInDistribution_of_identDistrib_rows_varying
    (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n))))
    (fun n => stdGaussian (EuclideanSpace ℝ (Fin (2 * m n)))) P'
    (fun n => centeredSpectralSquares (a n))
    (fun n => centeredSpectralSquares (signedInterleavedRow (a n))) Q atTop
    (fun n => (signedInterleavedRow_identDistrib (a n)).symm)
    (signedInterleavedRow_tendsto_secondChaos_of_powerSums m a lam hmtop hs hp P' Q hQ)

/-- No target random variable or matching data are supplied by the caller. -/
theorem exists_centeredSpectralSquares_limit_of_signed_powerSums
    (m : ℕ → ℕ) (a : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hmtop : Tendsto m atTop atTop)
    (hs : Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, a n i ^ k) atTop (𝓝 (∑' j, lam j ^ k))) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      IsSecondChaosSeriesLaw gaussianSeqMeasure Q (signedSortedSpectrum lam) ∧
      TendstoInDistribution (fun n => centeredSpectralSquares (a n)) atTop Q
        (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n)))) gaussianSeqMeasure := by
  obtain ⟨Q, hQ⟩ := exists_isSecondChaosSeriesLaw_gaussSeq (signedSortedSpectrum lam)
    (signedSortedSpectrum_hasSum_sq hs).summable
  exact ⟨Q, hQ, centeredSpectralSquares_tendsto_of_signed_powerSums
    m a lam hmtop hs hp gaussianSeqMeasure Q hQ⟩

end Hurst
