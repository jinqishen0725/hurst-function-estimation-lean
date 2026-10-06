import Hurst.P1ActualPowerSums
import Hurst.WeightedRieszSpectrumClosed
import Hurst.SignedPowerLimit
import Hurst.OptimalActiveRowDensity

/-!
# Actual q1 quadratic statistics with a constructed general signed limit

This composes P1's feasible-bandwidth power sums with the closed equivalent-
kernel spectrum and the general signed second-chaos limit. The spectrum and
limit random variable are constructed internally. Negative spectral mass need
not vanish; neither weights nor limiting eigenvalues are assumed nonnegative.

This is the quadratic-statistic endpoint, not the final H-estimator theorem.
The actual feature-row nondegeneracy premise `hane` remains explicit. Its
model-level discharge and the subsequent log-projection, estimator, and
truth-centering steps are separate obligations. No all-row nonemptiness
condition is used: the active cardinality tends to infinity by window geometry.
-/

set_option maxHeartbeats 2000000

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Real
open scoped Topology RealInnerProductSpace

namespace Hurst

private theorem signedClosed_delta_pos (γ : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

private theorem signedClosed_delta_tendsto (γ : ℝ) (hγ0 : 0 < γ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hγ0).comp tendsto_natCast_atTop_atTop

private theorem signedClosed_mesh_tendsto (γ : ℝ) (hγ1 : γ < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) - γ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 - γ by linarith)).comp
      tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring,
    Real.rpow_add hnR (1 : ℝ) (-γ), Real.rpow_one]

/-- Under the feasible window and explicit feature-row nondegeneracy, the
actual q1 quadratic statistic converges to a constructed signed weighted-Riesz
second-chaos law. All spectral and probability-law data are conclusions. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_generalSigned
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      IsWeightedRieszSecondChaosLaw gaussianSeqMeasure Q
        (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel r) ∧
      TendstoInDistribution
        (fun (n : ℕ) x => gaussianLogQuadraticStatistic
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
        atTop Q (fun n => featureGaussian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) gaussianSeqMeasure := by
  have hft1 : f t < 1 := lt_of_le_of_lt (hF ht).2 hb
  have hpsi0 : 0 < 2 - 2 * f t := by linarith
  have hpsi2 : 2 * (2 - 2 * f t) < 1 := by linarith
  have hc : 0 < f t * (2 * f t - 1) := mul_pos (by linarith) (by linarith)
  obtain ⟨ι, v, κ, B, lam, vec, MR, hMR, hbd,
    _hv, _he, _hcomplete, _hk0, _hksq, _hcompact, _hsym, _hmat,
    _hhs, _henum, _hmult, hs, hRiesz⟩ :=
    HS.exists_weightedRieszSpectrum_equiv_closed r hpsi0 hpsi2 hc
  have hSpec : IsWeightedRieszSpectrum (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel r) lam := ⟨hs, hRiesz⟩
  let m : ℕ → ℕ := fun n => (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card
  let row : ∀ n, Fin (m n) → ℝ := fun n =>
    (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues
  have hmtop : Tendsto m atTop atTop :=
    localWeightActiveSet_card_tendsto_atTop 1 t ht
      (fun n : ℕ => (n : ℝ) ^ (-γ)) (signedClosed_delta_pos γ)
      (signedClosed_delta_tendsto γ hγ0) (signedClosed_mesh_tendsto γ hγ1)
  have hPowers : ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i, row n i ^ k) atTop (𝓝 (∑' j, lam j ^ k)) := by
    intro k hk
    rw [(hRiesz k hk).tsum_eq]
    exact actualQ1_eigenPowerSums_feasible p a b M r hp ha hb hab hM f hf hF
      t ht hlong γ hγ0 hγ1 hgrid k hk
  obtain ⟨Q, hQ, hconv⟩ := exists_centeredSpectralSquares_limit_of_signed_powerSums
    m row lam hmtop hs hPowers
  refine ⟨Q, ⟨signedSortedSpectrum lam, hSpec.signedSorted, hQ⟩, ?_⟩
  refine tendstoInDistribution_of_identDistrib_rows_varying
    (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n)))) gaussianSeqMeasure
    (fun n => gaussianLogQuadraticStatistic
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)
      (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t))
    (fun n => centeredSpectralSquares (row n)) Q atTop ?_ hconv
  intro n
  simpa only [row, m, actualQ1Hermitian] using
    (gaussianLogQuadraticStatistic_identDistrib_eigenvalueSquares
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
      (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) (hane n))

end Hurst
