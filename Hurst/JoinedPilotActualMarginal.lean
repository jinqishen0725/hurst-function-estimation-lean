import Hurst.ActualShortMainline
import Hurst.ShortMemoryCLTApplicability

/-!
# Marginal one-scale pilot limits from the actual Bardet-Surgailis endpoints

Phase-1 scoping of the unknown-scale chain showed that the wired unknown-scale
main theorem chain consumes only MARGINAL one-scale distributional limits of
pilot statistics: the scale estimate is removed through the deterministic
`L1`-smallness premises `hurstHolder_q1_scale_L1_negligible` /
`hurstHolder_q2_scale_L1_negligible` inside
`boundedInverse_scale_distribution_transfer`, never through a joint CLT.

This module discharges the last remaining internal premise of that chain,
namely the per-truncation polynomial CLT premises `hpoly` of
`hurstHolder_q1_conditional_short_mainline` and
`hurstHolder_q2_conditional_short_mainline`, by instantiating them from the
exact external Bardet-Surgailis endpoints
`hurstHolder_stride_first_finiteHermite_CLT_actual` and
`hurstHolder_grid_second_finiteHermite_CLT_actual` together with the
internally proved truncated-variance limits
`hurstHolder_stride_first_full_truncatedVariance_tendsto` /
`hurstHolder_grid_second_full_truncatedVariance_tendsto` and their positivity
`firstIncrement_full_truncatedVariance_limit_pos` /
`secondIncrement_full_truncatedVariance_limit_pos`.

The assembled conclusions `hurstHolder_q1_unknown_short_mainline_actual` and
`hurstHolder_q2_unknown_short_mainline_actual` are the unknown-scale
short-memory mainlines with premises only

* the exact external Bardet-Surgailis theorem
  `BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0}`,
* ordinary model assumptions (Holder class, compact range, interior point,
  `ContDiffOn`, nonzero scale parameters of the bandwidth), and
* the deterministic limit `hV` of the Gaussian truncated-covariance lag
  series (an ordinary parameter assumption, not a convergence premise of any
  statistic).

No internal premise restates convergence of the estimator statistics.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Deterministic long-run variance of the `K`-truncated q = 1 stride-first
log statistic: the equivalent-kernel `L2` mass times the Gaussian
log-truncation covariance lag series of the first increment at `h`. -/
def strideFirstTruncatedSeries (r : ℕ) (h : ℝ) (K : ℕ) : ℝ :=
  (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
    ∑' l : ℕ, (if l = 0 then (1 : ℝ) else 2) *
      gaussianLogTruncationCovariance K (firstIncrementLagCorrelation h l)

/-- Deterministic long-run variance of the `K`-truncated q = 2 grid-second
log statistic. -/
def gridSecondTruncatedSeries (r : ℕ) (h : ℝ) (K : ℕ) : ℝ :=
  (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
    ∑' l : ℕ, (if l = 0 then (1 : ℝ) else 2) *
      gaussianLogTruncationCovariance K (secondIncrementLagCorrelation h l)

theorem strideFirstTruncatedSeries_eq_zero_of_le_two (r : ℕ) (h : ℝ) (K : ℕ)
    (hK : K ≤ 2) : strideFirstTruncatedSeries r h K = 0 := by
  unfold strideFirstTruncatedSeries
  have h0 : ∀ l : ℕ, (if l = 0 then (1 : ℝ) else 2) *
      gaussianLogTruncationCovariance K (firstIncrementLagCorrelation h l) = 0 := by
    intro l
    rw [gaussianLogTruncationCovariance_eq_zero_of_le_two K hK]
    split_ifs <;> ring
  rw [tsum_congr h0, tsum_zero, mul_zero]

theorem gridSecondTruncatedSeries_eq_zero_of_le_two (r : ℕ) (h : ℝ) (K : ℕ)
    (hK : K ≤ 2) : gridSecondTruncatedSeries r h K = 0 := by
  unfold gridSecondTruncatedSeries
  have h0 : ∀ l : ℕ, (if l = 0 then (1 : ℝ) else 2) *
      gaussianLogTruncationCovariance K (secondIncrementLagCorrelation h l) = 0 := by
    intro l
    rw [gaussianLogTruncationCovariance_eq_zero_of_le_two K hK]
    split_ifs <;> ring
  rw [tsum_congr h0, tsum_zero, mul_zero]

/-- **Marginal one-scale polynomial pilot limit, q = 1, optimal bandwidth.**
For every Hermite truncation order `k` the normalized truncated statistic
converges to `N(0, strideFirstTruncatedSeries r (f t) k)`.  The only
probabilistic premise is the exact external Bardet-Surgailis theorem; the
truncated-variance limits come from
`hurstHolder_stride_first_full_truncatedVariance_tendsto`. -/
theorem hurstHolder_stride_first_optimal_hpoly_actual
    (hBS : BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0})
    (a b M : ℝ) (r : ℕ)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass ((r : ℝ) + 1) M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ k : ℕ, TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        gaussianLogTruncationStatistic
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
          (gridStrideFirstCoefficients n 1) k x) atTop
      (fun z : ℝ => Real.sqrt (strideFirstTruncatedSeries r (f t) k) * z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1) := by
  classical
  obtain ⟨hδ, hδ0, hN, _, _⟩ := optimalLocalBandwidth_bias_conditions r b hb
  have hSsucc := optimalLocalEffectiveSize_succ_ratio_tendsto_one ((r : ℝ) + 1)
  have hp : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  intro k
  rcases Nat.lt_or_ge k 3 with hK | hK
  · -- the truncation polynomial vanishes below Hermite rank two
    have hstat : ∀ n : ℕ, gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
        (gridStrideFirstCoefficients n 1) k = fun _ => 0 :=
      fun n => gaussianLogTruncationStatistic_eq_zero_of_le_two _ _ _ k (by omega)
    rw [show (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        gaussianLogTruncationStatistic
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
          (gridStrideFirstCoefficients n 1) k x)
        = (fun (n : ℕ) (_ : EuclideanSpace ℝ (Fin n)) => (0 : ℝ)) from by
          funext n x
          rw [hstat n]
          simp,
      strideFirstTruncatedSeries_eq_zero_of_le_two r (f t) k (by omega)]
    exact tendstoInDistribution_const_zero _
  · exact hurstHolder_stride_first_finiteHermite_CLT_actual hBS ((r : ℝ) + 1) a b M r
      hp ha hb hab hM f hf hF t ht (optimalLocalBandwidth ((r : ℝ) + 1)) hδ hδ0 hN
      hSsucc k (strideFirstTruncatedSeries r (f t) k)
      (firstIncrement_full_truncatedVariance_limit_pos r k (f t) hK
        (lt_of_lt_of_le ha (hF ht).1) (lt_of_le_of_lt (hF ht).2 hb))
      (hurstHolder_stride_first_full_truncatedVariance_tendsto ((r : ℝ) + 1) a b M r k
        hp ha hb hab hM f hf hF t ht (optimalLocalBandwidth ((r : ℝ) + 1)) hδ hδ0 hN)

/-- **Marginal one-scale polynomial pilot limit, q = 2, optimal bandwidth.** -/
theorem hurstHolder_grid_second_optimal_hpoly_actual
    (hBS : BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0})
    (a b M : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass ((r : ℝ) + 1) M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ k : ℕ, TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        gaussianLogTruncationStatistic
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
          (gridSecondCoefficients n) k x) atTop
      (fun z : ℝ => Real.sqrt (gridSecondTruncatedSeries r (f t) k) * z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1) := by
  classical
  obtain ⟨hδ, hδ0, hN, _, _⟩ := optimalLocalBandwidth_bias_conditions r 0 (by norm_num)
  have hSsucc := optimalLocalEffectiveSize_succ_ratio_tendsto_one ((r : ℝ) + 1)
  have hp : (2 : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast (show 2 ≤ r + 1 by omega)
  intro k
  rcases Nat.lt_or_ge k 3 with hK | hK
  · have hstat : ∀ n : ℕ, gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
        (gridSecondCoefficients n) k = fun _ => 0 :=
      fun n => gaussianLogTruncationStatistic_eq_zero_of_le_two _ _ _ k (by omega)
    rw [show (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        gaussianLogTruncationStatistic
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
          (gridSecondCoefficients n) k x)
        = (fun (n : ℕ) (_ : EuclideanSpace ℝ (Fin n)) => (0 : ℝ)) from by
          funext n x
          rw [hstat n]
          simp,
      gridSecondTruncatedSeries_eq_zero_of_le_two r (f t) k (by omega)]
    exact tendstoInDistribution_const_zero _
  · exact hurstHolder_grid_second_finiteHermite_CLT_actual hBS ((r : ℝ) + 1) a b M r
      hp ha hb hab hM f hf hF t ht (optimalLocalBandwidth ((r : ℝ) + 1)) hδ hδ0 hN
      hSsucc k (gridSecondTruncatedSeries r (f t) k)
      (secondIncrement_full_truncatedVariance_limit_pos r k (f t) hK
        (lt_of_lt_of_le ha (hF ht).1) (lt_of_le_of_lt (hF ht).2 hb))
      (hurstHolder_grid_second_full_truncatedVariance_tendsto ((r : ℝ) + 1) a b M r k
        hp ha hb hab hM f hf hF t ht (optimalLocalBandwidth ((r : ℝ) + 1)) hδ hδ0 hN)

/-- **Unknown-scale q = 1 short-memory mainline, actual model.**  Both the
known-scale and the unknown-scale local estimators are asymptotically
normal at the bias-corrected rate; the only premises are the external
Bardet-Surgailis theorem, ordinary model assumptions, and the deterministic
limit of the truncated-covariance series. -/
theorem hurstHolder_q1_unknown_short_mainline_actual
    (hBS : BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0})
    (a b M : ℝ) (r : ℕ)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass ((r : ℝ) + 1) M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r + 1) f (Ioo (0 : ℝ) 1))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (V : ℝ)
    (hV : Tendsto (strideFirstTruncatedSeries r (f t)) atTop (𝓝 V)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n : ℝ)*optimalLocalBandwidth ((r : ℝ) + 1) n)*Real.log n*
      (q1LocalEstimator r n (optimalLocalBandwidth ((r : ℝ) + 1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r + 1) f t/((r + 1).factorial : ℝ))*equivalentKernelMoment r (r + 1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n : ℝ)*optimalLocalBandwidth ((r : ℝ) + 1) n)*Real.log n*
      (q1UnknownLocalEstimator r n (scaleAverageResolution ((r : ℝ) + 1) n) (optimalLocalBandwidth ((r : ℝ) + 1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r + 1) f t/((r + 1).factorial : ℝ))*equivalentKernelMoment r (r + 1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) :=
  hurstHolder_q1_conditional_short_mainline a b M r ha hb hab hM f hf hF hfc t ht V
    (strideFirstTruncatedSeries r (f t)) hV
    (hurstHolder_stride_first_optimal_hpoly_actual hBS a b M r ha hb hab hM f hf hF t ht)

/-- **Unknown-scale q = 2 short-memory mainline, actual model.** -/
theorem hurstHolder_q2_unknown_short_mainline_actual
    (hBS : BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0})
    (a b M : ℝ) (r : ℕ) (u : ℝ) (hr : 1 ≤ r) (hu : u < 1) (hbu : b < u)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass ((r : ℝ) + 1) M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r + 1) f (Ioo (0 : ℝ) 1))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (htu : f t < u)
    (V : ℝ)
    (hV : Tendsto (gridSecondTruncatedSeries r (f t)) atTop (𝓝 V)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n : ℝ)*optimalLocalBandwidth ((r : ℝ) + 1) n)*Real.log n*
      (q2LocalEstimator u r n (optimalLocalBandwidth ((r : ℝ) + 1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r + 1) f t/((r + 1).factorial : ℝ))*equivalentKernelMoment r (r + 1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n : ℝ)*optimalLocalBandwidth ((r : ℝ) + 1) n)*Real.log n*
      (q2UnknownLocalEstimator (a / 2) u r n (scaleAverageResolution ((r : ℝ) + 1) n) (optimalLocalBandwidth ((r : ℝ) + 1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r + 1) f t/((r + 1).factorial : ℝ))*equivalentKernelMoment r (r + 1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) :=
  hurstHolder_q2_conditional_short_mainline a b M r u hr hu hbu ha hb hab hM f hf hF
    hfc t ht htu V (gridSecondTruncatedSeries r (f t)) hV
    (hurstHolder_grid_second_optimal_hpoly_actual hBS a b M r hr ha hb hab hM f hf hF t ht)
    (hurstHolder_q2_scale_L1_negligible a b M r u hr ha hb hab hM hu hbu f hf hF)

end Hurst
