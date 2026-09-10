import Hurst.SecondChaosWeightedKernelTarget
import Hurst.ActualFirstLongWeightedKernel
import Hurst.ActualFirstLongQuadraticReindex
import Hurst.FirstStrideMean
import Hurst.DistributionEventualTransfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Conditional actual q=1 second-chaos endpoint after the complete
model-specific weighted-kernel reduction.  Its only premise is the explicitly
marked generic probability target `GaussianQuadraticWeightedKernelContinuity`.
No article-specific covariance, window, weight, or reindexing assertion remains
inside that target. -/
theorem hurstHolder_q1_actual_quadratic_secondChaos_of_weighted_kernel
    (hSecondChaos : GaussianQuadraticWeightedKernelContinuity)
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t) :
    ∃ Ccov ≥ 0, ∃ Ctail ≥ 0, ∃ L > 0,
      ∀ (δ : ℕ → ℝ) (R : ℕ → ℕ),
      (∀ᶠ n in atTop, 0 < δ n) →
      Tendsto δ atTop (𝓝 0) →
      Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop →
      (∀ᶠ n in atTop, 1 ≤ R n) →
      Tendsto (fun n : ℕ =>
        ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
          ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          (2 * (R n : ℝ) + 1)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n) (R n)) atTop (𝓝 0) →
      ∀ (P' : Measure ℝ) [IsProbabilityMeasure P'],
      IsWeightedRieszSecondChaosLaw P' id (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r) →
      TendstoInDistribution (fun (n : ℕ) x =>
        ((n : ℝ) * δ n) ^ (2 - 2 * f t) *
          gaussianLogQuadraticStatistic
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
            (localPolynomialWeights r n 1 (δ n) t)
            (gridDifferenceCoefficients n) x)
        atTop id
        (fun n : ℕ => featureGaussian
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hweighted⟩ :=
    hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz
      p a b M r hp ha hb hab hM f hf hF t ht hlong
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, ?_⟩
  intro δ R hδpos hδ0 hS hR hcut henv P' _ hQ
  let m := fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card
  let obs := fun n : ℕ => gridObservationFeatures n
    (midpointSampleHurst f hf.1 n)
  let coeff := fun n : ℕ => fun i : Fin (m n) =>
    gridDifferenceCoefficients n
      (localWeightActiveIndex n 1 (δ n) t i)
  let S := fun n : ℕ => (n : ℝ) * δ n
  let psi := 2 - 2 * f t
  let c := f t * (2 * f t - 1)
  let u := fun n : ℕ => fun i : Fin (m n) =>
    S n * localPolynomialWeights r n 1 (δ n) t
      (localWeightActiveIndex n 1 (δ n) t i)
  have hpsi0 : 0 < psi := by
    dsimp only [psi]
    have hft : f t < 1 := (hF ht).2.trans_lt hb
    linarith
  have hpsihalf : psi < 1 / 2 := by
    dsimp only [psi]
    linarith
  have hSpos : ∀ᶠ n in atTop, 0 < S n := hS.eventually_gt_atTop 0
  have hratio : Tendsto (fun n : ℕ => (m n : ℝ) / S n)
      atTop (𝓝 2) := by
    simpa only [m, S] using
      (localWeightActiveSet_card_ratio_tendsto_two
        1 t ht δ hδpos hδ0 hS).2
  obtain ⟨_Cmean, _hCmean, hnonzero⟩ :=
    hurstHolder_stride_first_log_mean
      p a b M hp ha hb hab hM 1 (by norm_num)
  have hfeature : ∀ᶠ n in atTop, ∀ i : Fin (m n),
      ∑ j, coeff n i j • obs n j ≠ 0 := by
    filter_upwards [hnonzero] with n hn
    intro i
    simpa only [coeff, obs,
      show gridStrideFirstCoefficients n 1 = gridDifferenceCoefficients n from rfl]
      using (hn f hf hF (localWeightActiveIndex n 1 (δ n) t i)).1
  have hmodel := hweighted δ R hδpos hδ0 hS hR hcut henv
  have hkernel : Tendsto (fun n : ℕ =>
      realScaleMeshEnergy (S n) (fun i j =>
        u n i * (S n ^ psi *
          featureCorrelation (obs n) (coeff n i) (coeff n j)) -
        equivalentKernel r
          (2 * (((i.val + 1 : ℕ) : ℝ) / (m n : ℝ)) - 1) *
          rankRieszKernel (S n) psi c i j)) atTop (𝓝 0) := by
    apply hmodel.congr'
    filter_upwards [eventually_gt_atTop 0, hδpos, hSpos,
      (localWeightActiveSet_card_ratio_tendsto_two
        1 t ht δ hδpos hδ0 hS).1] with n hn hδn hSn hcard
    apply congrArg (realScaleMeshEnergy (S n))
    funext i j
    have hcorr := gridStrideFirst_correlation_identity n 1 hn (by norm_num)
      (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 (δ n) t i)
      (localWeightActiveIndex n 1 (δ n) t j)
    have hriesz := q1RieszActiveKernel_eq_rankRieszKernel
      n hn (δ n) t (S n) psi c hδn hSn hcard
    rw [hriesz]
    unfold q1ActualLongActiveKernel
    simpa only [m, S, psi, c, u, obs, coeff,
      show gridDifferenceCoefficients n = gridStrideFirstCoefficients n 1 from rfl]
      using (congrArg (fun z : ℝ =>
        (S n * localPolynomialWeights r n 1 (δ n) t
          (localWeightActiveIndex n 1 (δ n) t i)) *
          (S n ^ psi * z) -
        equivalentKernel r
          (2 * (((i.val + 1 : ℕ) : ℝ) / (m n : ℝ)) - 1) *
          rankRieszKernel (S n) psi c i j) hcorr).symm
  have hlimit := hSecondChaos m obs coeff S psi c u (equivalentKernel r)
    P' hpsi0 hpsihalf hSpos hS hratio hfeature hkernel
    (by simpa only [psi, c] using hQ)
  let X := fun n : ℕ => fun x => S n ^ (psi - 1) * ∑ i,
    u n i * ((standardizedFeatureObservation (obs n) (coeff n i) x) ^ 2 - 1)
  let Y := fun n : ℕ => fun x => S n ^ psi *
    gaussianLogQuadraticStatistic (obs n)
      (localPolynomialWeights r n 1 (δ n) t)
      (gridDifferenceCoefficients n) x
  have hYmeas : ∀ n, AEMeasurable (Y n) (featureGaussian (obs n)) := by
    intro n
    exact (gaussianLogQuadraticStatistic_memLp_two (obs n)
      (localPolynomialWeights r n 1 (δ n) t)
      (gridDifferenceCoefficients n)).aemeasurable.const_mul _
  have hXY : ∀ᶠ n in atTop,
      X n =ᵐ[featureGaussian (obs n)] Y n := by
    filter_upwards [hSpos] with n hSn
    filter_upwards [] with x
    dsimp only [X, Y, obs]
    rw [q1_actual_quadraticStatistic_active r n (δ n) t
      (midpointSampleHurst f hf.1 n) x]
    have hpow : S n ^ (psi - 1) * S n = S n ^ psi := by
      conv_lhs => rhs; rw [← Real.rpow_one (S n)]
      rw [← Real.rpow_add hSn]
      congr 1
      ring
    dsimp only [u, coeff]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hpow]
    ring
  apply tendstoInDistribution_congr_eventually
    (fun n => featureGaussian (obs n)) P' X Y id atTop hYmeas hXY
  simpa only [X] using hlimit

end Hurst
