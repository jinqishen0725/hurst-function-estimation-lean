import Hurst.ExternalSecondChaosLimit
import Hurst.ActualFirstLongHilbertSchmidtClosed
import Hurst.ActiveWeightProfile
import Hurst.FirstStrideMean

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Conditional endpoint for the actual q=1 local quadratic statistic.
The correlation kernel, active-window geometry, weight profile, and exact
statistic reindexing are verified here.  The premise
`WeightedGaussianQuadraticSecondChaosConvergence` is currently an explicit
model-independent internal proof target; it is not claimed to be the verbatim
statement of a published theorem. -/
theorem hurstHolder_q1_actual_quadratic_secondChaos
    (hSecondChaos : WeightedGaussianQuadraticSecondChaosConvergence)
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
        (fun (n : ℕ) => featureGaussian
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hkernel⟩ :=
    hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz_closed
      p a b M hp ha hb hab hM f hf hF t ht hlong
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, ?_⟩
  intro δ R hδpos hδ0 hS hR hcut henv P' _ hQ
  let m := fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card
  let v := fun n : ℕ => gridObservationFeatures n
    (midpointSampleHurst f hf.1 n)
  let coeff := fun n : ℕ => fun i : Fin (m n) =>
    gridDifferenceCoefficients n
      (localWeightActiveIndex n 1 (δ n) t i)
  let w := fun n : ℕ => fun i : Fin (m n) =>
    localPolynomialWeights r n 1 (δ n) t
      (localWeightActiveIndex n 1 (δ n) t i)
  let S := fun n : ℕ => (n : ℝ) * δ n
  let psi := 2 - 2 * f t
  let c := f t * (2 * f t - 1)
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
      ∑ j, coeff n i j • v n j ≠ 0 := by
    filter_upwards [hnonzero] with n hn
    intro i
    simpa only [coeff, v,
      show gridStrideFirstCoefficients n 1 = gridDifferenceCoefficients n from rfl]
      using (hn f hf hF (localWeightActiveIndex n 1 (δ n) t i)).1
  have hactualKernel := hkernel δ R hδpos hδ0 hS hR hcut henv
  have hkernel' : Tendsto (fun n : ℕ =>
      realScaleMeshEnergy (S n) (fun i j =>
        S n ^ psi * featureCorrelation (v n) (coeff n i) (coeff n j) -
          rankRieszKernel (S n) psi c i j)) atTop (𝓝 0) := by
    apply hactualKernel.congr'
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
    have hentry :
        S n ^ psi * featureCorrelation (v n) (coeff n i) (coeff n j) -
            rankRieszKernel (S n) psi c i j =
          q1ActualLongActiveKernel f hf n (δ n) t (S n) psi i j -
            q1RieszActiveKernel n (δ n) t (S n) psi c i j := by
      rw [hriesz]
      unfold q1ActualLongActiveKernel
      simpa only [v, coeff,
        show gridDifferenceCoefficients n = gridStrideFirstCoefficients n 1 from rfl]
        using congrArg (fun z : ℝ => z - rankRieszKernel (S n) psi c i j)
          (congrArg (fun z : ℝ => S n ^ psi * z) hcorr)
    exact hentry.symm
  have hweight : ∀ eps > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n),
      |S n * w n i -
        equivalentKernel r
          (2 * (((i.val + 1 : ℕ) : ℝ) / (m n : ℝ)) - 1)| ≤ eps := by
    intro eps heps
    simpa only [m, S, w] using
      (localPolynomialWeights_active_rank_uniform_tendsto
        r 1 t ht δ hδpos hδ0 hS eps heps)
  have hlimit := hSecondChaos m v coeff S psi c w (equivalentKernel r)
    P' hpsi0 hpsihalf hSpos hS hratio hfeature hkernel' hweight
    (by simpa only [psi, c] using hQ)
  refine TendstoInDistribution.congr (fun n => ?_)
    (Filter.EventuallyEq.refl _ _) hlimit
  filter_upwards [] with x
  rw [q1_actual_quadraticStatistic_active r n (δ n) t
    (midpointSampleHurst f hf.1 n) x]

end Hurst
