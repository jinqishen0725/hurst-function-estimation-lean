import Hurst.HonestRateDrift
import Hurst.FullChainGeneralSigned
import Hurst.FeatureRowNondegenerate
import Hurst.KernelEnergyRateDischarge
import Hurst.FirstScaleLongRates
import Hurst.LocalWeightSupport
import Hurst.PackingAsymptotics

/-!
# The statistical-closure endpoint via the honest-rate drift (takeover10, task 3)

This is the FINAL ASSEMBLY of the drift route: the truth-centered full-chain
endpoint of `Hurst.FullChainGeneralSigned.actualQ1_knownScaleH_fullChain_generalSigned`
with the hBias premise (`|E Ĥ_n - f t| ≤ C n^(-(f t))`, refuted as
unsatisfiable at `γ = f t` under the long-memory band in
`Hurst.HBiasSecondOrder`) REPLACED by the honest-rate drift of task 2
(`seamScaleC · |E Ĥ_n - f t| → 0`, `honestRate_drift_tendsto_zero`), consumed
through the `p5_transport_truthCentered_of_drift` L1 channel (the integrand
difference is the constant `c n (E Ĥ_n - f t)`, so the L1 norm IS the scaled
drift — the FullChainGeneralSigned precedent, step 7).

The center is pinned internally at `cσ = gaussianLogSquareMean` (the
model-determined constant that kills the `1/log n` offset term of the E5
identity).  The final premise list is the model window (with the second-order
band `1/2 < a`), the b-band datum, and the polynomial order `r` — nothing
else.  The scalar rates (`hR`/`hcut`/`hEnv`) are instantiated internally at
`R n = ⌊n^β⌋₊` with the β-window midpoint (takeover7's zeroDoof pattern).

## Legacy honesty note

The old hBias-shaped endpoints
(`actualQ1_knownScaleH_fullChain_generalSigned_feasible`,
`…_feasible_centerBand`, `…_feasible_centerBand_zeroDof`) remain in the tree
unchanged; at `γ = f t` their hBias premise is vacuous on the regular model
class (only degenerate profiles satisfy it — hand-derived, see
`IncrementLogSecondOrder` module docs; the FORMAL refutation covers the
per-row log-route windows `bias_window_firstOrder_infeasible` /
`bias_window_secondOrder_infeasible`).  This endpoint is the honest
replacement: closure follows from the drift, not from a rate.
-/

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace Hurst

/-! ## Feasible-bandwidth window facts (replicated from FullChainGeneralSigned) -/

private theorem hrc_bandwidth_pos (γ : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) ^ (-γ)) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

private theorem hrc_bandwidth_tendsto (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ (-γ))) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop

private theorem hrc_mesh_tendsto_atTop (γ : ℝ) (hγ : 0 < γ) (hγlt : γ < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) * ((n : ℝ) ^ (-γ)))) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 - γ))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  refine Tendsto.congr' ?_ h1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring,
    Real.rpow_add hnR (1 : ℝ) (-γ), Real.rpow_one]

private theorem hrc_mesh_pos (γ : ℝ) :
    ∀ n : ℕ, 2 ≤ n → 0 < (n : ℝ) * ((n : ℝ) ^ (-γ)) := by
  intro n hn
  have h0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact mul_pos h0 (Real.rpow_pos_of_pos h0 _)

private theorem hrc_estimator_aemeasurable (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ) (n : ℕ)
    (h : ∀ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0) :
    AEMeasurable (p5KnownScaleEstimator f r n (δ n) t cσ)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
  have hG : AEMeasurable (p5KnownScaleLogStatistic f r n (δ n) t)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
    (gaussianLogStatistic_memLp_two (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
      (actualQ1Coeff n (δ n) t) h).aemeasurable
  exact p5Trunc01_continuous.measurable.comp_aemeasurable
    ((aemeasurable_const.sub hG).div_const (2 * Real.log n))

private theorem hrc_estimator_integrable (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ) (n : ℕ)
    (h : ∀ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0) :
    Integrable (p5KnownScaleEstimator f r n (δ n) t cσ)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
  refine Integrable.of_bound
    (hrc_estimator_aemeasurable f hf r t δ cσ n h).aestronglyMeasurable (1 : ℝ)
    (Eventually.of_forall fun x => ?_)
  have hb : p5KnownScaleEstimator f r n (δ n) t cσ x ∈ Set.Icc 0 1 :=
    p5Trunc01_mem_Icc (p5KnownScaleHtilde f r n (δ n) t cσ x)
  obtain ⟨h1, h2⟩ := hb
  exact abs_le.mpr ⟨by linarith, h2⟩

/-! ## The statistical-closure endpoint -/

/-- **The statistical-closure endpoint via the honest-rate drift.**  Under the
model window (with the second-order band `1/2 < a`), the b-band datum
`(1-f t)² < 1-b`, and the polynomial order `r`, the seam-scaled, truth-centered
known-scale H estimator at the pinned center `cσ = gaussianLogSquareMean`
converges in distribution to the reflection `-Q` of the CONSTRUCTED signed
weighted-Riesz second-chaos law:

`2 n^{ψ(1-f t)} log n · (Ĥ_n - f t) ⇒ -Q`,  `ψ = 2 - 2 f t`.

The `hane` row nondegeneracy, the center band, the scalar rates and the β
window are all discharged internally; the honest-rate drift of task 2 replaces
the (vacuous-at-`γ = f t`) hBias premise of the legacy endpoints. -/
theorem actualQ1_knownScaleH_fullChain_honestRate
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 1 / 2 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hbband : (1 - f t) ^ 2 < 1 - b) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      IsWeightedRieszSecondChaosLaw gaussianSeqMeasure Q (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r) ∧
      TendstoInDistribution
        (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
          seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean x
              - f t))
        atTop (fun ω => -Q ω)
        (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        gaussianSeqMeasure := by
  have hft : f t ∈ Ioo (0 : ℝ) 1 := hf.1 ht
  have hft1 : (f t : ℝ) < 1 := hft.2
  have hfb : f t < 1 := hft1
  have hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0 :=
    fun n k => actualQ1_hane_all f hf ((n : ℝ) ^ (-(f t))) t n k
  -- the bandwidth windows at γ = f t
  have hδpos := hrc_bandwidth_pos (f t)
  have hδ0 := hrc_bandwidth_tendsto (f t) hft.1
  have hN := hrc_mesh_tendsto_atTop (f t) hft.1 hft1
  have hSpos := hrc_mesh_pos (f t)
  -- 1. the quadratic side: the constructed signed law
  obtain ⟨Q, hLaw, hquad⟩ :=
    actualQ1LongStatistic_tendsto_secondChaos_generalSigned p a b M r hp
      (by linarith : 0 < a) hb hab hM f hf hF t ht hlong (f t) hft.1 hft1
      (by
        -- the grid window at γ = f t is the b-band datum
        have h2 : (1 - f t) * (2 - 2 * f t) = 2 * ((1 - f t) * (1 - f t)) := by ring
        have hbd : (1 - f t) * (1 - f t) < 1 - b := by simpa only [pow_two] using hbband
        rw [h2]; linarith)
      hane
  -- 2. the scalar rates instantiated at the β-window midpoint (zeroDoof pattern)
  have h4 : (0 : ℝ) < 4 * f t - 3 := by linarith
  set β : ℝ := (1 - f t) * (4 * f t - 3) / 2 with hβdef
  have hβ0 : (0 : ℝ) < β :=
    div_pos (mul_pos (sub_pos.mpr hft1) h4) (by norm_num)
  have hβ' : β < (1 - f t) * (1 - 2 * (2 - 2 * f t)) := by
    have hw : (1 - f t) * (4 * f t - 3) = (1 - f t) * (1 - 2 * (2 - 2 * f t)) := by ring
    rw [hβdef, hw]
    nlinarith [mul_pos (sub_pos.mpr hft1) h4]
  set R : ℕ → ℕ := fun n => (⌊(n : ℝ) ^ β⌋₊ : ℕ) with hRdef
  have hR := feasibleR_tendsto_atTop β hβ0
  have hcut := feasibleR_cut_tendsto f t (f t) β hft1 hβ0 hβ'
  have hgrid' : (1 - f t) * (2 - 2 * f t) < 2 - 2 * b := by
    have h2 : (1 - f t) * (2 - 2 * f t) = 2 * ((1 - f t) * (1 - f t)) := by ring
    have hbd : (1 - f t) * (1 - f t) < 1 - b := by simpa only [pow_two] using hbband
    rw [h2]; linarith
  have hEnv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0,
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n ((n : ℝ) ^ (-(f t)))
          ((n : ℝ) * ((n : ℝ) ^ (-(f t)))) (R n)) atTop (𝓝 0) :=
    fun Ccov _ Ctail _ L _ =>
      feasibleR_env_tendsto b Ccov Ctail L M (f t) (f t) β hft.1
        (by linarith : 0 < 2 - 2 * f t) (by linarith : 2 - 2 * f t < 1 / 2) hgrid' hβ0
  -- 3. the expectation-centered full chain at the pinned center (the E5 drift
  --    and hBias premises of the legacy endpoint are NOT consumed here; the
  --    seam side needs only the center band, discharged internally)
  have hband := centerBand_hband_discharged p a b M hp (by linarith : 0 < a) hb hab hM
    f hf hF r t ht (f t) gaussianLogSquareMean hft.1 hft1 hlong
  -- the legacy feasible endpoint is NOT consumed (its hBias premise at
  -- γ = f t is vacuous on the regular model class); instead the seam+join
  -- layers are consumed directly and the truth-centering runs on task 2's
  -- honest-rate drift through the E4 transport:
  have hFourth := gs_fourthEnergy_tendsto_zero p a b M hp (by linarith : 0 < a) hb hab hM
    f hf hF r t ht hlong (fun n => ((n : ℝ) ^ (-(f t)))) R hδpos hδ0 hN hR hcut hEnv
  have hL1 := actualQ1_logStatistic_tendsto_secondChaos_doubleSum f hf r t
    (fun n => ((n : ℝ) ^ (-(f t)))) ht gaussianSeqMeasure Q hane hquad hFourth
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L₀, hL₀, C₂, hC₂, hEnergy⟩ :=
    hurstHolder_q1_actual_normalized_energy_eventually_bounded
      p a b M hp (by linarith : 0 < a) hb hab hM f hf hF t ht hlong
  have hRn : ∀ᶠ n : ℕ in atTop, 1 ≤ R n := by
    filter_upwards [hR.eventually_ge_atTop 1] with n hn
    exact_mod_cast hn
  have hEcore := hEnergy (fun n => ((n : ℝ) ^ (-(f t)))) R hδpos hδ0 hN hRn hcut
    (hEnv Ccov hCcov Ctail hCtail L₀ hL₀)
  have hE : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * ((n : ℝ) ^ (-(f t)))) ^ (2 * (2 - 2 * f t) - 2) *
        (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
          ∑ k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
            (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
              (actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t j)
              (actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t k)) ^ 2) ≤ C₂ := by
    filter_upwards [hEcore, eventually_gt_atTop (0 : ℕ)] with n hEn hn
    have hsum : (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
          ∑ k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
            (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
              (actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t j)
              (actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t k)) ^ 2)
        = ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
            ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
              (vectorCorrelation
                (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-(f t))) t i))
                (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-(f t))) t j))) ^ 2 :=
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ =>
          congrArg (fun z => z ^ 2)
            (gridStrideFirst_correlation_identity n 1 hn (by norm_num)
              (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-(f t))) t i)
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-(f t))) t j))
    rw [hsum]
    exact hEn
  obtain ⟨U, hU, huW0⟩ := localPolynomialWeights_scaled_eventually_bounded
    r 1 t ht (fun n => ((n : ℝ) ^ (-(f t)))) hδpos hδ0 hN
  have huW : ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
      |actualQ1ChainWeight f r n ((n : ℝ) ^ (-(f t))) t j| ≤ U := by
    filter_upwards [huW0] with n hn
    intro j
    exact hn (localWeightActiveIndex n 1 ((n : ℝ) ^ (-(f t))) t j)
  have hJoin := gs_logProjection_L1_tendsto_instantiated f hf r t
    (fun n => ((n : ℝ) ^ (-(f t)))) hN hSpos hlong hfb hane C₂ U hU hE huW
    gaussianLogSquareMean ((1 - f t) / 2) (div_pos (by linarith) (by norm_num)) hband
  have hSeam := logStatistic_knownScaleH_seam_of_logLimit f hf r t
    (fun n => ((n : ℝ) ^ (-(f t)))) gaussianSeqMeasure Q hane hL1 gaussianLogSquareMean hJoin
  -- 4. the honest-rate drift (task 2) consumed through the E4 transport
  have hDrift := honestRate_drift_tendsto_zero p a b M hp ha hb hab hM f hf hF t ht
    hlong hbband r
  refine ⟨Q, hLaw, ?_⟩
  refine @p5_transport_truthCentered_of_drift
    (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    (fun n => featureGaussian_isProbability _) (ℕ → ℝ) _ gaussianSeqMeasure _ Q
    (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
      p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean x)
    (fun n => seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n) (f t) hSeam ?_ ?_ ?_
  · intro n
    exact ((hrc_estimator_aemeasurable f hf r t (fun n => ((n : ℝ) ^ (-(f t))))
      gaussianLogSquareMean n (hane n)).sub aemeasurable_const).const_mul _
  · refine Eventually.of_forall fun n => ?_
    have hEstInt := hrc_estimator_integrable f hf r t
      (fun n => ((n : ℝ) ^ (-(f t)))) gaussianLogSquareMean n (hane n)
    exact (((hEstInt.sub (integrable_const (f t))).const_mul _).sub
      ((hEstInt.sub (integrable_const _)).const_mul _))
  · have habscont : Continuous (fun z : ℝ => |z|) := by fun_prop
    have key : Tendsto (fun n : ℕ => |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
        ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|)
        atTop (𝓝 0) := hDrift
    have hint : ∀ n : ℕ, ∫ ω,
        |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean ω - f t)
          - seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean ω
              - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        = |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
            ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              - f t)| := by
      intro n
      have hpt : ∀ ω : EuclideanSpace ℝ (Fin n),
          |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
              (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean ω - f t)
            - seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean ω
                  - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
          = |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                - f t)| := fun ω => by
        rw [show seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
              (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean ω - f t)
              - seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean ω
                  - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
            = seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
                ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                    featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                  - f t) by ring]
      calc ∫ ω,
            |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean ω - f t)
              - seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean ω
                  - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
            ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          = ∫ ω, |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                - f t)|
            ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) :=
              integral_congr_ae (Eventually.of_forall hpt)
        _ = |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                - f t)| := by
              rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    refine Tendsto.congr (fun n => ?_) key
    rw [hint n]

end Hurst
