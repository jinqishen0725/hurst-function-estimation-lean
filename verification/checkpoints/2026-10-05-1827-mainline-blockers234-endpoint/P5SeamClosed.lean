import Hurst.P5LogHLayers

/-!
# P5 seam closed: Layer1 (log statistic) → Layer2 (known-scale H), conditionally

This file closes the Layer1 → Layer2 seam of `Hurst.P5LogHLayers` CONDITIONALLY
on the L1 joining lemma (proved in parallel in `Hurst.P5L1Joining`, taken here
as the explicit hypothesis `hJoin` in the EXACT shape of the `hL1` contract
consumed by `p5_transport_expectationCentered`):

`hJoin : Tendsto (fun n => ∫ ω, |c n * (Ĥ_n ω - E Ĥ_n) - -(Ĝ_spec n ω - E Ĝ_spec n)|
  ∂Pn n) atTop (𝓝 0)`

with the concrete chain objects

* `Pn n = featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))`
  (the D3 observation measure),
* `Ĝ_spec n = gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
  (actualQ1Coeff n (δ n) t)` (the Layer-1 D3 limit object, spectral weights
  `S^{ψ-1} u_i`, `S = n δ n`, `ψ = 2 - 2 f t`),
* `Ĥ_n = p5KnownScaleEstimator f r n (δ n) t cσ` (the clipped known-scale
  estimator; its inner log statistic `p5KnownScaleLogStatistic` carries the
  unit-sum weights `S⁻¹ u_i`),
* `c n = 2 S^ψ log n` (`seamScaleC`).

## The scale bridge (why the two weightings meet)

`gaussianLogStatistic` is LINEAR in the weight vector, and `S⁻¹ u_i =
S^(-ψ) (S^{ψ-1} u_i)` for `S > 0` (`p5Seam_unitWeight_eq`), so pointwise
`Ĝ_unit = S^(-ψ) Ĝ_spec`.  Hence the scaled centered untruncated deviation
satisfies the exact center identity (`p5Seam_center_identity`,
`p5Seam_joinBridge_mean`)

`2 S^ψ log n (H̃ - E H̃) = -(Ĝ_spec - EĜ_spec)`,  `H̃ = (cσ - Ĝ_unit)/(2 log n)`,

which converts the joining-lemma output shape (the clipped-vs-unclipped
projection gap for one and the same log statistic, as documented in
`Hurst.P5L1Joining.logProjection_L1_tendsto_zero`) into the transport-consumable
`hJoin` shape above — see `p5Seam_joinBridge`.

## Main statements

* `logStatistic_knownScaleH_seam` — the expectation-centered known-scale H
  layer: `c n (Ĥ_n - E Ĥ_n) ⇒ -Q` from (i) Layer 1's quadratic→log conclusion
  (D3 signature verbatim), (ii) `hJoin`, (iii) Layer 2's transport contract
  `p5_transport_expectationCentered` (its measurability and integrability side
  contracts are discharged here).
* `logStatistic_knownScaleH_seam_truthCentered` — the truth-centered variant:
  under the E5 bias condition `(1 - γ) ψ < γ s` with the conservative `s = 1`
  (`hE5`, `γ = f t`, `ψ = 2 - 2 f t`) whose drift smallness is kept explicit as
  `hDrift : c n (E Ĥ_n - f t) → 0`, one gets `c n (Ĥ_n - f t) ⇒ -Q`.
* `p5Seam_joinBridge` — converts the parallel joining lemma's output shape
  into the `hJoin` shape, from `Hurst.P5LogHLayers` lemmas alone.

Repair status (2026-09-26): row nonemptiness is derived eventually by the
CapstoneV2 quadratic endpoint; no hypothesis requires every finite row to be
nonempty.  The old unnormalized `hE2` and vanishing-negative-mass assumptions
remain explicit pending separate repairs.  Removing `hm` alone does not make
this a fully instantiated endpoint for the actual model.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## Scale algebra for the two weightings -/

/-- `gaussianLogStatistic` is linear in the weight vector. -/
theorem gaussianLogStatistic_const_weight_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ℝ) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) :
    gaussianLogStatistic (fun i => c * w i) a x = c * gaussianLogStatistic w a x := by
  unfold gaussianLogStatistic
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The unit-sum chain weight is the spectral weight rescaled by `S ^ (-ψ)`:
`S⁻¹ u = S^(-ψ) (S^{ψ-1} u)` for `S > 0`. -/
theorem p5Seam_unitWeight_eq (S u ψ : ℝ) (hS : 0 < S) :
    S⁻¹ * u = S ^ (-ψ) * (S ^ (ψ - 1) * u) := by
  rw [← mul_assoc, ← Real.rpow_add hS (-ψ) (ψ - 1),
    show (-ψ : ℝ) + (ψ - 1) = -1 by ring, Real.rpow_neg_one]

/-- The seam center identity: with `Ĝ_unit = S^(-ψ) Ĝ_spec` pointwise, the
scaled centered untruncated-H deviation equals the negated centered spectral
log statistic (the `p5_YX_identity` of `Hurst.P5LogHLayers`, unpacked). -/
private theorem p5Seam_center_identity (S ψ L g m cσ : ℝ) (hS : 0 < S) (hL : L ≠ 0) :
    2 * S ^ ψ * L * ((cσ - S ^ (-ψ) * g) / (2 * L)
      - (cσ - S ^ (-ψ) * m) / (2 * L)) = -(g - m) := by
  have hcancel : S ^ ψ * S ^ (-ψ) = 1 := by
    rw [← Real.rpow_add hS ψ (-ψ), show ψ + -ψ = (0 : ℝ) by ring, Real.rpow_zero]
  have hB : (cσ - S ^ (-ψ) * g) / (2 * L) - (cσ - S ^ (-ψ) * m) / (2 * L)
      = (S ^ (-ψ) * (m - g)) / (2 * L) := by ring
  have h2L : 2 * L ≠ 0 := fun h => hL (by linarith)
  have hmul : 2 * S ^ ψ * L * ((S ^ (-ψ) * (m - g)) / (2 * L))
      = S ^ ψ * (S ^ (-ψ) * (m - g)) := by
    field_simp
  rw [hB, hmul, ← mul_assoc, hcancel, one_mul]
  ring

/-! ## The chain objects of the seam -/

/-- The seam scale `c n = 2 S^ψ log n` with `S = n δ n` and `ψ = 2 - 2 f t`. -/
def seamScaleC (f : ℝ → ℝ) (t : ℝ) (δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * ((n : ℝ) * δ n) ^ (2 - 2 * f t) * Real.log n

/-- The clip is continuous (the P5L1Joining `p5Trunc01_continuous`, replicated
locally to keep this file depending only on `Hurst.P5LogHLayers`). -/
private theorem p5Seam_trunc01_continuous : Continuous p5Trunc01 := by
  unfold p5Trunc01
  have h1 : Continuous fun x : ℝ => max (0 : ℝ) x :=
    continuous_const.max continuous_id
  exact (continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).min h1

/-- The estimator of the seam is measurable on the D3 observation measure. -/
private theorem p5Seam_estimator_aemeasurable (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ) (n : ℕ)
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
  have hHt : AEMeasurable
      (fun x => (cσ - p5KnownScaleLogStatistic f r n (δ n) t x) / (2 * Real.log n))
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
    (aemeasurable_const.sub hG).div_const (2 * Real.log n)
  have hmeas : Measurable p5Trunc01 := p5Seam_trunc01_continuous.measurable
  exact hmeas.comp_aemeasurable hHt

/-- The estimator of the seam is integrable on the D3 observation measure
(it is clipped to `[0, 1]`). -/
private theorem p5Seam_estimator_integrable (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ) (n : ℕ)
    (h : ∀ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0) :
    Integrable (p5KnownScaleEstimator f r n (δ n) t cσ)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
  refine Integrable.of_bound
    (p5Seam_estimator_aemeasurable f hf r t δ cσ n h).aestronglyMeasurable (1 : ℝ)
    (Eventually.of_forall fun x => ?_)
  have hb : p5KnownScaleEstimator f r n (δ n) t cσ x ∈ Set.Icc 0 1 :=
    p5Trunc01_mem_Icc (p5KnownScaleHtilde f r n (δ n) t cσ x)
  obtain ⟨h1, h2⟩ := hb
  exact abs_le.mpr ⟨by linarith, h2⟩

/-! ## The joining-shape bridge

Converts the parallel joining lemma's output shape (the clipped-vs-unclipped
projection gap for the unit-weight log statistic, cf.
`Hurst.P5L1Joining.logProjection_L1_tendsto_zero`) into the
`p5_transport_expectationCentered` L1 contract. -/

/-- **The seam bridge (joining-lemma shape → transport-consumable shape).**

Hypothesis `hSmall` is exactly `Hurst.P5L1Joining.logProjection_L1_tendsto_zero`
instantiated at `G = p5KnownScaleLogStatistic f r n (δ n) t`,
`Pn = featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))`,
`Sψ n = (n δ n) ^ (2 - 2 f t)`, `L n = log n`.  Its conclusion is the `hJoin`
contract consumed by `logStatistic_knownScaleH_seam`. -/
theorem p5Seam_joinBridge
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hSpos : ∀ n : ℕ, 2 ≤ n → 0 < (n : ℝ) * δ n)
    (hSmall : Tendsto (fun n : ℕ => ∫ x,
        |(2 * ((n : ℝ) * δ n) ^ (2 - 2 * f t) * Real.log n) *
            (p5Trunc01 ((cσ - p5KnownScaleLogStatistic f r n (δ n) t x) / (2 * Real.log n))
              - ∫ y, p5Trunc01
                  ((cσ - p5KnownScaleLogStatistic f r n (δ n) t y) / (2 * Real.log n)) ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) -
          (2 * ((n : ℝ) * δ n) ^ (2 - 2 * f t) * Real.log n) *
            ((cσ - p5KnownScaleLogStatistic f r n (δ n) t x) / (2 * Real.log n)
              - ∫ y, (cσ - p5KnownScaleLogStatistic f r n (δ n) t y) / (2 * Real.log n) ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ x,
        |seamScaleC f t δ n *
            (p5KnownScaleEstimator f r n (δ n) t cσ x -
              ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) -
          -(gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) x -
            ∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
      atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ hSmall
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  have hLne : Real.log n ≠ 0 := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact (Real.log_pos h1).ne'
  -- the pointwise rescaling `Ĝ_unit = S^(-ψ) Ĝ_spec`
  have hGval : ∀ z : EuclideanSpace ℝ (Fin n), p5KnownScaleLogStatistic f r n (δ n) t z
      = ((n : ℝ) * δ n) ^ (-(2 - 2 * f t)) *
        gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
          (actualQ1Coeff n (δ n) t) z := by
    intro z
    have hw : (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
        = fun i => ((n : ℝ) * δ n) ^ (-(2 - 2 * f t)) *
            actualQ1SpectralWeight f r n (δ n) t i := by
      funext i
      exact p5Seam_unitWeight_eq _ _ _ (hSpos n hn)
    unfold p5KnownScaleLogStatistic
    rw [hw, gaussianLogStatistic_const_weight_mul]
  -- the mean conversion `E H̃ = (cσ - S^(-ψ) EĜ_spec)/(2 log n)`
  have hMean : ∫ y, (cσ - p5KnownScaleLogStatistic f r n (δ n) t y) / (2 * Real.log n)
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      = (cσ - ((n : ℝ) * δ n) ^ (-(2 - 2 * f t)) *
          (∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
            (actualQ1Coeff n (δ n) t) y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
        / (2 * Real.log n) := by
    have hGSLInt : Integrable (p5KnownScaleLogStatistic f r n (δ n) t)
        (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
      (gaussianLogStatistic_memLp_two (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
        (actualQ1Coeff n (δ n) t) (hane n)).integrable one_le_two
    rw [integral_div, integral_sub (integrable_const cσ) hGSLInt,
      integral_const, smul_eq_mul, probReal_univ, one_mul,
      integral_congr_ae (Eventually.of_forall fun y => hGval y), integral_const_mul]
  -- the center identity ties the two integrands
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  have hc := p5Seam_center_identity ((n : ℝ) * δ n) (2 - 2 * f t) (Real.log n)
    (gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
      (actualQ1Coeff n (δ n) t) x)
    (∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
      (actualQ1Coeff n (δ n) t) y ∂
    featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) cσ
    (hSpos n hn) hLne
  unfold seamScaleC p5KnownScaleEstimator p5KnownScaleHtilde
  rw [hMean, hGval x, hc]

/-! ## The seam theorems -/

/-- **Generic seam core (Layer 1 as a hypothesis).**  Everything downstream of
Layer 1 in `logStatistic_knownScaleH_seam` — the negation, the measurability
and integrability contracts, and the Layer 2 transport — depends only on
`hane` and `hJoin`, not on which route produced the Layer 1 limit.  This is
the reusable form consumed by the blocker-3/4-repaired chain (double-sum
Layer 1' + general signed quadratic limit). -/
theorem logStatistic_knownScaleH_seam_of_logLimit
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hL1 : TendstoInDistribution
      (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) => gaussianLogStatistic
          (actualQ1SpectralWeight f r n (δ n) t) (actualQ1Coeff n (δ n) t) x -
        (∫ y, gaussianLogStatistic
          (actualQ1SpectralWeight f r n (δ n) t) (actualQ1Coeff n (δ n) t) y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
      atTop Q (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P')
    (cσ : ℝ)
    (hJoin : Tendsto (fun n : ℕ => ∫ ω,
        |seamScaleC f t δ n *
            (p5KnownScaleEstimator f r n (δ n) t cσ ω -
              ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) -
          -(gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) ω -
            ∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) x => seamScaleC f t δ n *
        (p5KnownScaleEstimator f r n (δ n) t cσ x -
          ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
      atTop (fun ω => -Q ω)
      (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  -- negate Layer 1 (continuous mapping theorem with `g = -·`)
  have hX : TendstoInDistribution
      (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
        -(gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
            (actualQ1Coeff n (δ n) t) x -
          ∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
            (actualQ1Coeff n (δ n) t) y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
      atTop (fun ω => -Q ω)
      (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' :=
    hL1.continuous_comp (show Continuous (fun z : ℝ => -z) by fun_prop)
  -- transport contract: measurability of the scaled centered estimator
  have hYmeas : ∀ n : ℕ, AEMeasurable
      (fun x => seamScaleC f t δ n *
        (p5KnownScaleEstimator f r n (δ n) t cσ x -
          ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
    intro n
    exact (p5Seam_estimator_aemeasurable f hf r t δ cσ n (hane n)).sub
      aemeasurable_const |>.const_mul _
  -- transport contract: integrability of the L1 gap integrand
  have hDint : ∀ᶠ n : ℕ in atTop, Integrable
      (fun ω => seamScaleC f t δ n *
          (p5KnownScaleEstimator f r n (δ n) t cσ ω -
            ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
              featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        - -(gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
            (actualQ1Coeff n (δ n) t) ω -
          ∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
    refine Eventually.of_forall fun n => ?_
    have hGInt : Integrable (gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
        (actualQ1Coeff n (δ n) t))
        (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
      (gaussianLogStatistic_memLp_two (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1SpectralWeight f r n (δ n) t) (actualQ1Coeff n (δ n) t)
        (hane n)).integrable one_le_two
    have hEstInt := p5Seam_estimator_integrable f hf r t δ cσ n (hane n)
    exact ((hEstInt.sub (integrable_const _)).const_mul _).sub
      ((hGInt.sub (integrable_const _)).neg)
  -- assemble via Layer 2's transport core
  exact p5_transport_expectationCentered _ _ _ hX hYmeas hDint hJoin

/-- **The Layer1 → Layer2 seam (expectation-centered), conditionally on `hJoin`.

From (i) Layer 1's quadratic→log conclusion
`actualQ1_logStatistic_tendsto_secondChaos_of_quadratic` (the D3 signature
verbatim), (ii) the L1 joining contract `hJoin` (exact shape of the `hL1`
input of `p5_transport_expectationCentered` at the chain objects:
`∫ ω, |c n (Ĥ_n ω - E Ĥ_n) - -(Ĝ_spec n ω - EĜ_spec n)| ∂Pn n → 0`), and
(iii) Layer 2's transport contract, conclude the known-scale H layer
`c n (Ĥ_n - E Ĥ_n) ⇒ -Q` with `c n = 2 S^ψ log n`, `S = n δ n`,
`ψ = 2 - 2 f t`, `Ĥ_n = p5KnownScaleEstimator f r n (δ n) t cσ`. -/
theorem logStatistic_knownScaleH_seam
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (min ((actualQ1Hermitian f hf r n (δ n) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0))
    (hlong : 3 / 4 < f t)
    (hW0 : Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) atTop (𝓝 0))
    (hE2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2 ≤ C)
    (cσ : ℝ)
    (hJoin : Tendsto (fun n : ℕ => ∫ ω,
        |seamScaleC f t δ n *
            (p5KnownScaleEstimator f r n (δ n) t cσ ω -
              ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) -
          -(gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) ω -
            ∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) x => seamScaleC f t δ n *
        (p5KnownScaleEstimator f r n (δ n) t cσ x -
          ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
      atTop (fun ω => -Q ω)
      (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  -- Layer 1: `Ĝ_spec - EĜ_spec ⇒ Q` (D3 signature verbatim)
  have hL1 := actualQ1_logStatistic_tendsto_secondChaos_of_quadratic f hf r t δ hδpos hδ0
    hN ht P' Q lam hQ hlam hPow hane hNegMass hlong hW0 hE2
  exact logStatistic_knownScaleH_seam_of_logLimit f hf r t δ P' Q hane hL1 cσ hJoin

set_option linter.unusedVariables false in
/-- **The Layer1 → Layer2 seam (truth-centered), conditionally on `hJoin`.

Under the E5 bias condition `(1 - γ) ψ < γ s` with the conservative `s = 1`
(`hE5`, with `γ = f t` and `ψ = 2 - 2 f t`; it is exactly what makes the
deterministic drift vanish upstream) and the explicit drift smallness
`hDrift : c n (E Ĥ_n - f t) → 0`, the expectation-centered seam limit implies
the truth-centered known-scale H layer `c n (Ĥ_n - f t) ⇒ -Q`. -/
theorem logStatistic_knownScaleH_seam_truthCentered
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (min ((actualQ1Hermitian f hf r n (δ n) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0))
    (hlong : 3 / 4 < f t)
    (hW0 : Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) atTop (𝓝 0))
    (hE2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2 ≤ C)
    (cσ : ℝ)
    (hJoin : Tendsto (fun n : ℕ => ∫ ω,
        |seamScaleC f t δ n *
            (p5KnownScaleEstimator f r n (δ n) t cσ ω -
              ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) -
          -(gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) ω -
            ∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
      atTop (𝓝 0))
    (hE5 : (1 - f t) * (2 - 2 * f t) < f t)
    (hDrift : Tendsto (fun n : ℕ => seamScaleC f t δ n *
        ((∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) x => seamScaleC f t δ n *
        (p5KnownScaleEstimator f r n (δ n) t cσ x - f t))
      atTop (fun ω => -Q ω)
      (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  have hE := logStatistic_knownScaleH_seam f hf r t δ hδpos hδ0 hN ht P' Q lam hQ hlam
    hPow hane hNegMass hlong hW0 hE2 cσ hJoin
  refine @p5_transport_truthCentered_of_drift
    (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    (fun n => featureGaussian_isProbability _) Theta _ P' _ Q
    (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) => p5KnownScaleEstimator f r n (δ n) t cσ x)
    (fun n => seamScaleC f t δ n) (f t) hE ?meas ?dint ?l1
  · intro n
    exact ((p5Seam_estimator_aemeasurable f hf r t δ cσ n (hane n)).sub
      aemeasurable_const).const_mul _
  · refine Eventually.of_forall fun n => ?_
    have hEstInt := p5Seam_estimator_integrable f hf r t δ cσ n (hane n)
    exact (((hEstInt.sub (integrable_const (f t))).const_mul _).sub
      ((hEstInt.sub (integrable_const _)).const_mul _))
  · -- the projection drift is constant: `∫ |...| = |c n (E Ĥ_n - f t)| → 0`
    have habscont : Continuous (fun z : ℝ => |z|) := by fun_prop
    have key : Tendsto (fun n : ℕ => |seamScaleC f t δ n *
        ((∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|)
        atTop (𝓝 0) := by
      have h0 := (habscont.tendsto (0 : ℝ)).comp hDrift
      have h1 : Tendsto (fun n : ℕ => |seamScaleC f t δ n *
          ((∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
              featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|)
          atTop (𝓝 (abs (0 : ℝ))) :=
        h0.congr (fun n => rfl)
      rwa [abs_zero] at h1
    have hint : ∀ n : ℕ, ∫ ω,
        |seamScaleC f t δ n * (p5KnownScaleEstimator f r n (δ n) t cσ ω - f t)
          - seamScaleC f t δ n * (p5KnownScaleEstimator f r n (δ n) t cσ ω
              - ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        = |seamScaleC f t δ n *
            ((∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|
        := by
      intro n
      have hpt : ∀ ω : EuclideanSpace ℝ (Fin n),
          |seamScaleC f t δ n * (p5KnownScaleEstimator f r n (δ n) t cσ ω - f t)
            - seamScaleC f t δ n * (p5KnownScaleEstimator f r n (δ n) t cσ ω
                - ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                    featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
          = |seamScaleC f t δ n *
              ((∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)| :=
        fun ω => by
          rw [show seamScaleC f t δ n * (p5KnownScaleEstimator f r n (δ n) t cσ ω - f t)
              - seamScaleC f t δ n * (p5KnownScaleEstimator f r n (δ n) t cσ ω
                  - ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              = seamScaleC f t δ n *
                  ((∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                    - f t) by ring]
      calc ∫ ω,
          |seamScaleC f t δ n * (p5KnownScaleEstimator f r n (δ n) t cσ ω - f t)
            - seamScaleC f t δ n * (p5KnownScaleEstimator f r n (δ n) t cσ ω
                - ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                    featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
            ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          = ∫ ω, |seamScaleC f t δ n *
              ((∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|
            ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) :=
            integral_congr_ae (Eventually.of_forall hpt)
        _ = |seamScaleC f t δ n *
              ((∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)| := by
            rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    refine Tendsto.congr (fun n => ?_) key
    rw [hint n]

end Hurst
