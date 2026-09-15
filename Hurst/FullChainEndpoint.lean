import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Hurst.P5JoinInstantiation
import Hurst.P5TruthCenter

/-!
# Full-chain endpoint: the quadratic second-chaos limit → the known-scale H law

ONE composition of the landed P5 layers, at the FEASIBLE bandwidth
`δ n = n^{-γ}` (`0 < γ < 1`):

* D3 (`actualQ1LongStatistic_tendsto_secondChaos_signed`, quadratic → signed
  second chaos) is consumed INTERNALLY by Layer 1;
* Layer 1 (`actualQ1_logStatistic_tendsto_secondChaos_of_quadratic`):
  quadratic → expectation-centered log limit `Ĝ_spec - E Ĝ_spec ⇒ Q`;
* the L1 joining lemma instantiated at the seam
  (`Hurst.P5JoinInstantiation.logProjection_L1_tendsto_instantiated`)
  DISCHARGES the seam's `hJoin` contract — its conclusion IS the `hJoin`
  consumed by the seam (verified against the exact statements);
* the seam (`Hurst.P5SeamClosed.logStatistic_knownScaleH_seam`):
  log → known-scale H, expectation-centered `c n (Ĥ_n - E Ĥ_n) ⇒ -Q`
  with `c n = 2 S^ψ log n`, `S = n δ n = n^{1-γ}`, `ψ = 2 - 2 f t`;
* the E5 truth-centering layer: `p5_truthCenter_drift_s1` supplies the
  deterministic drift `c n (E Ĥ_n - f t) → 0` from the explicit bias envelope
  `hBias` under the E5 window `(1 - γ) * ψ < γ * 1` (conservative `s = 1`),
  and file 24 E4's center-change rule
  (`p5_transport_truthCentered_of_drift`) ends at the endpoint
  `c n (Ĥ_n - f t) ⇒ -Q`.

Main statements:

* `actualQ1_knownScaleH_fullChain` — the TRUTH-centered endpoint
  `seamScaleC f t (n ↦ n^{-γ}) n * (Ĥ_n - f t) ⇒ -Q` (needs the E5 window
  `hE5` and the explicit `s = 1` bias envelope `hBias`);
* `actualQ1_knownScaleH_fullChain_expectationCentered` — the KNOWN-SCALE
  (expectation-centered) variant `seamScaleC f t (n ↦ n^{-γ}) n *
  (Ĥ_n - E Ĥ_n) ⇒ -Q` (no E5 data needed);
* `actualQ1_knownScaleH_fullChain_feasible` — the instance `γ = f t`, where
  the E5 window `(1 - f t) * ψ < f t` (with `ψ = 2 - 2 f t`) is discharged
  from the long-memory band `hlong : 3 / 4 < f t` by arithmetic alone.

The union of the ordinary hypotheses is carried VERBATIM from the layers:

* D3 data: `hQ`, `hlam`, `hm`, `hPow`, `hane`, `hNegMass` (stated at the
  feasible bandwidth) and the long-memory band `hlong : 3 / 4 < f t`;
* L1-instantiation data: `hW0`, `hE2`, the calibration center `cσ`, the
  projection-center band width `d` (`hd : 0 < d`) and the band `hband`
  (the center depends on the data; discharging it is upstream, file 22 W9);
* E5 data: the window `hE5` and the explicit bias envelope `hBias`
  (upstream, see the deviation note in `Hurst.P5TruthCenter`).

Discharged INTERNALLY from `γ` and `hf`: the D3 window facts `hδpos`, `hδ0`,
`hN` (feasible-bandwidth mesh `n δ n = n^{1-γ} → ∞`), the pointwise `hSpos`
of the join instantiation, and `hfb : f t < 1` (from `hf.1` and `ht`).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## The feasible bandwidth `δ n = n^{-γ}`: the D3 window facts -/

/-- The feasible bandwidth `δ n = n^{-γ}` is eventually positive. -/
private theorem feasibleBandwidth_pos (γ : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) ^ (-γ)) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

/-- The feasible bandwidth tends to zero for `0 < γ`. -/
private theorem feasibleBandwidth_tendsto (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ (-γ))) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop

set_option linter.unusedVariables false in
/-- The feasible-bandwidth mesh `n δ n = n^{1 - γ}` diverges for `γ < 1`. -/
private theorem feasibleMesh_tendsto_atTop (γ : ℝ) (hγ : 0 < γ) (hγlt : γ < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) * ((n : ℝ) ^ (-γ)))) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 - γ))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  refine Tendsto.congr' ?_ h1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heq : ((n : ℝ) * ((n : ℝ) ^ (-γ))) = (n : ℝ) ^ (1 - γ) := by
    conv_rhs => rw [show (1 : ℝ) - γ = (1 : ℝ) + (-γ) by ring]
    rw [Real.rpow_add hn0 (1 : ℝ) (-γ), Real.rpow_one]
  exact heq.symm

/-- The feasible-bandwidth mesh is eventually positive (the pointwise `hSpos`
of `logProjection_L1_tendsto_instantiated`). -/
private theorem feasibleMesh_pos (γ : ℝ) :
    ∀ n : ℕ, 2 ≤ n → 0 < (n : ℝ) * ((n : ℝ) ^ (-γ)) := by
  intro n hn
  have h0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact mul_pos h0 (Real.rpow_pos_of_pos h0 _)

/-! ## Auxiliary regularity of the clipped known-scale estimator -/

/-- The clipped known-scale estimator is a.e. measurable on the D3
observation measure (the P5SeamClosed regularity, at a general bandwidth). -/
private theorem fullChain_estimator_aemeasurable (f : ℝ → ℝ)
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

/-- The clipped known-scale estimator is integrable on the D3 observation
measure (it is clipped to `[0, 1]`). -/
private theorem fullChain_estimator_integrable (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ) (n : ℕ)
    (h : ∀ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0) :
    Integrable (p5KnownScaleEstimator f r n (δ n) t cσ)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
  refine Integrable.of_bound
    (fullChain_estimator_aemeasurable f hf r t δ cσ n h).aestronglyMeasurable (1 : ℝ)
    (Eventually.of_forall fun x => ?_)
  have hb : p5KnownScaleEstimator f r n (δ n) t cσ x ∈ Set.Icc 0 1 :=
    p5Trunc01_mem_Icc (p5KnownScaleHtilde f r n (δ n) t cσ x)
  obtain ⟨h1, h2⟩ := hb
  exact abs_le.mpr ⟨by linarith, h2⟩

/-! ## The full-chain endpoint (truth-centered, via the E5 drift) -/

/-- **The full-chain endpoint (truth-centered).**  At the feasible bandwidth
`δ n = n^{-γ}` (`0 < γ < 1`) the clipped known-scale H estimator satisfies

`2 n^{ψ (1 - γ)} log n * (Ĥ_n - f t) ⇒ -Q`,   `ψ = 2 - 2 f t`,

under (i) the D3 signature at that bandwidth (`hQ`, `hlam`, `hm`, `hPow`,
`hane`, `hNegMass`, `hlong`), (ii) the L1-instantiation data (`hW0`, `hE2`,
`cσ`, `d`, `hd`, `hband`), and (iii) the E5 data (`hE5` with the conservative
`s = 1`, and the explicit bias envelope `hBias`).  Each landed layer is
applied internally: D3 → Layer 1 → instantiated L1 join → seam → E5
truth-centering. -/
theorem actualQ1_knownScaleH_fullChain
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (γ : ℝ) (hγpos : 0 < γ) (hγlt : γ < 1)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hm : ∀ n, 0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card)
    (hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0))
    (hlong : 3 / 4 < f t)
    (hW0 : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i) ^ 2) atTop (𝓝 0))
    (hE2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t i)
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t j)) ^ 2 ≤ C)
    (cσ d : ℝ) (hd : 0 < d)
    (hband : ∀ᶠ n in atTop,
      d ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
        ≤ 1 - d)
    (hE5 : (1 - γ) * (2 - 2 * f t) < γ * 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * ((n : ℝ) ^ (-γ))) :
    TendstoInDistribution
      (fun (n : ℕ) x => seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
        (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ x - f t))
      atTop (fun ω => -Q ω)
      (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  -- the D3 window facts at the feasible bandwidth
  have hδpos := feasibleBandwidth_pos γ
  have hδ0 := feasibleBandwidth_tendsto γ hγpos
  have hN := feasibleMesh_tendsto_atTop γ hγpos hγlt
  -- `hfb : f t < 1` from the Holder class membership
  have hfb : f t < 1 := (hf.1 ht).2
  -- the L1 join instantiated at the seam: its conclusion IS the seam's `hJoin`
  have hJoin := logProjection_L1_tendsto_instantiated f hf r t
    (fun m => ((m : ℝ) ^ (-γ))) (feasibleMesh_pos γ) hN hlong hfb hane hW0 hE2
    cσ d hd hband
  -- the expectation-centered seam (Layer 1 internally applies D3)
  have hE := logStatistic_knownScaleH_seam f hf r t (fun m => ((m : ℝ) ^ (-γ)))
    hδpos hδ0 hN ht P' Q lam hQ hlam hm hPow hane hNegMass hlong hW0 hE2 cσ hJoin
  -- the E5 drift at the feasible bandwidth
  have hDrift := p5_truthCenter_drift_s1 f hf r t cσ γ hγpos hγlt hlong hfb hE5 C hC hBias
  -- file 24 E4: center change by the vanishing deterministic drift
  refine @p5_transport_truthCentered_of_drift
    (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    (fun n => featureGaussian_isProbability _) Theta _ P' _ Q
    (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
      p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ x)
    (fun n => seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n) (f t) hE ?_ ?_ ?_
  · -- measurability of the truth-centered scaled statistic
    intro n
    exact ((fullChain_estimator_aemeasurable f hf r t (fun m => ((m : ℝ) ^ (-γ))) cσ n
      (hane n)).sub aemeasurable_const).const_mul _
  · -- integrability of the L1 gap integrand
    refine Eventually.of_forall fun n => ?_
    have hEstInt := fullChain_estimator_integrable f hf r t
      (fun m => ((m : ℝ) ^ (-γ))) cσ n (hane n)
    exact (((hEstInt.sub (integrable_const (f t))).const_mul _).sub
      ((hEstInt.sub (integrable_const _)).const_mul _))
  · -- the projection drift is constant: `∫ |...| = |c n (E Ĥ_n - f t)| → 0`
    have habscont : Continuous (fun z : ℝ => |z|) := by fun_prop
    have key : Tendsto (fun n : ℕ => |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
        ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|)
        atTop (𝓝 0) := by
      have h0 := (habscont.tendsto (0 : ℝ)).comp hDrift
      have h1 : Tendsto (fun n : ℕ => |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
          ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
              featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|)
          atTop (𝓝 (abs (0 : ℝ))) :=
        h0.congr (fun n => rfl)
      rwa [abs_zero] at h1
    have hint : ∀ n : ℕ, ∫ ω,
        |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω - f t)
          - seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω
              - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        = |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
            ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|
        := by
      intro n
      have hpt : ∀ ω : EuclideanSpace ℝ (Fin n),
          |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω - f t)
            - seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω
                - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                    featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
          = |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|
          := fun ω => by
            rw [show seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω - f t)
              - seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω
                  - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              = seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                  ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                    - f t) by ring]
      calc ∫ ω,
            |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω - f t)
              - seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω
                  - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
            ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          = ∫ ω, |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|
            ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) :=
            integral_congr_ae (Eventually.of_forall hpt)
        _ = |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)| := by
            rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    refine Tendsto.congr (fun n => ?_) key
    rw [hint n]

/-! ## The known-scale (expectation-centered) endpoint -/

/-- **The full-chain endpoint (expectation-centered).**  The KNOWN-SCALE
variant of `actualQ1_knownScaleH_fullChain`: at the feasible bandwidth
`δ n = n^{-γ}` the expectation-centered law

`2 n^{ψ (1 - γ)} log n * (Ĥ_n - E Ĥ_n) ⇒ -Q`

needs NO E5 data — only the D3 signature and the L1-instantiation data
(`hband` etc.). -/
theorem actualQ1_knownScaleH_fullChain_expectationCentered
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (γ : ℝ) (hγpos : 0 < γ) (hγlt : γ < 1)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hm : ∀ n, 0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card)
    (hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0))
    (hlong : 3 / 4 < f t)
    (hW0 : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i) ^ 2) atTop (𝓝 0))
    (hE2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t i)
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t j)) ^ 2 ≤ C)
    (cσ d : ℝ) (hd : 0 < d)
    (hband : ∀ᶠ n in atTop,
      d ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
        ≤ 1 - d) :
    TendstoInDistribution
      (fun (n : ℕ) x => seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
        (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ x -
          ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
      atTop (fun ω => -Q ω)
      (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  have hδpos := feasibleBandwidth_pos γ
  have hδ0 := feasibleBandwidth_tendsto γ hγpos
  have hN := feasibleMesh_tendsto_atTop γ hγpos hγlt
  have hfb : f t < 1 := (hf.1 ht).2
  have hJoin := logProjection_L1_tendsto_instantiated f hf r t
    (fun m => ((m : ℝ) ^ (-γ))) (feasibleMesh_pos γ) hN hlong hfb hane hW0 hE2
    cσ d hd hband
  exact logStatistic_knownScaleH_seam f hf r t (fun m => ((m : ℝ) ^ (-γ)))
    hδpos hδ0 hN ht P' Q lam hQ hlam hm hPow hane hNegMass hlong hW0 hE2 cσ hJoin

/-! ## The feasible instance `γ = f t`: the E5 window is free -/

/-- **The feasible instance `γ = f t` of the truth-centered endpoint.**  At
the bandwidth `δ n = n^{-f t}` (note `0 < f t < 1` from `ht` and `hf.1`) the
E5 window `(1 - f t) * (2 - 2 * f t) < f t` — i.e. `ψ² < f t` with
`ψ = 2 - 2 f t` — follows from the long-memory band `hlong : 3 / 4 < f t` by
arithmetic alone, so the truth-centered endpoint needs only the D3 signature,
the L1-instantiation data and the explicit bias envelope `hBias`. -/
theorem actualQ1_knownScaleH_fullChain_feasible
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hm : ∀ n, 0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card)
    (hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
        (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-(f t))) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
        (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-(f t))) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0))
    (hlong : 3 / 4 < f t)
    (hW0 : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
        (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-(f t))) t i) ^ 2) atTop (𝓝 0))
    (hE2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t i)
            (actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t j)) ^ 2 ≤ C)
    (cσ d : ℝ) (hd : 0 < d)
    (hband : ∀ᶠ n in atTop,
      d ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-(f t))) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-(f t))) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
        ≤ 1 - d)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * ((n : ℝ) ^ (-(f t)))) :
    TendstoInDistribution
      (fun (n : ℕ) x => seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
        (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t cσ x - f t))
      atTop (fun ω => -Q ω)
      (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  have hft : f t ∈ Ioo (0 : ℝ) 1 := hf.1 ht
  have hft1 : (f t : ℝ) < 1 := hft.2
  -- the E5 window at `γ = f t` is `ψ² < f t`, discharged from `hlong`
  have hE5 : (1 - f t) * (2 - 2 * f t) < f t * 1 := by
    have hq : (0 : ℝ) ≤ 1 - f t := by linarith
    have hq1 : 1 - f t ≤ 1 / 4 := by linarith
    have hsq : (1 - f t) * (1 - f t) ≤ (1 - f t) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hq1 hq
    have hsq2 : (1 - f t) * (1 / 4) ≤ (1 : ℝ) / 16 := by
      have h := mul_le_mul_of_nonneg_right hq1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      rwa [show ((1 : ℝ) / 4) * (1 / 4) = (1 : ℝ) / 16 by norm_num] at h
    have e : (1 - f t) * (2 - 2 * f t) = 2 * ((1 - f t) * (1 - f t)) := by ring
    rw [e]
    linarith
  exact actualQ1_knownScaleH_fullChain f hf r t ht (f t) hft.1 hft.2 P' Q lam hQ hlam
    hm hPow hane hNegMass hlong hW0 hE2 cσ d hd hband hE5 C hC hBias

end Hurst
