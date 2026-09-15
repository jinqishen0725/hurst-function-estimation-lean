import Hurst.P5TruthCenter
import Hurst.GridErrorRate
import Hurst.P5LogHLayers
import Hurst.FirstScaleLongRates

/-!
# File 24 E5: the bias envelope `|E[Ĥ_n] - h| ≤ C n^{-γ}` from the grid-error layer

This file closes the last upstream of the truth-centered variant: it derives the
EXPLICIT bias envelope consumed by `Hurst.P5TruthCenter.drift_condition_s1`
(`|E Ĥ_n - h| ≤ C n^{-γ}`) from the grid-error layer, closing the truth-centering
under the ordinary model + feasible bandwidth `δ n = n^{-γ}`.

## The written E5 derivation (file 24, §E5) and its rate algebra

The landed log-layer bias
(`Hurst.FirstScaleLongBias.hurstHolder_q1_linearScale_bias_lt_one`, mirrored as
the hypothesis `hLogBias` of `e5_calibratedBias_of_logBias` below) is

`|E Ĝ_n - (cσ - 2 h log n)| ≤ log n * gridCovarianceError b E n`,

with `gridCovarianceError b E n = E * (1 + log (2n)) * (n^{-1} + n^{2b-2})`
(`Hurst.GridCorrelationDecay`).  Through the known-scale calibration
`X_n = (cσ - Ĝ_n) / (2 log n)` (the `p5_YX_identity` scale) this becomes a bias
of the UNTRUNCATED H statistic of size `gridCovarianceError b E n / 2` — the
`log n` factors CANCEL.  Paper check of the remaining factor (as requested):
`gridCovarianceError b E n ~ E (1 + log 2n) n^{max(-1, 2b-2)}` has no `δ`
dependence at all, and

`gridCovarianceError b E n * n^{γ} → 0`  iff  `0 < γ < 1` and `γ + 2b < 2`

(`gridCovarianceError_rpow_tendsto` below): the `(1 + log 2n)` factor is
absorbed polynomially, so the consumer's clean envelope `C n^{-γ}` holds with NO
residual log factor whenever `γ + 2 * b < 2` — the grid-error headroom window.
(`gridErr` decays FASTER than `n^{-γ}` exactly in that window; if `γ ≥ 2 - 2b`
the honest envelope is the slower `gridCovarianceError`-shaped one and the
consumer's `s = 1` window must be adjusted — not taken here.)

## What is proved / the honest gaps

* `e5_calibratedBias_of_logBias` — the log-cancellation: the landed-shape
  log-statistic bias gives the calibrated untruncated-H bias
  `|E X_n - h| ≤ gridCovarianceError b E n / 2`.  Pure bias algebra.
* `e5_bias_envelope` — the MAIN statement for the CLIPPED estimator
  `Ĥ_n = p5Trunc01 (X_n)`: `∃ C ≥ 0, ∀ᶠ n, |E Ĥ_n - h| ≤ C n^{-γ}`, from the
  calibrated bias plus ONE explicit fluctuation hypothesis
  `hFluct : E|X_n - E X_n| ≤ F n^{-γ}` (the mean-centered L1 layer).  This
  hypothesis is needed because `p5Trunc01` is not affine:
  `|E[T(X)] - h| ≤ |T(E X) - h| + E|T(X) - T(E X)|`, and the second term is a
  fluctuation, not a bias.  It mirrors the landed variance layer
  (`Hurst.FirstScaleLongVariance`): `E|X_n - E X_n| ≤ sqrt Var Ĝ / (2 log n) ~
  sqrt(firstStrideLongRowBound / n) / 2`, which is `O(n^{-γ})` whenever the
  row-bound grows subpolynomially against `n^{1 - 2γ}` (e.g. `γ < 1/2`).
* `e5_drift_of_bias_envelope` — composition with
  `Hurst.P5TruthCenter.drift_condition_s1`: under the E5 window
  `(1 - γ) * ψ < γ * 1` the truth-centering drift vanishes.  Full consistency of
  the windows (`ψ/(1+ψ) < γ < 1/2` plus `γ + 2b < 2`) is feasible in the
  long-memory band `0 < ψ < 1/2` with `b < 1 - γ/2`.
* Instantiation at the literal P5 chain objects additionally needs the
  measurability/integrability of `p5KnownScaleLogStatistic` under
  `featureGaussian` (upstream); the statements here are therefore packaged over
  an abstract probability model, with the log-bias hypothesis in EXACTLY the
  landed bias lemma's conclusion shape.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Hurst

/-! ## The clipped transform: Lipschitz continuity and expectation transfer -/

/-- `p5Trunc01` is the clamp to `[0, 1]`. -/
private theorem p5Trunc01_eq_clamp (x : ℝ) : p5Trunc01 x = max 0 (min 1 x) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [p5Trunc01, max_eq_left (le_of_lt hx),
      min_eq_right (le_of_lt (show x < 1 by linarith)),
      max_eq_left (le_of_lt hx), min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
  · rw [hx, p5Trunc01]
    norm_num
  · rcases lt_trichotomy x 1 with hy | hy | hy
    · rw [p5Trunc01, max_eq_right hx.le, min_eq_right hy.le, max_eq_right hx.le]
    · rw [hy, p5Trunc01]
      norm_num
    · rw [p5Trunc01, max_eq_right hx.le, min_eq_left hy.le,
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

private theorem p5Trunc01_continuous : Continuous p5Trunc01 := by
  show Continuous fun x => min 1 (max 0 x)
  exact continuous_const.min (continuous_const.max continuous_id)

private theorem min_one_lipschitz (a b : ℝ) : |min 1 a - min 1 b| ≤ |a - b| := by
  rcases lt_trichotomy a 1 with ha | ha | ha <;>
  rcases lt_trichotomy b 1 with hb | hb | hb
  · rw [min_eq_right ha.le, min_eq_right hb.le]
  · rw [hb, min_eq_right ha.le, min_eq_right (le_refl (1 : ℝ))]
  · rw [min_eq_right ha.le, min_eq_left hb.le,
      abs_of_neg (show a - 1 < 0 by linarith),
      abs_of_neg (show a - b < 0 by linarith)]
    linarith
  · rw [ha, min_eq_right hb.le, min_eq_right (le_refl (1 : ℝ))]
  · rw [ha, hb, min_eq_left (le_refl (1 : ℝ))]
  · rw [ha, min_eq_left (le_refl (1 : ℝ)), min_eq_left hb.le]
    simp
  · rw [min_eq_left ha.le, min_eq_right hb.le,
      abs_of_pos (show 0 < 1 - b by linarith),
      abs_of_pos (show 0 < a - b by linarith)]
    linarith
  · rw [hb, min_eq_left ha.le, min_eq_left (le_refl (1 : ℝ))]
    simp
  · rw [min_eq_left ha.le, min_eq_left hb.le]
    simp

/-- `p5Trunc01` is 1-Lipschitz. -/
theorem p5Trunc01_lipschitz (a b : ℝ) : |p5Trunc01 a - p5Trunc01 b| ≤ |a - b| := by
  rw [p5Trunc01_eq_clamp a, p5Trunc01_eq_clamp b, max_comm 0 (min 1 a),
    max_comm 0 (min 1 b)]
  calc |max (min 1 a) 0 - max (min 1 b) 0| ≤ |min 1 a - min 1 b| :=
        abs_max_sub_max_le_abs (min 1 a) (min 1 b) 0
    _ ≤ |a - b| := min_one_lipschitz a b

/-- **Expectation transfer through the clip.**  For a probability measure and an
integrable real statistic, the expectation of the clipped statistic is within
the mean-centered L1 mass of the unclipped one plus the calibrated bias of the
truth `h ∈ [0, 1]`. -/
theorem p5Trunc01_expectation_dist {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXint : Integrable X μ)
    (h : ℝ) (hh : h ∈ Icc 0 1) :
    |∫ x, p5Trunc01 (X x) ∂μ - h| ≤ ∫ x, |X x - (∫ y, X y ∂μ)| ∂μ
      + |(∫ y, X y ∂μ) - h| := by
  have hTXm : AEMeasurable (fun x => p5Trunc01 (X x)) μ :=
    p5Trunc01_continuous.measurable.comp_aemeasurable hXint.aemeasurable
  have hTXint : Integrable (fun x => p5Trunc01 (X x)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hTXm.aestronglyMeasurable ?_
    filter_upwards with x
    have hx := p5Trunc01_mem_Icc (X x)
    simp only [Real.norm_eq_abs]
    refine abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hTmint : Integrable (fun _ : Ω => p5Trunc01 (∫ y, X y ∂μ)) μ :=
    integrable_const _
  have hsubint : Integrable
      (fun x => p5Trunc01 (X x) - p5Trunc01 (∫ y, X y ∂μ)) μ := hTXint.sub hTmint
  have hintconst : ∫ x, p5Trunc01 (∫ y, X y ∂μ) ∂μ = p5Trunc01 (∫ y, X y ∂μ) := by
    rw [integral_const]
    simp
  -- step A: |E T(X) - T(E X)| ≤ E|X - E X|
  have stepA : |∫ x, p5Trunc01 (X x) ∂μ - ∫ x, p5Trunc01 (∫ y, X y ∂μ) ∂μ|
      ≤ ∫ x, |X x - (∫ y, X y ∂μ)| ∂μ := by
    rw [← integral_sub hTXint hTmint]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono hsubint.abs (hXint.sub (integrable_const _)).abs ?_
    intro x
    simpa only [Real.norm_eq_abs] using p5Trunc01_lipschitz (X x) (∫ y, X y ∂μ)
  -- step B: |E[T(E X)] - h| ≤ |E X - h|
  have stepB : |∫ x, p5Trunc01 (∫ y, X y ∂μ) ∂μ - h| ≤ |(∫ y, X y ∂μ) - h| := by
    rw [hintconst]
    have hTh : p5Trunc01 h = h := p5Trunc01_eq_self hh
    calc |p5Trunc01 (∫ y, X y ∂μ) - h|
        = |p5Trunc01 (∫ y, X y ∂μ) - p5Trunc01 h| := by rw [hTh]
      _ ≤ |(∫ y, X y ∂μ) - h| := p5Trunc01_lipschitz _ _
  calc |∫ x, p5Trunc01 (X x) ∂μ - h|
      = |(∫ x, p5Trunc01 (X x) ∂μ - ∫ x, p5Trunc01 (∫ y, X y ∂μ) ∂μ)
          + (∫ x, p5Trunc01 (∫ y, X y ∂μ) ∂μ - h)| := by congr 1; ring
    _ ≤ |∫ x, p5Trunc01 (X x) ∂μ - ∫ x, p5Trunc01 (∫ y, X y ∂μ) ∂μ|
          + |∫ x, p5Trunc01 (∫ y, X y ∂μ) ∂μ - h| := abs_add_le _ _
    _ ≤ ∫ x, |X x - (∫ y, X y ∂μ)| ∂μ + |(∫ y, X y ∂μ) - h| := by
        linarith [stepA, stepB]

/-! ## The grid-error envelope at rate `n^{-γ}` -/

/-- **The grid-error decay is polynomially faster than `n^{-γ}`** in the window
`0 < γ < 1`, `γ + 2 * b < 2`: `gridCovarianceError b E n * n^{γ} → 0`.  This is
the paper-check step: the `(1 + log (2n))` factor of the grid covariance error
is absorbed, so the landed grid-error layer yields the clean bandwidth-power
envelope consumed by `Hurst.P5TruthCenter.drift_condition_s1` (no residual log
factor). -/
theorem gridCovarianceError_rpow_tendsto (b E γ : ℝ) (hb : b < 1)
    (hγpos : 0 < γ) (hγlt : γ < 1) (hγb : γ + 2 * b < 2) :
    Tendsto (fun n : ℕ => gridCovarianceError b E n * (n : ℝ) ^ γ)
      atTop (𝓝 0) := by
  have hr1 : γ - 1 < 0 := by linarith
  have hr2 : 2 * b - 2 + γ < 0 := by linarith
  have h1 := (mesh_log_power_rpow_tendsto (γ - 1) hr1 1).const_mul E
  have h2 := (mesh_log_power_rpow_tendsto (2 * b - 2 + γ) hr2 1).const_mul E
  simp only [pow_one] at h1 h2
  have h := h1.add h2
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have e1 : (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ γ = (n : ℝ) ^ (γ - 1) := by
    rw [← Real.rpow_add hn0]
    ring
  have e2 : (n : ℝ) ^ (2 * b - 2) * (n : ℝ) ^ γ = (n : ℝ) ^ (2 * b - 2 + γ) := by
    rw [← Real.rpow_add hn0]
  unfold gridCovarianceError
  calc E * ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (γ - 1)) +
      E * ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (2 * b - 2 + γ))
    = E * (1 + Real.log (2 * (n : ℝ))) * ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
        * (n : ℝ) ^ γ := by
        rw [mul_add, ← e1, ← e2, ← mul_assoc, ← mul_assoc, ← mul_add]
        ring

/-- The envelope corollary: eventually
`gridCovarianceError b E n ≤ n^{-γ}` (with constant `1`) in the same window. -/
theorem gridCovarianceError_le_const_rpow (b E γ : ℝ) (hb : b < 1)
    (hγpos : 0 < γ) (hγlt : γ < 1) (hγb : γ + 2 * b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      gridCovarianceError b E n ≤ C * (n : ℝ) ^ (-γ) := by
  refine ⟨1, zero_le_one, ?_⟩
  have h := gridCovarianceError_rpow_tendsto b E γ hb hγpos hγlt hγb
  have hlt : ∀ᶠ n : ℕ in atTop, gridCovarianceError b E n * (n : ℝ) ^ γ < 1 :=
    h.eventually_lt_const zero_lt_one
  filter_upwards [hlt, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hne : (n : ℝ) ^ (-γ) ≠ 0 :=
    (Real.rpow_ne_zero hn0.le (by linarith : (-γ : ℝ) ≠ 0)).mpr hn0.ne'
  have hgg : (n : ℝ) ^ γ * (n : ℝ) ^ (-γ) = 1 := by
    rw [← Real.rpow_add hn0, show γ + -γ = (0 : ℝ) by ring, Real.rpow_zero]
  have key : gridCovarianceError b E n ≤ (n : ℝ) ^ (-γ) := by
    have h1' : gridCovarianceError b E n * (n : ℝ) ^ γ * (n : ℝ) ^ (-γ)
        ≤ (1 : ℝ) * (n : ℝ) ^ (-γ) :=
      mul_le_mul_of_nonneg_right hn.le (Real.rpow_nonneg hn0.le _)
    rw [one_mul] at h1'
    have h2' : gridCovarianceError b E n * (n : ℝ) ^ γ * (n : ℝ) ^ (-γ)
        = gridCovarianceError b E n := by
      rw [mul_assoc, hgg, mul_one]
    rw [← h2']
    exact h1'
  rw [one_mul]
  exact key

/-! ## The E5 bias envelope -/

/-- **Log-layer cancellation (file 24 §E5, (E2)).**  The landed log-statistic
bias (EXACTLY the conclusion shape of
`Hurst.FirstScaleLongBias.hurstHolder_q1_linearScale_bias_lt_one`:
`|E Ĝ_n - (cσ - 2 h log n)| ≤ log n * gridCovarianceError b E n`) gives, through
the known-scale calibration `X = (cσ - Ĝ) / (2 log n)`, the calibrated
untruncated-H bias `|E X_n - h| ≤ gridCovarianceError b E n / 2`: the `log n`
factors cancel. -/
theorem e5_calibratedBias_of_logBias (cσ h E b : ℝ) (EG : ℕ → ℝ)
    (hLogBias : ∀ᶠ n : ℕ in atTop,
      |EG n - (cσ - 2 * h * Real.log (n : ℝ))|
        ≤ Real.log (n : ℝ) * gridCovarianceError b E n) :
    ∀ᶠ n : ℕ in atTop,
      |(cσ - EG n) / (2 * Real.log (n : ℝ)) - h|
        ≤ (1 / 2) * gridCovarianceError b E n := by
  filter_upwards [hLogBias, eventually_ge_atTop 2] with n hB hn
  have hlogpos : (0 : ℝ) < 2 * Real.log (n : ℝ) := by
    have h1 : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    linarith
  have hne : (2 : ℝ) * Real.log (n : ℝ) ≠ 0 := ne_of_gt hlogpos
  have hsplit : (cσ - EG n) / (2 * Real.log (n : ℝ)) - h
      = -(EG n - (cσ - 2 * h * Real.log (n : ℝ))) / (2 * Real.log (n : ℝ)) := by
    rw [div_sub' hne]
    congr 1
    ring
  rw [hsplit, neg_div, abs_neg, abs_div, abs_of_pos hlogpos]
  have key : |EG n - (cσ - 2 * h * Real.log (n : ℝ))| / (2 * Real.log (n : ℝ))
      ≤ (1 / 2) * gridCovarianceError b E n := by
    rw [div_le_iff₀ hlogpos]
    calc |EG n - (cσ - 2 * h * Real.log (n : ℝ))|
        ≤ Real.log (n : ℝ) * gridCovarianceError b E n := hB
      _ = (1 / 2) * gridCovarianceError b E n * (2 * Real.log (n : ℝ)) := by ring
  exact key

/-- **File 24 E5: the bias envelope for the clipped known-scale H estimator.**

Ordinary model (a probability space per `n`), feasible bandwidth `δ n = n^{-γ}`,
and the weight/profile hypotheses as packaged by the landed layers:

* `hBias` — the calibrated untruncated-H bias at the grid-error rate
  (`gridCovarianceError / 2`; exactly what `e5_calibratedBias_of_logBias` lands
  from the log-statistic bias of
  `Hurst.FirstScaleLongBias.hurstHolder_q1_linearScale_bias_lt_one`);
* `hFluct` — the mean-centered L1 fluctuation `E|X_n - E X_n| ≤ F n^{-γ}`
  (the variance layer; NOT a bias — the clip `p5Trunc01` is not affine, so the
  expectation of the clipped estimator sees it).

Conclusion: `∃ C ≥ 0, ∀ᶠ n, |E[Ĥ_n] - h| ≤ C n^{-γ}` — the clean bandwidth-power
envelope consumed by `Hurst.P5TruthCenter.drift_condition_s1` (no residual log
factor, per `gridCovarianceError_le_const_rpow` and the window `γ + 2 b < 2`). -/
theorem e5_bias_envelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω} [∀ n : ℕ, IsProbabilityMeasure (μ n)]
    {X : ℕ → Ω → ℝ} (h : ℝ) (E b γ F : ℝ)
    (hh : h ∈ Icc 0 1) (hb : b < 1)
    (hγpos : 0 < γ) (hγlt : γ < 1) (hγb : γ + 2 * b < 2)
    (hXint : ∀ n : ℕ, Integrable (X n) (μ n))
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ x, X n x ∂μ n - h| ≤ (1 / 2) * gridCovarianceError b E n)
    (hFluct : ∀ᶠ n : ℕ in atTop,
      ∫ x, |X n x - ∫ y, X n y ∂μ n| ∂μ n ≤ F * (n : ℝ) ^ (-γ)) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |∫ x, p5Trunc01 (X n x) ∂μ n - h| ≤ C * (n : ℝ) ^ (-γ) := by
  obtain ⟨Cg, hCg0, hCg⟩ := gridCovarianceError_le_const_rpow b E γ hb hγpos hγlt hγb
  refine ⟨F + Cg / 2, by linarith, ?_⟩
  filter_upwards [hBias, hFluct, hCg] with n hB hF1 hGr
  have key := p5Trunc01_expectation_dist (hXint n) h hh
  refine key.trans ?_
  have hbias : |(∫ y, X n y ∂μ n) - h| ≤ (1 / 2) * (Cg * (n : ℝ) ^ (-γ)) :=
    hB.trans (mul_le_mul_of_nonneg_left hGr (by norm_num))
  calc ∫ x, |X n x - (∫ y, X n y ∂μ n)| ∂μ n + |(∫ y, X n y ∂μ n) - h|
      ≤ F * (n : ℝ) ^ (-γ) + (1 / 2) * (Cg * (n : ℝ) ^ (-γ)) := add_le_add hF1 hbias
    _ = (F + Cg / 2) * (n : ℝ) ^ (-γ) := by ring

/-- **The E5 drift condition from the bias envelope** — composition with
`Hurst.P5TruthCenter.drift_condition_s1`: under the E5 window
`(1 - γ) * ψ < γ * 1` the truth-centering drift
`|2 n^{ψ (1 - γ)} log n * (E Ĥ_n - h)|` tends to zero.  This closes the
truth-centering (file 24 E4) under the ordinary model + feasible bandwidth
`δ n = n^{-γ}` + the grid-error window `γ + 2 b < 2` + the fluctuation layer. -/
theorem e5_drift_of_bias_envelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω} [∀ n : ℕ, IsProbabilityMeasure (μ n)]
    {X : ℕ → Ω → ℝ} (h : ℝ) (E b γ F ψ : ℝ)
    (hh : h ∈ Icc 0 1) (hb : b < 1)
    (hγpos : 0 < γ) (hγlt : γ < 1) (hγb : γ + 2 * b < 2)
    (hψpos : 0 < ψ) (hE5 : (1 - γ) * ψ < γ * 1)
    (hXint : ∀ n : ℕ, Integrable (X n) (μ n))
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ x, X n x ∂μ n - h| ≤ (1 / 2) * gridCovarianceError b E n)
    (hFluct : ∀ᶠ n : ℕ in atTop,
      ∫ x, |X n x - ∫ y, X n y ∂μ n| ∂μ n ≤ F * (n : ℝ) ^ (-γ)) (hF : 0 ≤ F) :
    Tendsto (fun n : ℕ =>
      |2 * (n : ℝ) ^ (ψ * (1 - γ)) * Real.log n *
        (∫ x, p5Trunc01 (X n x) ∂μ n - h)|) atTop (𝓝 0) := by
  obtain ⟨C, hC, henv⟩ :=
    e5_bias_envelope h E b γ F hh hb hγpos hγlt hγb hXint hBias hFluct hF
  exact drift_condition_s1 h (fun n => ∫ x, p5Trunc01 (X n x) ∂μ n) γ ψ
    hγpos hγlt hψpos hE5 C hC henv

end Hurst
