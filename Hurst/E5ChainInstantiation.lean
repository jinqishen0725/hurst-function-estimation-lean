import Hurst.E5FluctuationFinisher
import Hurst.P5LogHLayers
import Hurst.P7RowBound
import Hurst.GridErrorRate
import Hurst.GaussianLog
import Hurst.GaussianLogRisk

/-!
# E5 fluctuation: the INSTANTIATION at the literal P5 chain statistic

`Hurst.E5FluctuationFinisher.e5_fluctuation_discharged` packages the E5
mean-fluctuation discharge over an ABSTRACT probability family `μ n` and an
abstract statistic `X n`.  This module instantiates it at the LITERAL P5 chain
objects:

* the statistic `X_n := chainCalibratedStatistic f r n (δ n) t cσ
  = (cσ - Ĝ_n) / (2 * log n)`, the known-scale calibration of the literal chain
  log statistic `Ĝ_n := chainLogStatistic f r n (δ n) t
  = gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
      (actualQ1Coeff n (δ n) t)`
  (the same calibration shape as the landed `Hurst.P5LogHLayers` pointwise
  identity `p5_YX_identity`: `X = (cσ - S^{-ψ} sx) / (2 L)` with
  `Ĝ_spec = S^ψ sx`);
* the measure `μ n := featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))`.

Because the chain lives on the n-DEPENDENT type `EuclideanSpace ℝ (Fin n)`, the
abstract finisher (one fixed `Ω` for all `n`) cannot be applied verbatim; we
first clone it with dependent types (`e5c_fluctuation_discharged_dep`, proof
verbatim) and instantiate THAT.

## What discharges from landed facts

* `MemLp` of the literal log statistic: `gaussianLogStatistic_memLp_two`
  (`Hurst.GaussianLog`); `MemLp` of the calibrated statistic follows by affine
  closure (`MemLp.sub`, `MemLp.neg`, `MemLp.const_mul`,
  `chainCalibratedStatistic_memLp_two`).
* `Var(Ĝ_n) = O(spectral-weight energy)`:
  `gaussianLogStatistic_variance_correlation_bound` (`Hurst.GaussianLogRisk`)
  gives `Var ≤ 4 * gaussianLogSquareVariance * ∑∑ |w_j| |w_k| corr_{jk}²`, and
  `chainLogStatistic_variance_energy` bounds the energy by
  `card * ∑ w_spec²` (each chain correlation is at most `1` in absolute value,
  unconditionally, and `(∑ |w|)² ≤ card * ∑ w²` by Cauchy–Schwarz
  `sq_sum_le_card_mul_sum_sq`).
* The calibration layer `e5c_calibration_centered_integral`:
  `E|X_n - E X_n| = (2 log n)^{-1} E|Ĝ_n - E Ĝ_n|`, so the L1 ≤ L2 route gives
  `E|X_n - E X_n| ≤ (2 log n)^{-1} √Var(Ĝ_n)`.

## Main statements

* `e5_fluctuation_at_chain` — the E5 fluctuation at the literal objects: an
  eventually-polynomial spectral-energy input in the rate form
  `∑∑ |w_j||w_k| corr² ≤ E · n^{-2γ} (log n)²` yields
  `∃ F ≥ 0, ∀ᶠ n, E|X_n - E X_n| ≤ F n^{-γ}` with the explicit
  `F = √(4 gaussianLogSquareVariance E) / 2`.
* `e5_chain_fluctuation_discharged_window` — the windowed variant: inside the
  finisher's feasible window (`3/4 ≤ b < 1`, `0 < γ ≤ 1 - b`) a variance bound
  at the literal calibrated chain statistic in EXACTLY the shape of the landed
  `hurstHolder_q1_linearScale_variance_lt_one` yields the same conclusion.
* `e5_chain_calibrated_fluctuation_tendsto_zero` — the long-window corollary:
  under the ordinary bandwidth data, `hW0/hU`-shape bounded chain weights, and
  the long-memory band `3/4 < f t` (so `ψ = 2 - 2 f t < 1/2` and
  `∑ w_spec² = S^{2ψ-2} ∑ u²`, whence `S · ∑ w_spec² = S^{2ψ-1} → 0`), the
  calibrated L1 fluctuation tends to `0`.

## Gaps (documented deviations)

1. Energy-to-rate bridge: the landed `hE2` shape bounds the correlation energy
   by a CONSTANT; a polynomial rate `n^{-2γ} (log n)²` for
   `∑∑ |w_j||w_k| corr²` is therefore an explicit hypothesis of
   `e5_fluctuation_at_chain` (in the spirit of the verbatim `hW0/hE2` inputs
   of `actualQ1_logStatistic_tendsto_secondChaos_of_quadratic`).  Deriving
   that rate from the P7 row-bound machinery requires the
   spectral-energy-to-`firstStrideLongRowBound` link, which is NOT landed.
2. `e5_chain_fluctuation_discharged_window` keeps the variance bound (in the
   exact landed shape) as an explicit hypothesis at the literal objects: the
   constants `A_i, C_i, D_i` of `hurstHolder_q1_linearScale_variance_lt_one`
   are proved for the unit-sum statistic `q1LinearScale`, not for the spectral
   statistic; transporting them is the same missing energy-to-row-bound link.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Hurst

/-! ### Elementary helpers (the finisher's private helpers, restated here) -/

/-- √-subadditivity: `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
private theorem e5c_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hx' := Real.sqrt_nonneg x
  have hy' := Real.sqrt_nonneg y
  have h1 : (Real.sqrt x + Real.sqrt y) ^ 2
      = x + y + 2 * Real.sqrt x * Real.sqrt y := by
    rw [pow_two, mul_add, add_mul, add_mul,
      Real.mul_self_sqrt hx, Real.mul_self_sqrt hy]
    ring
  have hle : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    rw [h1]
    linarith [mul_nonneg hx' hy']
  have h2 := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ Real.sqrt x + Real.sqrt y)] at h2

/-- **L1 ≤ L2 on a probability space**: `E|g| ≤ √(E g²)`. -/
private theorem e5c_integral_abs_le_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Integrable g μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    ∫ x, |g x| ∂μ ≤ Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hs0 : 0 ≤ ∫ x, |g x| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have hpw : ∀ x : Ω,
      (2 * ∫ y, |g y| ∂μ) * |g x| ≤ (∫ y, |g y| ∂μ) ^ 2 + g x ^ 2 := by
    intro x
    have h2 : (2 * ∫ y, |g y| ∂μ) * |g x|
        ≤ (∫ y, |g y| ∂μ) ^ 2 + |g x| ^ 2 := by
      nlinarith [sq_nonneg ((∫ y, |g y| ∂μ) - |g x|)]
    rwa [sq_abs] at h2
  have hdom : Integrable (fun x => (∫ y, |g y| ∂μ) ^ 2 + g x ^ 2) μ :=
    (integrable_const _).add hg2
  have hint1 : Integrable (fun x => (2 * ∫ y, |g y| ∂μ) * |g x|) μ :=
    hg.abs.const_mul (2 * ∫ y, |g y| ∂μ)
  have hmono := integral_mono hint1 hdom hpw
  have hL : ∫ x, (2 * ∫ y, |g y| ∂μ) * |g x| ∂μ
      = 2 * (∫ y, |g y| ∂μ) * (∫ y, |g y| ∂μ) := by
    rw [integral_const_mul]
  have hR : ∫ x, (∫ y, |g y| ∂μ) ^ 2 + g x ^ 2 ∂μ
      = (∫ y, |g y| ∂μ) ^ 2 + ∫ x, g x ^ 2 ∂μ := by
    rw [integral_add (integrable_const _) hg2]
    simp
  rw [hL, hR] at hmono
  have hkey : (∫ x, |g x| ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
    nlinarith [hmono, hs0]
  calc ∫ x, |g x| ∂μ = Real.sqrt ((∫ x, |g x| ∂μ) ^ 2) := (Real.sqrt_sq hs0).symm
    _ ≤ Real.sqrt (∫ x, g x ^ 2 ∂μ) := Real.sqrt_le_sqrt hkey

/-- **The mean-centered L1 mass is at most the standard deviation.** -/
private theorem e5c_integral_abs_le_sqrt_var {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ x, |X x - ∫ y, X y ∂μ| ∂μ ≤ Real.sqrt (Var[X; μ]) := by
  have hc : MemLp (fun x => X x - ∫ y, X y ∂μ) 2 μ := hX.sub (memLp_const _)
  rw [ProbabilityTheory.variance_eq_integral hX.aemeasurable]
  exact e5c_integral_abs_le_sq (hc.integrable (by norm_num)) hc.integrable_sq

/-- `√(x ^ e) = x ^ (e / 2)`. -/
private theorem e5c_sqrt_rpow (x : ℝ) (hx : 0 ≤ x) (e : ℝ) :
    Real.sqrt (x ^ e) = x ^ (e / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

/-- `(x ^ e) ^ 2 = x ^ (2 * e)`. -/
private theorem e5c_rpow_sq (x : ℝ) (hx : 0 ≤ x) (e : ℝ) :
    (x ^ e) ^ 2 = x ^ (2 * e) := by
  rw [← Real.rpow_natCast (x := x ^ e) (n := 2), ← Real.rpow_mul hx]
  congr 1
  ring

/-- `x * x ^ e = x ^ (1 + e)`. -/
private theorem e5c_rpow_mul_one_add (x : ℝ) (hx : 0 < x) (e : ℝ) :
    x * x ^ e = x ^ (1 + e) := by
  rw [Real.rpow_add hx 1 e, Real.rpow_one]

/-- Division/inverse algebra of the calibration (valid also at `s = 0`). -/
private theorem e5c_inv_mul_neg_div (c x s : ℝ) : s⁻¹ * -(x - c) = (c - x) / s := by
  by_cases hs : s = 0
  · subst hs
    simp
  · field_simp
    ring

/-- The double-sum weight energy is at most `card * ∑ w²`
(`(∑ |w|)² ≤ card * ∑ w²`, Cauchy–Schwarz/Jensen). -/
private theorem e5c_energy_card_sq {κ : Type*} [Fintype κ] (w : κ → ℝ) :
    ∑ j : κ, ∑ k : κ, |w j| * |w k| ≤ (Fintype.card κ : ℝ) * ∑ i : κ, w i ^ 2 := by
  have habseq : ∑ i : κ, |w i| ^ 2 = ∑ i : κ, w i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq_abs _
  calc ∑ j : κ, ∑ k : κ, |w j| * |w k| = (∑ j : κ, |w j|) * (∑ k : κ, |w k|) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ i : κ, |w i|) ^ 2 := by rw [pow_two]
    _ ≤ (Fintype.card κ : ℝ) * ∑ i : κ, |w i| ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = (Fintype.card κ : ℝ) * ∑ i : κ, w i ^ 2 := by rw [habseq]

/-! ### The literal P5 chain objects and their calibration -/

/-- The literal chain log statistic `Ĝ_n` of the P5 chain: the log statistic
with the SPECTRAL weights `S^{ψ-1} u_{n,i}` (the statistic whose centered law
is identified in `Hurst.P5LogHLayers`). -/
def chainLogStatistic (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  gaussianLogStatistic
    (actualQ1SpectralWeight f r n δ t) (actualQ1Coeff n δ t) x

/-- The known-scale calibration of the chain log statistic:
`X_n = (cσ - Ĝ_n) / (2 log n)` — the same calibration shape as
`Hurst.P5LogHLayers.p5KnownScaleHtilde`, at the spectral statistic. -/
def chainCalibratedStatistic (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ) (cσ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (cσ - chainLogStatistic f r n δ t x) / (2 * Real.log n)

/-- The chain log statistic is L² on the literal feature-Gaussian model (the
landed `gaussianLogStatistic_memLp_two`, verbatim). -/
theorem chainLogStatistic_memLp_two (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    {H : Fin n → Ioo (0 : ℝ) 1}
    (hane : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t k i • actualQ1Obs f n H i ≠ 0) :
    MemLp (chainLogStatistic f r n δ t) 2 (featureGaussian (actualQ1Obs f n H)) :=
  gaussianLogStatistic_memLp_two _ _ _ hane

/-- The calibrated chain statistic is L² on the literal feature-Gaussian model
(affine closure of `chainLogStatistic_memLp_two`; at `n = 1` the calibration
degenerates to the zero map, which is harmless). -/
theorem chainCalibratedStatistic_memLp_two (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (cσ : ℝ) {H : Fin n → Ioo (0 : ℝ) 1}
    (hane : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t k i • actualQ1Obs f n H i ≠ 0) :
    MemLp (chainCalibratedStatistic f r n δ t cσ) 2
      (featureGaussian (actualQ1Obs f n H)) := by
  have hG := chainLogStatistic_memLp_two f r n δ t hane
  have hsub := hG.sub (memLp_const (cσ : ℝ))
  refine MemLp.ae_eq (Eventually.of_forall fun x => ?_)
    (hsub.neg.const_mul ((2 * Real.log n)⁻¹))
  exact e5c_inv_mul_neg_div cσ (chainLogStatistic f r n δ t x) (2 * Real.log n)

/-! ### The calibration layer -/

/-- **The calibration centering rule.**  For `s > 0` the mean-centered L1 mass
is scale-equivariant: `E|(cσ - Ĝ)/s - E((cσ - Ĝ)/s)| = s⁻¹ · E|Ĝ - E Ĝ|`. -/
theorem e5c_calibration_centered_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Ω → ℝ} (c s : ℝ) (hs : 0 < s)
    (hG : MemLp G 2 μ) :
    ∫ x, |(c - G x) / s - ∫ y, (c - G y) / s ∂μ| ∂μ
      = s⁻¹ * ∫ x, |G x - ∫ y, G y ∂μ| ∂μ := by
  have hint : ∫ y, (c - G y) / s ∂μ = (c - ∫ y, G y ∂μ) / s := by
    have hfun : (fun y => (c - G y) / s) = fun y => s⁻¹ * (c - G y) := by
      funext y
      rw [div_eq_inv_mul]
    rw [hfun, integral_const_mul,
      integral_sub (integrable_const c) (hG.integrable (by norm_num))]
    simp
    rw [div_eq_inv_mul]
  have hpt : (fun x => |(c - G x) / s - ∫ y, (c - G y) / s ∂μ|)
      = fun x => s⁻¹ * |G x - ∫ y, G y ∂μ| := by
    funext x
    rw [hint]
    have hstep : (c - G x) / s - (c - ∫ y, G y ∂μ) / s
        = s⁻¹ * -(G x - ∫ y, G y ∂μ) := by
      have hnum : (c - G x) - (c - ∫ y, G y ∂μ)
          = ∫ y, G y ∂μ - G x := by ring
      rw [div_sub_div_same, hnum, ← e5c_inv_mul_neg_div]
    rw [hstep, abs_mul, abs_inv, abs_of_pos hs, abs_neg]
  rw [hpt, integral_const_mul]

/-! ### The dependent-type clone of the fluctuation discharge -/

/-- **The E5 mean-fluctuation discharge, over n-dependent probability spaces**
(the type-generalized clone of
`Hurst.E5FluctuationFinisher.e5_fluctuation_discharged`: the chain lives on
`EuclideanSpace ℝ (Fin n)`, so one fixed `Ω` cannot carry all the `μ n`).
Same hypotheses, same conclusion; the per-`n` proof is verbatim. -/
theorem e5c_fluctuation_discharged_dep {Ωd : ℕ → Type*}
    [∀ n : ℕ, MeasurableSpace (Ωd n)]
    {μ : (n : ℕ) → Measure (Ωd n)} [∀ n : ℕ, IsProbabilityMeasure (μ n)]
    {X : (n : ℕ) → Ωd n → ℝ}
    (b C₁ A₁ D₁ C₂ A₂ D₂ γ : ℝ)
    (hb34 : 3 / 4 ≤ b) (hb : b < 1)
    (hC₁ : 0 ≤ C₁) (hD₁ : 0 ≤ D₁) (hC₂ : 0 ≤ C₂) (hD₂ : 0 ≤ D₂)
    (hγpos : 0 < γ) (hγb : γ ≤ 1 - b)
    (hX2 : ∀ n : ℕ, MemLp (X n) 2 (μ n))
    (hVar : ∀ᶠ n : ℕ in atTop,
      Var[X n; μ n] ≤ (1 / 4) * ((4 + 4 / (Real.log 2) ^ 2) *
        (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
         D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n))) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop,
      ∫ x, |X n x - ∫ y, X n y ∂μ n| ∂μ n ≤ F * (n : ℝ) ^ (-γ) := by
  -- the row-bound split (valid for every n ≥ 1)
  obtain ⟨Cv₁, hCv₁₀, hs1⟩ :=
    p7_firstStrideLongRowBound_div_n_le b C₁ A₁ 1 hb (by norm_num)
  obtain ⟨Cv₂, hCv₂₀, hs2⟩ :=
    p7_firstStrideLongRowBound_div_n_le b C₂ A₂ 2 hb (by norm_num)
  -- the grid-covariance error at rate n^{-γ} (the bias-envelope window is subsumed)
  have hb0 : 0 < b := by linarith
  have hγlt : γ < 1 := by linarith
  have hγ2 : γ + 2 * b < 2 := by linarith
  obtain ⟨Cg₁, hCg₁₀, hCg₁⟩ := gridCovarianceError_le_const_rpow b C₁ γ hb hγpos hγlt hγ2
  obtain ⟨Cg₂, hCg₂₀, hCg₂⟩ := gridCovarianceError_le_const_rpow b C₂ γ hb hγpos hγlt hγ2
  have hK0 : 0 ≤ (4 : ℝ) + 4 / (Real.log 2) ^ 2 := by
    have h2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hsq : (0 : ℝ) < Real.log 2 ^ 2 := pow_pos h2pos 2
    have hinv : (0 : ℝ) ≤ (Real.log 2 ^ 2)⁻¹ := (inv_pos.mpr hsq).le
    have hdiv : (4 : ℝ) / Real.log 2 ^ 2 = 4 * (Real.log 2 ^ 2)⁻¹ := by ring
    rw [hdiv]
    linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hinv]
  have hDCv0 : 0 ≤ D₁ * Cv₁ + D₂ * Cv₂ := by
    have p1 : 0 ≤ D₁ * Cv₁ := mul_nonneg hD₁ hCv₁₀
    have p2 : 0 ≤ D₂ * Cv₂ := mul_nonneg hD₂ hCv₂₀
    linarith
  refine ⟨Real.sqrt (4 + 4 / (Real.log 2) ^ 2) / 2 *
    (3 * Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂)
      + Real.sqrt 32 * (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂)), ?_, ?_⟩
  · -- F ≥ 0
    have s1 : 0 ≤ Real.sqrt (4 + 4 / (Real.log 2) ^ 2) := Real.sqrt_nonneg _
    have s2 : 0 ≤ Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) := Real.sqrt_nonneg _
    have s3 : 0 ≤ Real.sqrt 32 := Real.sqrt_nonneg _
    have s4 : 0 ≤ Real.sqrt D₁ := Real.sqrt_nonneg _
    have s5 : 0 ≤ Real.sqrt D₂ := Real.sqrt_nonneg _
    have t : 0 ≤ 3 * Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂)
        + Real.sqrt 32 * (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂) := by
      have a1 : 0 ≤ Real.sqrt D₁ * Cg₁ := mul_nonneg s4 hCg₁₀
      have a2 : 0 ≤ Real.sqrt D₂ * Cg₂ := mul_nonneg s5 hCg₂₀
      have a3 : 0 ≤ Real.sqrt 32 * (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂) :=
        mul_nonneg s3 (add_nonneg a1 a2)
      linarith
    exact mul_nonneg (div_nonneg s1 (by norm_num)) t
  · filter_upwards [hVar, hCg₁, hCg₂, eventually_ge_atTop 1] with n hV hG₁ hG₂ hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    -- step 1: E|X_n - E X_n| ≤ √Var[X_n]
    have hL1 := e5c_integral_abs_le_sqrt_var (hX2 n)
    -- step 2: the row-bound split on the variance shape
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℕ) < n by omega)
    have hrow₁ : 0 ≤ firstStrideLongRowBound b C₁ A₁ 1 n := by
      unfold firstStrideLongRowBound gridCovarianceError
      positivity
    have hrow₂ : 0 ≤ firstStrideLongRowBound b C₂ A₂ 2 n := by
      unfold firstStrideLongRowBound gridCovarianceError
      positivity
    set S : ℝ := D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
      D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n with hS_def
    have hS0 : 0 ≤ S := by
      rw [hS_def]
      exact add_nonneg (mul_nonneg (div_nonneg hD₁ hnR.le) hrow₁)
        (mul_nonneg (div_nonneg hD₂ hnR.le) hrow₂)
    set R : ℝ := (n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)
      with hR_def
    have hR0 : 0 ≤ R := by
      rw [hR_def]
      exact add_nonneg (add_nonneg (Real.rpow_nonneg hnR.le _)
        (Real.rpow_nonneg hnR.le _)) (Real.rpow_nonneg hnR.le _)
    have hDCv : 0 ≤ D₁ * Cv₁ + D₂ * Cv₂ := hDCv0
    have hg₁0 : 0 ≤ gridCovarianceError b C₁ n := p7_gridCovarianceError_nonneg b C₁ hC₁ n
    have hg₂0 : 0 ≤ gridCovarianceError b C₂ n := p7_gridCovarianceError_nonneg b C₂ hC₂ n
    have hsq1 : 0 ≤ D₁ * gridCovarianceError b C₁ n ^ 2 := mul_nonneg hD₁ (sq_nonneg _)
    have hsq2 : 0 ≤ D₂ * gridCovarianceError b C₂ n ^ 2 := mul_nonneg hD₂ (sq_nonneg _)
    -- f1/f2: each row bound through the split (shape-matched)
    have f1 : D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n
        ≤ D₁ * Cv₁ * R + 32 * (D₁ * gridCovarianceError b C₁ n ^ 2) := by
      have hrew : D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n
          = D₁ * (firstStrideLongRowBound b C₁ A₁ 1 n / (n : ℝ)) := by ring
      rw [hrew]
      have hsp := hs1 n hn
      rw [← hR_def] at hsp
      linarith [mul_le_mul_of_nonneg_left hsp hD₁]
    have f2 : D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n
        ≤ D₂ * Cv₂ * R + 32 * (D₂ * gridCovarianceError b C₂ n ^ 2) := by
      have hrew : D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n
          = D₂ * (firstStrideLongRowBound b C₂ A₂ 2 n / (n : ℝ)) := by ring
      rw [hrew]
      have hsp := hs2 n hn
      rw [← hR_def] at hsp
      linarith [mul_le_mul_of_nonneg_left hsp hD₂]
    have hSle : S ≤ (D₁ * Cv₁ + D₂ * Cv₂) * R
        + 32 * (D₁ * gridCovarianceError b C₁ n ^ 2
          + D₂ * gridCovarianceError b C₂ n ^ 2) := by
      calc S = D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n
            + D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n := hS_def.symm
        _ ≤ D₁ * Cv₁ * R + 32 * (D₁ * gridCovarianceError b C₁ n ^ 2)
            + (D₂ * Cv₂ * R + 32 * (D₂ * gridCovarianceError b C₂ n ^ 2)) :=
              add_le_add f1 f2
        _ = (D₁ * Cv₁ + D₂ * Cv₂) * R
            + 32 * (D₁ * gridCovarianceError b C₁ n ^ 2
              + D₂ * gridCovarianceError b C₂ n ^ 2) := by ring
    -- step 3: the square-root chain
    have hsqrtS : Real.sqrt S ≤ Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * (3 * (n : ℝ) ^ (-(1 - b)))
        + Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n
          + Real.sqrt D₂ * gridCovarianceError b C₂ n) := by
      have h32 : 0 ≤ (32 : ℝ) * (D₁ * gridCovarianceError b C₁ n ^ 2
          + D₂ * gridCovarianceError b C₂ n ^ 2) :=
        mul_nonneg (by norm_num) (add_nonneg hsq1 hsq2)
      have hsplit0 : 0 ≤ 32 * (D₁ * gridCovarianceError b C₁ n ^ 2
          + D₂ * gridCovarianceError b C₂ n ^ 2) := h32
      have htermA : Real.sqrt ((D₁ * Cv₁ + D₂ * Cv₂) * R)
          = Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * Real.sqrt R := Real.sqrt_mul hDCv _
      have htermB : Real.sqrt (32 * (D₁ * gridCovarianceError b C₁ n ^ 2))
          = Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n) := by
        rw [show (32 : ℝ) * (D₁ * gridCovarianceError b C₁ n ^ 2)
            = (32 * D₁) * gridCovarianceError b C₁ n ^ 2 from by ring,
          Real.sqrt_mul (mul_nonneg (by norm_num) hD₁),
          Real.sqrt_sq_eq_abs, abs_of_nonneg hg₁0,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32)]
        ring
      have htermC : Real.sqrt (32 * (D₂ * gridCovarianceError b C₂ n ^ 2))
          = Real.sqrt 32 * (Real.sqrt D₂ * gridCovarianceError b C₂ n) := by
        rw [show (32 : ℝ) * (D₂ * gridCovarianceError b C₂ n ^ 2)
            = (32 * D₂) * gridCovarianceError b C₂ n ^ 2 from by ring,
          Real.sqrt_mul (mul_nonneg (by norm_num) hD₂),
          Real.sqrt_sq_eq_abs, abs_of_nonneg hg₂0,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32)]
        ring
      have hSR : Real.sqrt ((D₁ * Cv₁ + D₂ * Cv₂) * R
          + 32 * (D₁ * gridCovarianceError b C₁ n ^ 2
            + D₂ * gridCovarianceError b C₂ n ^ 2))
          ≤ Real.sqrt ((D₁ * Cv₁ + D₂ * Cv₂) * R)
            + Real.sqrt (32 * (D₁ * gridCovarianceError b C₁ n ^ 2
              + D₂ * gridCovarianceError b C₂ n ^ 2)) :=
        e5c_sqrt_add_le _ _ (mul_nonneg hDCv hR0) hsplit0
      have hinner : Real.sqrt (32 * (D₁ * gridCovarianceError b C₁ n ^ 2
            + D₂ * gridCovarianceError b C₂ n ^ 2))
          ≤ Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n)
            + Real.sqrt 32 * (Real.sqrt D₂ * gridCovarianceError b C₂ n) := by
        have h1 := e5c_sqrt_add_le (32 * (D₁ * gridCovarianceError b C₁ n ^ 2))
          (32 * (D₂ * gridCovarianceError b C₂ n ^ 2))
          (mul_nonneg (by norm_num) hsq1) (mul_nonneg (by norm_num) hsq2)
        rw [htermB, htermC] at h1
        rw [mul_add]
        exact h1
      have hsqrtR : Real.sqrt R ≤ 3 * (n : ℝ) ^ (-(1 - b)) := by
        have h1 : Real.sqrt R ≤ Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ))
            + Real.sqrt ((n : ℝ) ^ (2 * b - 2)) :=
          e5c_sqrt_add_le _ _ (add_nonneg (Real.rpow_nonneg hnR.le _)
            (Real.rpow_nonneg hnR.le _)) (Real.rpow_nonneg hnR.le _)
        have h2 : Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ))
            ≤ Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)) + Real.sqrt ((n : ℝ) ^ (-1 : ℝ)) :=
          e5c_sqrt_add_le _ _ (Real.rpow_nonneg hnR.le _) (Real.rpow_nonneg hnR.le _)
        linarith [p7_sqrt_rpow_sum_le_mesh b hb34 hb n hn, h1, h2]
      calc Real.sqrt S
          ≤ Real.sqrt ((D₁ * Cv₁ + D₂ * Cv₂) * R
              + 32 * (D₁ * gridCovarianceError b C₁ n ^ 2
                + D₂ * gridCovarianceError b C₂ n ^ 2)) := Real.sqrt_le_sqrt hSle
        _ ≤ Real.sqrt ((D₁ * Cv₁ + D₂ * Cv₂) * R)
            + Real.sqrt (32 * (D₁ * gridCovarianceError b C₁ n ^ 2
              + D₂ * gridCovarianceError b C₂ n ^ 2)) := hSR
        _ = Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * Real.sqrt R
            + Real.sqrt (32 * (D₁ * gridCovarianceError b C₁ n ^ 2
              + D₂ * gridCovarianceError b C₂ n ^ 2)) := by rw [htermA]
        _ ≤ Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * (3 * (n : ℝ) ^ (-(1 - b)))
            + (Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n)
              + Real.sqrt 32 * (Real.sqrt D₂ * gridCovarianceError b C₂ n)) := by
            refine add_le_add (mul_le_mul_of_nonneg_left hsqrtR
              (Real.sqrt_nonneg _)) hinner
        _ = Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * (3 * (n : ℝ) ^ (-(1 - b)))
            + Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n
              + Real.sqrt D₂ * gridCovarianceError b C₂ n) := by ring
    -- step 4: absorb n^{-(1-b)} into n^{-γ} and the grid errors into n^{-γ}
    have hexp : (n : ℝ) ^ (-(1 - b)) ≤ (n : ℝ) ^ (-γ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hγ0 : 0 ≤ (n : ℝ) ^ (-γ) := Real.rpow_nonneg hnR.le _
    have t1 : Real.sqrt D₁ * gridCovarianceError b C₁ n
        ≤ Real.sqrt D₁ * (Cg₁ * (n : ℝ) ^ (-γ)) :=
      mul_le_mul_of_nonneg_left hG₁ (Real.sqrt_nonneg _)
    have t2 : Real.sqrt D₂ * gridCovarianceError b C₂ n
        ≤ Real.sqrt D₂ * (Cg₂ * (n : ℝ) ^ (-γ)) :=
      mul_le_mul_of_nonneg_left hG₂ (Real.sqrt_nonneg _)
    have hbnd : Real.sqrt (Var[X n; μ n])
        ≤ Real.sqrt (4 + 4 / (Real.log 2) ^ 2) / 2 *
          (3 * Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂)
            + Real.sqrt 32 * (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂))
          * (n : ℝ) ^ (-γ) := by
      rw [ProbabilityTheory.variance_eq_integral (hX2 n).aemeasurable]
      have hV' : ∫ x, (X n x - ∫ y, X n y ∂μ n) ^ 2 ∂μ n
          ≤ (1 / 4) * ((4 + 4 / (Real.log 2) ^ 2) * S) := by
        rw [← ProbabilityTheory.variance_eq_integral (hX2 n).aemeasurable]
        exact hV
      have hstep1 : Real.sqrt (∫ x, (X n x - ∫ y, X n y ∂μ n) ^ 2 ∂μ n)
          ≤ Real.sqrt ((1 / 4) * ((4 + 4 / (Real.log 2) ^ 2) * S)) :=
        Real.sqrt_le_sqrt hV'
      have hstep2 : Real.sqrt ((1 / 4) * ((4 + 4 / (Real.log 2) ^ 2) * S))
          = Real.sqrt (4 + 4 / (Real.log 2) ^ 2) / 2 * Real.sqrt S := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
          show Real.sqrt ((1 : ℝ) / 4) = 1 / 2 from by
            have hq : ((1 : ℝ) / 4) = (1 / 2 : ℝ) ^ 2 := by norm_num
            rw [hq, Real.sqrt_sq_eq_abs]
            norm_num,
          Real.sqrt_mul hK0]
        ring
      have hmid : Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * (3 * (n : ℝ) ^ (-(1 - b)))
          + Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n
            + Real.sqrt D₂ * gridCovarianceError b C₂ n)
          ≤ (3 * Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂)
            + Real.sqrt 32 * (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂))
            * (n : ℝ) ^ (-γ) := by
        have u1 : Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * 3 * (n : ℝ) ^ (-(1 - b))
            ≤ Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * 3 * (n : ℝ) ^ (-γ) :=
          mul_le_mul_of_nonneg_left hexp
            (mul_nonneg (Real.sqrt_nonneg _) (by norm_num))
        have u2 : Real.sqrt D₁ * (Cg₁ * (n : ℝ) ^ (-γ))
            + Real.sqrt D₂ * (Cg₂ * (n : ℝ) ^ (-γ))
            ≤ (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂) * (n : ℝ) ^ (-γ) := by
          nlinarith [Real.sqrt_nonneg D₁, Real.sqrt_nonneg D₂, hγ0]
        have u4 : Real.sqrt D₁ * gridCovarianceError b C₁ n
              + Real.sqrt D₂ * gridCovarianceError b C₂ n
            ≤ Real.sqrt D₁ * (Cg₁ * (n : ℝ) ^ (-γ))
              + Real.sqrt D₂ * (Cg₂ * (n : ℝ) ^ (-γ)) := by
          nlinarith [t1, t2, hg₁0, hg₂0, Real.sqrt_nonneg D₁, Real.sqrt_nonneg D₂]
        have u3 : Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n
              + Real.sqrt D₂ * gridCovarianceError b C₂ n)
            ≤ Real.sqrt 32 * (Real.sqrt D₁ * (Cg₁ * (n : ℝ) ^ (-γ))
              + Real.sqrt D₂ * (Cg₂ * (n : ℝ) ^ (-γ))) :=
          mul_le_mul_of_nonneg_left u4 (Real.sqrt_nonneg _)
        calc Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * (3 * (n : ℝ) ^ (-(1 - b)))
              + Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n
                + Real.sqrt D₂ * gridCovarianceError b C₂ n)
            ≤ Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * 3 * (n : ℝ) ^ (-γ)
              + Real.sqrt 32 * (Real.sqrt D₁ * (Cg₁ * (n : ℝ) ^ (-γ))
                + Real.sqrt D₂ * (Cg₂ * (n : ℝ) ^ (-γ))) := by
              nlinarith [u1, u3, Real.sqrt_nonneg 32, hγ0]
          _ = (3 * Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂)
                + Real.sqrt 32 * (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂))
                * (n : ℝ) ^ (-γ) := by ring
      calc Real.sqrt (∫ x, (X n x - ∫ y, X n y ∂μ n) ^ 2 ∂μ n)
          ≤ Real.sqrt ((1 / 4) * ((4 + 4 / (Real.log 2) ^ 2) * S)) := hstep1
        _ = Real.sqrt (4 + 4 / (Real.log 2) ^ 2) / 2 * Real.sqrt S := hstep2
        _ ≤ Real.sqrt (4 + 4 / (Real.log 2) ^ 2) / 2 *
            (Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂) * (3 * (n : ℝ) ^ (-(1 - b)))
              + Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n
                + Real.sqrt D₂ * gridCovarianceError b C₂ n)) := by
            exact mul_le_mul_of_nonneg_left hsqrtS
              (by nlinarith [hK0, Real.sqrt_nonneg (4 + 4 / (Real.log 2) ^ 2)])
        _ ≤ Real.sqrt (4 + 4 / (Real.log 2) ^ 2) / 2 *
            ((3 * Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂)
              + Real.sqrt 32 * (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂))
              * (n : ℝ) ^ (-γ)) := by
            refine mul_le_mul_of_nonneg_left hmid ?_
            nlinarith [hK0, Real.sqrt_nonneg (4 + 4 / (Real.log 2) ^ 2),
              Real.sqrt_nonneg (D₁ * Cv₁ + D₂ * Cv₂), Real.sqrt_nonneg 32,
              Real.sqrt_nonneg D₁, Real.sqrt_nonneg D₂, hCg₁₀, hCg₂₀, hγ0]
        _ = Real.sqrt (4 + 4 / (Real.log 2) ^ 2) / 2 *
            (3 * Real.sqrt (D₁ * Cv₁ + D₂ * Cv₂)
              + Real.sqrt 32 * (Real.sqrt D₁ * Cg₁ + Real.sqrt D₂ * Cg₂))
              * (n : ℝ) ^ (-γ) := by ring
    exact hL1.trans hbnd

/-! ### The variance of the literal chain statistic from the spectral energy -/

/-- **Var(Ĝ_n) ≤ 4·gaussianLogSquareVariance·(spectral correlation energy)**:
the landed `gaussianLogStatistic_variance_correlation_bound` at the literal
chain objects (retains all cross covariances; no independence needed). -/
theorem chainLogStatistic_variance_correlation
    (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    {H : Fin n → Ioo (0 : ℝ) 1}
    (hane : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t k i • actualQ1Obs f n H i ≠ 0) :
    Var[chainLogStatistic f r n δ t;
        featureGaussian (actualQ1Obs f n H)]
      ≤ 4 * gaussianLogSquareVariance *
        ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          ∑ k : Fin (localWeightActiveSet n 1 δ t).card,
            |actualQ1SpectralWeight f r n δ t i| *
              |actualQ1SpectralWeight f r n δ t k| *
              (featureCorrelation (actualQ1Obs f n H)
                (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t k)) ^ 2 :=
  gaussianLogStatistic_variance_correlation_bound _ _ _ hane

/-- **Var(Ĝ_n) ≤ 4·gaussianLogSquareVariance·card·∑ w_spec²** — the
spectral-weight energy form: each chain correlation is at most `1` in absolute
value (the inner-product form of `featureCorrelation`, unconditional), and the
double weight energy is at most `card · ∑ w²` (Cauchy–Schwarz). -/
theorem chainLogStatistic_variance_energy
    (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    {H : Fin n → Ioo (0 : ℝ) 1}
    (hane : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t k i • actualQ1Obs f n H i ≠ 0) :
    Var[chainLogStatistic f r n δ t;
        featureGaussian (actualQ1Obs f n H)]
      ≤ 4 * gaussianLogSquareVariance *
        ((Fintype.card (Fin (localWeightActiveSet n 1 δ t).card) : ℝ) *
          ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
            (actualQ1SpectralWeight f r n δ t i) ^ 2) := by
  refine (chainLogStatistic_variance_correlation f r n δ t hane).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg)
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_).trans
    (e5c_energy_card_sq (actualQ1SpectralWeight f r n δ t))
  have h1 : |featureCorrelation (actualQ1Obs f n H)
      (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t k)| ≤ 1 := by
    simpa only [featureCorrelation] using
      abs_real_inner_div_norm_mul_norm_le_one
        (∑ j, actualQ1Coeff n δ t i j • actualQ1Obs f n H j)
        (∑ j, actualQ1Coeff n δ t k j • actualQ1Obs f n H j)
  have hc1 : (featureCorrelation (actualQ1Obs f n H)
      (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t k)) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans (one_pow 2).le
  calc |actualQ1SpectralWeight f r n δ t i| * |actualQ1SpectralWeight f r n δ t k| *
      featureCorrelation (actualQ1Obs f n H)
        (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t k) ^ 2
      ≤ |actualQ1SpectralWeight f r n δ t i| * |actualQ1SpectralWeight f r n δ t k| * 1 :=
        mul_le_mul_of_nonneg_left hc1
          (mul_nonneg (abs_nonneg (actualQ1SpectralWeight f r n δ t i))
            (abs_nonneg (actualQ1SpectralWeight f r n δ t k)))
    _ = |actualQ1SpectralWeight f r n δ t i| * |actualQ1SpectralWeight f r n δ t k| := by
        rw [mul_one]

/-! ### The E5 fluctuation AT the literal chain statistic -/

/-- **MAIN: the E5 mean-fluctuation hypothesis at the literal P5 chain.**
Under the ordinary model (the literal feature-Gaussian measure
`featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))`) with the
chain nondegeneracy `hane`, and the spectral correlation energy in the RATE
form `∑∑ |w_j||w_k| corr² ≤ E · n^{-2γ} (log n)²` (eventually; the
energy-rate fact in the hE2 shape, cf. the docstring gap note), the calibrated
known-scale statistic `X_n = (cσ - Ĝ_n)/(2 log n)` satisfies, with the
explicit constant `F = √(4 gaussianLogSquareVariance E) / 2`,

`E|X_n - E X_n| ≤ F · n^{-γ}` eventually. -/
theorem e5_fluctuation_at_chain (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ)
    (cσ γ : ℝ)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hEnergy : ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
          |actualQ1SpectralWeight f r n (δ n) t i| *
            |actualQ1SpectralWeight f r n (δ n) t k| *
            (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
              (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t k)) ^ 2
        ≤ E * (n : ℝ) ^ (-2 * γ) * (Real.log n) ^ 2) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop,
      ∫ x, |chainCalibratedStatistic f r n (δ n) t cσ x -
          ∫ y, chainCalibratedStatistic f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        ≤ F * (n : ℝ) ^ (-γ) := by
  obtain ⟨E, hE0, hEn⟩ := hEnergy
  refine ⟨Real.sqrt (4 * gaussianLogSquareVariance * E) / 2,
    div_nonneg (Real.sqrt_nonneg _) (by norm_num), ?_⟩
  filter_upwards [hEn, eventually_ge_atTop 2] with n hEn' hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℕ) < n by omega)
  have hlog : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show (1 : ℕ) < n by omega))
  -- the log statistic is L², and its variance carries the spectral energy
  have hG2 : MemLp (chainLogStatistic f r n (δ n) t) 2
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
    chainLogStatistic_memLp_two f r n (δ n) t (hane n)
  have hVle : Var[chainLogStatistic f r n (δ n) t;
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))]
      ≤ 4 * gaussianLogSquareVariance *
        (E * (n : ℝ) ^ (-2 * γ) * (Real.log n) ^ 2) := by
    refine (chainLogStatistic_variance_correlation f r n (δ n) t (hane n)).trans ?_
    exact mul_le_mul_of_nonneg_left hEn'
      (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg)
  -- L1 ≤ √Var at the log statistic
  have hL1 : ∫ x, |chainLogStatistic f r n (δ n) t x -
      ∫ y, chainLogStatistic f r n (δ n) t y ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      ≤ Real.sqrt (Var[chainLogStatistic f r n (δ n) t;
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))]) :=
    e5c_integral_abs_le_sqrt_var hG2
  -- the calibration layer
  have hcal : ∫ x, |chainCalibratedStatistic f r n (δ n) t cσ x -
      ∫ y, chainCalibratedStatistic f r n (δ n) t cσ y ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      = (2 * Real.log n)⁻¹ * ∫ x, |chainLogStatistic f r n (δ n) t x -
          ∫ y, chainLogStatistic f r n (δ n) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) := by
    have heq : (chainCalibratedStatistic f r n (δ n) t cσ)
        = fun x => (cσ - chainLogStatistic f r n (δ n) t x) / (2 * Real.log n) := rfl
    rw [heq]
    exact e5c_calibration_centered_integral cσ (2 * Real.log n)
      (by linarith [hlog]) hG2
  -- the square root of the rate form
  have hsqsplit : Real.sqrt (4 * gaussianLogSquareVariance *
      (E * (n : ℝ) ^ (-2 * γ) * (Real.log n) ^ 2))
      = Real.sqrt (4 * gaussianLogSquareVariance * E) *
        (n : ℝ) ^ (-γ) * Real.log n := by
    have hA0 : 0 ≤ 4 * gaussianLogSquareVariance * E :=
      mul_nonneg (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg) hE0
    rw [show (4 * gaussianLogSquareVariance * (E * (n : ℝ) ^ (-2 * γ) *
          (Real.log n) ^ 2))
        = (4 * gaussianLogSquareVariance * E) *
          ((n : ℝ) ^ (-2 * γ) * (Real.log n) ^ 2) from by ring,
      Real.sqrt_mul hA0, Real.sqrt_mul (Real.rpow_nonneg hnR.le _),
      e5c_sqrt_rpow (n : ℝ) hnR.le (-2 * γ : ℝ),
      show (-2 : ℝ) * γ / 2 = -γ from by ring,
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.log_nonneg
        (by
          have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith))]
    ring
  -- assemble
  rw [hcal]
  calc (2 * Real.log n)⁻¹ * ∫ x, |chainLogStatistic f r n (δ n) t x -
        ∫ y, chainLogStatistic f r n (δ n) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
    ≤ (2 * Real.log n)⁻¹ * Real.sqrt (Var[chainLogStatistic f r n (δ n) t;
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))]) :=
      mul_le_mul_of_nonneg_left hL1 (inv_nonneg.mpr (by linarith [hlog]))
  _ ≤ (2 * Real.log n)⁻¹ * Real.sqrt (4 * gaussianLogSquareVariance *
        (E * (n : ℝ) ^ (-2 * γ) * (Real.log n) ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hVle)
        (inv_nonneg.mpr (by linarith [hlog]))
  _ = (2 * Real.log n)⁻¹ * (Real.sqrt (4 * gaussianLogSquareVariance * E) *
        (n : ℝ) ^ (-γ) * Real.log n) := by rw [hsqsplit]
  _ = Real.sqrt (4 * gaussianLogSquareVariance * E) / 2 * (n : ℝ) ^ (-γ) := by
      have hne : (2 : ℝ) * Real.log n ≠ 0 := by linarith
      field_simp

/-- **Windowed variant at the literal chain.**  Inside the finisher's feasible
window (`3/4 ≤ b < 1`, `0 < γ ≤ 1 - b`), a variance bound at the literal
calibrated chain statistic in EXACTLY the shape of the landed
`hurstHolder_q1_linearScale_variance_lt_one` discharges the E5 fluctuation
hypothesis (`MemLp` from `gaussianLogStatistic_memLp_two` + affine closure;
the discharge is the dependent-type clone of the finisher). -/
theorem e5_chain_fluctuation_discharged_window (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ)
    (b γ C₁ A₁ D₁ C₂ A₂ D₂ : ℝ)
    (hb34 : 3 / 4 ≤ b) (hb : b < 1)
    (hC₁ : 0 ≤ C₁) (hD₁ : 0 ≤ D₁) (hC₂ : 0 ≤ C₂) (hD₂ : 0 ≤ D₂)
    (hγpos : 0 < γ) (hγb : γ ≤ 1 - b)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hVar : ∀ᶠ n : ℕ in atTop,
      Var[chainCalibratedStatistic f r n (δ n) t cσ;
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))]
        ≤ (1 / 4) * ((4 + 4 / (Real.log 2) ^ 2) *
          (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
           D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n))) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop,
      ∫ x, |chainCalibratedStatistic f r n (δ n) t cσ x -
          ∫ y, chainCalibratedStatistic f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        ≤ F * (n : ℝ) ^ (-γ) := by
  refine e5c_fluctuation_discharged_dep b C₁ A₁ D₁ C₂ A₂ D₂ γ hb34 hb hC₁ hD₁
    hC₂ hD₂ hγpos hγb (fun n => chainCalibratedStatistic_memLp_two f r n (δ n) t
      cσ (hane n)) hVar

/-! ### The long-window corollary: the calibrated L1 fluctuation tends to 0 -/

/-- **The calibrated L1 fluctuation tends to 0 in the long-memory band.**
Under the ordinary bandwidth data (`0 < δ n` eventually, `δ n → 0`,
`n δ n → ∞`), the chain nondegeneracy `hane`, the bounded chain-weight energy
`hU` (the `hW0/hU` shape of `Hurst.P5LogHLayers`), and the long-memory band
`3/4 < f t` (so `ψ = 2 - 2 f t < 1/2`, hence
`∑ w_spec² = S^{2ψ-2} ∑ u²` and `S · ∑ w_spec² = S^{2ψ-1} → 0`), the
mean-centered L1 mass of the calibrated chain statistic
`X_n = (cσ - Ĝ_n)/(2 log n)` tends to `0`. -/
theorem e5_chain_calibrated_fluctuation_tendsto_zero (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hlong : 3 / 4 < f t)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hU : ∃ U : ℝ, 0 ≤ U ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1ChainWeight f r n (δ n) t i) ^ 2 ≤ U) :
    Tendsto (fun n : ℕ =>
      ∫ x, |chainCalibratedStatistic f r n (δ n) t cσ x -
          ∫ y, chainCalibratedStatistic f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
      atTop (𝓝 0) := by
  obtain ⟨U, hU0, hUn⟩ := hU
  set ψ : ℝ := 2 - 2 * f t with hψ_def
  have hψlt : ψ < 1 / 2 := by linarith
  -- the eventual bandwidth facts
  have hδle : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 :=
    (hδ0.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono fun _ h => le_of_lt h
  have hSpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * δ n := by
    filter_upwards [hδpos, eventually_ge_atTop 1] with n hδ hn
    exact mul_pos (by exact_mod_cast hn) hδ
  obtain ⟨_, hratio⟩ :=
    localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδpos hδ0 hN
  have hcardle : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * ((n : ℝ) * δ n) := by
    filter_upwards [hratio.eventually_lt_const (by norm_num : (2 : ℝ) < 3), hSpos] with n hlt hS
    exact le_of_lt ((div_lt_iff₀ hS).mp hlt)
  -- the spectral weights are S^{ψ-1} times the chain weights
  have hsumw : ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1SpectralWeight f r n (δ n) t i) ^ 2
      ≤ ((n : ℝ) * δ n) ^ (2 * (ψ - 1)) * U := by
    filter_upwards [hSpos, hUn] with n hS hUn'
    have hexpand : ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1SpectralWeight f r n (δ n) t i) ^ 2
        = ((n : ℝ) * δ n) ^ (2 * (ψ - 1)) *
          ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1ChainWeight f r n (δ n) t i) ^ 2 := by
      unfold actualQ1SpectralWeight
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, e5c_rpow_sq _ hS.le, hψ_def]
    rw [hexpand]
    exact mul_le_mul_of_nonneg_left hUn' (Real.rpow_nonneg hS.le _)
  -- the energy bound card · ∑ w² ≤ 3 U S^{2ψ-1}
  have hener : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (actualQ1SpectralWeight f r n (δ n) t i) ^ 2
      ≤ (3 * U) * ((n : ℝ) * δ n) ^ (2 * ψ - 1) := by
    filter_upwards [hcardle, hsumw, hSpos] with n hc hw hS
    have hw0 : 0 ≤ ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hjoin : (3 * ((n : ℝ) * δ n)) *
        (((n : ℝ) * δ n) ^ (2 * ψ - 2) * U)
        = (3 * U) * ((n : ℝ) * δ n) ^ (2 * ψ - 1) := by
      rw [show (3 * ((n : ℝ) * δ n)) * (((n : ℝ) * δ n) ^ (2 * ψ - 2) * U)
          = (3 * U) * (((n : ℝ) * δ n) * ((n : ℝ) * δ n) ^ (2 * ψ - 2)) from by ring,
        e5c_rpow_mul_one_add _ hS,
        show (1 : ℝ) + (2 * ψ - 2) = 2 * ψ - 1 from by ring]
    calc ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2
        ≤ (3 * ((n : ℝ) * δ n)) *
          ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 :=
          mul_le_mul_of_nonneg_right hc hw0
      _ ≤ (3 * ((n : ℝ) * δ n)) * (((n : ℝ) * δ n) ^ (2 * (ψ - 1)) * U) :=
          mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num) hS.le)
      _ ≤ (3 * ((n : ℝ) * δ n)) * (((n : ℝ) * δ n) ^ (2 * ψ - 2) * U) := by
          rw [show (2 : ℝ) * (ψ - 1) = 2 * ψ - 2 from by ring]
      _ = (3 * U) * ((n : ℝ) * δ n) ^ (2 * ψ - 1) := hjoin
  -- the L1 ≤ √Var route at the literal objects
  have hL1 : ∀ᶠ n : ℕ in atTop,
      ∫ x, |chainCalibratedStatistic f r n (δ n) t cσ x -
          ∫ y, chainCalibratedStatistic f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      ≤ (2 * Real.log n)⁻¹ * (Real.sqrt (12 * gaussianLogSquareVariance * U) *
        ((n : ℝ) * δ n) ^ (ψ - 1 / 2)) := by
    filter_upwards [hener, hSpos, eventually_ge_atTop 2] with n hene hS hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℕ) < n by omega)
    have hlog : 0 < Real.log n :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < n by omega))
    have hG2 : MemLp (chainLogStatistic f r n (δ n) t) 2
        (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
      chainLogStatistic_memLp_two f r n (δ n) t (hane n)
    have hVle : Var[chainLogStatistic f r n (δ n) t;
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))]
        ≤ 12 * gaussianLogSquareVariance * U * ((n : ℝ) * δ n) ^ (2 * ψ - 1) := by
      calc Var[chainLogStatistic f r n (δ n) t;
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))]
          ≤ 4 * gaussianLogSquareVariance *
              ((Fintype.card (Fin (localWeightActiveSet n 1 (δ n) t).card) : ℝ) *
                ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
                  (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) :=
            chainLogStatistic_variance_energy f r n (δ n) t (hane n)
        _ ≤ 4 * gaussianLogSquareVariance *
              (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
                ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
                  (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) := by
            rw [Fintype.card_fin]
        _ ≤ 4 * gaussianLogSquareVariance *
              (3 * U * ((n : ℝ) * δ n) ^ (2 * ψ - 1)) :=
            mul_le_mul_of_nonneg_left hene
              (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg)
        _ = 12 * gaussianLogSquareVariance * U * ((n : ℝ) * δ n) ^ (2 * ψ - 1) := by
            ring
    have hL1G := e5c_integral_abs_le_sqrt_var hG2
    have hcal : ∫ x, |chainCalibratedStatistic f r n (δ n) t cσ x -
        ∫ y, chainCalibratedStatistic f r n (δ n) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        = (2 * Real.log n)⁻¹ * ∫ x, |chainLogStatistic f r n (δ n) t x -
            ∫ y, chainLogStatistic f r n (δ n) t y ∂
              featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) := by
      have heq : (chainCalibratedStatistic f r n (δ n) t cσ)
          = fun x => (cσ - chainLogStatistic f r n (δ n) t x) / (2 * Real.log n) := rfl
      rw [heq]
      exact e5c_calibration_centered_integral cσ (2 * Real.log n)
        (by linarith [hlog]) hG2
    have hsqrt : Real.sqrt ((12 * gaussianLogSquareVariance * U) *
        ((n : ℝ) * δ n) ^ (2 * ψ - 1))
        = Real.sqrt (12 * gaussianLogSquareVariance * U) *
          ((n : ℝ) * δ n) ^ (ψ - 1 / 2) := by
      rw [Real.sqrt_mul
        (mul_nonneg (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg) hU0)]
      congr 1
      rw [e5c_sqrt_rpow ((n : ℝ) * δ n) hS.le (2 * ψ - 1),
        show ((2 : ℝ) * ψ - 1) / 2 = ψ - 1 / 2 from by ring]
    calc ∫ x, |chainCalibratedStatistic f r n (δ n) t cσ x -
          ∫ y, chainCalibratedStatistic f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        = (2 * Real.log n)⁻¹ * ∫ x, |chainLogStatistic f r n (δ n) t x -
            ∫ y, chainLogStatistic f r n (δ n) t y ∂
              featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) := hcal
      _ ≤ (2 * Real.log n)⁻¹ * Real.sqrt (Var[chainLogStatistic f r n (δ n) t;
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))]) :=
          mul_le_mul_of_nonneg_left hL1G (inv_nonneg.mpr (by linarith [hlog]))
      _ ≤ (2 * Real.log n)⁻¹ * Real.sqrt ((12 * gaussianLogSquareVariance * U) *
            ((n : ℝ) * δ n) ^ (2 * ψ - 1)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hVle)
            (inv_nonneg.mpr (by linarith [hlog]))
      _ = (2 * Real.log n)⁻¹ * (Real.sqrt (12 * gaussianLogSquareVariance * U) *
            ((n : ℝ) * δ n) ^ (ψ - 1 / 2)) := by rw [hsqrt]
  -- the mesh power S^{ψ - 1/2} → 0 (ψ < 1/2), and (2 log n)^{-1} → 0
  have hexpneg : 0 < 1 / 2 - ψ := by linarith
  have hmesh : Tendsto
      (fun n : ℕ => ((n : ℝ) * δ n) ^ (ψ - 1 / 2)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (1 / 2 - ψ)) atTop atTop :=
      (tendsto_rpow_atTop hexpneg).comp hN
    refine hbase.inv_tendsto_atTop.congr' ?_
    filter_upwards [hSpos] with n hS
    show ((↑n * δ n) ^ (1 / 2 - ψ))⁻¹ = (↑n * δ n) ^ (ψ - 1 / 2)
    rw [show (ψ - 1 / 2) = -(1 / 2 - ψ) from by ring, Real.rpow_neg hS.le]
  have hlogzero : Tendsto (fun n : ℕ => (2 * Real.log n)⁻¹) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => (2 : ℝ) * Real.log (n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num)
        (Tendsto.comp Real.tendsto_log_atTop tendsto_natCast_atTop_atTop)
    exact h2.inv_tendsto_atTop
  refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun _ => abs_nonneg _)
    hL1 ?_
  have hprod := Tendsto.mul hlogzero
    (hmesh.const_mul (Real.sqrt (12 * gaussianLogSquareVariance * U)))
  simpa using hprod

end Hurst
