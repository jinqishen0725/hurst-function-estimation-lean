import Hurst.E5BiasEnvelope
import Hurst.P7RowBound

/-!
# E5 fluctuation finisher: the mean-fluctuation hypothesis discharged

This module closes the ONE explicit hypothesis left open by `Hurst.E5BiasEnvelope`:
the mean-centered L1 fluctuation `E|X_n - E X_n| ≤ F n^{-γ}` consumed by
`e5_bias_envelope` (the clip `p5Trunc01` is not affine, so the expectation of the
clipped estimator sees the fluctuation layer).

## The discharge route (variance layer, clipped-Lipschitz shape)

The landed variance bound (`Hurst.FirstScaleLongVariance.hurstHolder_q1_linearScale_variance_lt_one`,
mirroring the `gaussianLogStatistic` variance layer of `Hurst.P5LogHLayers`) is

`Var[Ĝ_n] ≤ (4 + 4/log²2) · (log n)² · (D₁/n · row₁ n + D₂/n · row₂ n)`,

with `row_i n = firstStrideLongRowBound b C_i A_i d_i n`.  Through the known-scale
calibration `X_n = (cσ - Ĝ_n)/(2 log n)` the variance divides by `(2 log n)²`,
which cancels the `(log n)²` — exactly the hypothesis `hVar` of
`e5_fluctuation_discharged` below (the `1/4` factor).  Then

* `E|X_n - E X_n| ≤ √Var[X_n]` (L1 ≤ L2 on a probability space,
  `e5f_integral_abs_le_sq`);
* the landed row-bound split
  (`Hurst.P7RowBound.p7_firstStrideLongRowBound_div_n_le`) gives
  `row_i/n ≤ Cv_i (n^{-1/2} + n^{-1} + n^{2b-2}) + 32 · gridCov_i²`;
* `√(n^{-1/2} + n^{-1} + n^{2b-2}) ≤ 3 n^{-(1-b)}` for `3/4 ≤ b < 1`
  (`p7_sqrt_rpow_sum_le_mesh`);
* `gridCovarianceError b C_i n ≤ Cg_i n^{-γ}` eventually for `0 < γ < 1`,
  `γ + 2b < 2` (`gridCovarianceError_le_const_rpow`, from `Hurst.E5BiasEnvelope`).

## The joint feasible window (exact)

The fluctuation discharge `e5_fluctuation_discharged` requires EXACTLY

* the long-memory band `3/4 ≤ b < 1` (for the √-domination of the row-bound
  split), and
* the bandwidth window `0 < γ ≤ 1 - b`.

This SUBSUMES the E5 bias-envelope window: `γ < 1` (since `b ≥ 3/4 > 0`) and
`γ + 2b ≤ 1 + b < 2`, so `gridCovarianceError_le_const_rpow` applies with no
extra hypothesis; it also implies `γ < 1/2` (indeed `γ ≤ 1 - b ≤ 1/4`), so the
bandwidth `δ n = n^{-γ}` is feasible for every consumer that asks `γ < 1/2`.

The composed drift corollary `e5_drift_fully_discharged` adds the E5 drift
window `(1 - γ) ψ < γ` with `0 < ψ`, i.e. `γ > ψ/(1 + ψ)`.  Jointly the window
is nonempty iff `ψ/(1+ψ) < 1 - b`, i.e. `0 < ψ < (1 - b)/b` — for `b ∈ [3/4, 1)`
this admits every `ψ < (1-b)/b ≤ 1/3`.  Both the bias envelope and the
fluctuation are then derived from the ordinary model + bandwidth data alone:
NO explicit fluctuation hypothesis remains.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Hurst

/-! ### Elementary helpers -/

/-- √-subadditivity: `√(x + y) ≤ √x + √y` for `x, y ≥ 0` (the P7 helper is
private there, so we restate it). -/
private theorem e5f_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
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
private theorem e5f_integral_abs_le_sq {Ω : Type*} [MeasurableSpace Ω]
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
private theorem e5f_integral_abs_le_sqrt_var {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ x, |X x - ∫ y, X y ∂μ| ∂μ ≤ Real.sqrt (Var[X; μ]) := by
  have hc : MemLp (fun x => X x - ∫ y, X y ∂μ) 2 μ := hX.sub (memLp_const _)
  rw [ProbabilityTheory.variance_eq_integral hX.aemeasurable]
  exact e5f_integral_abs_le_sq (hc.integrable (by norm_num)) hc.integrable_sq

/-! ### The fluctuation discharge -/

/-- **The E5 mean-fluctuation hypothesis, discharged** (file 24 E5, variance
layer).  Under the ordinary model (a probability space per `n`), the long-memory
band `3/4 ≤ b < 1`, the bandwidth window `0 < γ ≤ 1 - b` (which implies
`γ < 1/2`, so `δ n = n^{-γ}` is feasible), the L² assumption on the statistic,
and the landed variance bound `hVar` — exactly
`Hurst.FirstScaleLongVariance.hurstHolder_q1_linearScale_variance_lt_one`
transported through the known-scale calibration `X_n = (cσ - Ĝ_n)/(2 log n)`
(the variance divides by `(2 log n)²`, cancelling the `(log n)²`) — there is a
constant `F ≥ 0` with, eventually,

`E|X_n - E X_n| ≤ F · n^{-γ}`,

which is exactly the fluctuation hypothesis `hFluct` of
`Hurst.E5BiasEnvelope.e5_bias_envelope`. -/
theorem e5_fluctuation_discharged {Ω : Type*} [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω} [∀ n : ℕ, IsProbabilityMeasure (μ n)]
    {X : ℕ → Ω → ℝ}
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
    have hL1 := e5f_integral_abs_le_sqrt_var (hX2 n)
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
        e5f_sqrt_add_le _ _ (mul_nonneg hDCv hR0) hsplit0
      have hinner : Real.sqrt (32 * (D₁ * gridCovarianceError b C₁ n ^ 2
            + D₂ * gridCovarianceError b C₂ n ^ 2))
          ≤ Real.sqrt 32 * (Real.sqrt D₁ * gridCovarianceError b C₁ n)
            + Real.sqrt 32 * (Real.sqrt D₂ * gridCovarianceError b C₂ n) := by
        have h1 := e5f_sqrt_add_le (32 * (D₁ * gridCovarianceError b C₁ n ^ 2))
          (32 * (D₂ * gridCovarianceError b C₂ n ^ 2))
          (mul_nonneg (by norm_num) hsq1) (mul_nonneg (by norm_num) hsq2)
        rw [htermB, htermC] at h1
        rw [mul_add]
        exact h1
      have hsqrtR : Real.sqrt R ≤ 3 * (n : ℝ) ^ (-(1 - b)) := by
        have h1 : Real.sqrt R ≤ Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ))
            + Real.sqrt ((n : ℝ) ^ (2 * b - 2)) :=
          e5f_sqrt_add_le _ _ (add_nonneg (Real.rpow_nonneg hnR.le _)
            (Real.rpow_nonneg hnR.le _)) (Real.rpow_nonneg hnR.le _)
        have h2 : Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ))
            ≤ Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)) + Real.sqrt ((n : ℝ) ^ (-1 : ℝ)) :=
          e5f_sqrt_add_le _ _ (Real.rpow_nonneg hnR.le _) (Real.rpow_nonneg hnR.le _)
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

/-! ### The composed drift corollary: no explicit fluctuation hypothesis -/

/-- **E5 fully discharged: the truth-centered drift vanishes.**  Composition of
`Hurst.E5BiasEnvelope.e5_bias_envelope` with the fluctuation discharge
`e5_fluctuation_discharged` and the drift condition
`Hurst.P5TruthCenter.drift_condition_s1`: under the ordinary model, the
long-memory band `3/4 ≤ b < 1`, the joint window
`0 < γ ≤ 1 - b` (bandwidth; subsumes the E5 bias window `γ < 1`, `γ + 2b < 2`,
and `γ < 1/2`) and `(1 - γ) ψ < γ` (drift; nonempty jointly iff
`0 < ψ < (1 - b)/b`), the truth-centered drift of the clipped known-scale H
estimator tends to zero — with NO explicit fluctuation hypothesis: the bias
envelope and the fluctuation both come from the ordinary + bandwidth data
(the calibrated bias `hBias` and the landed variance bound `hVar`). -/
theorem e5_drift_fully_discharged {Ω : Type*} [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω} [∀ n : ℕ, IsProbabilityMeasure (μ n)]
    {X : ℕ → Ω → ℝ} (h : ℝ) (E b γ ψ : ℝ) (C₁ A₁ D₁ C₂ A₂ D₂ : ℝ)
    (hh : h ∈ Icc 0 1) (hb34 : 3 / 4 ≤ b) (hb : b < 1)
    (hC₁ : 0 ≤ C₁) (hD₁ : 0 ≤ D₁) (hC₂ : 0 ≤ C₂) (hD₂ : 0 ≤ D₂)
    (hγpos : 0 < γ) (hγb : γ ≤ 1 - b)
    (hψpos : 0 < ψ) (hE5 : (1 - γ) * ψ < γ * 1)
    (hX2 : ∀ n : ℕ, MemLp (X n) 2 (μ n))
    (hVar : ∀ᶠ n : ℕ in atTop,
      Var[X n; μ n] ≤ (1 / 4) * ((4 + 4 / (Real.log 2) ^ 2) *
        (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
         D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)))
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ x, X n x ∂μ n - h| ≤ (1 / 2) * gridCovarianceError b E n) :
    Tendsto (fun n : ℕ =>
      |2 * (n : ℝ) ^ (ψ * (1 - γ)) * Real.log n *
        (∫ x, p5Trunc01 (X n x) ∂μ n - h)|) atTop (𝓝 0) := by
  obtain ⟨F, hF0, hF⟩ := e5_fluctuation_discharged b C₁ A₁ D₁ C₂ A₂ D₂ γ
    hb34 hb hC₁ hD₁ hC₂ hD₂ hγpos hγb hX2 hVar
  have hb0 : 0 < b := by linarith
  have hγlt : γ < 1 := by linarith
  have hγ2 : γ + 2 * b < 2 := by linarith
  have hXint : ∀ n : ℕ, Integrable (X n) (μ n) := fun n =>
    (hX2 n).integrable (by norm_num)
  exact e5_drift_of_bias_envelope h E b γ F ψ hh hb hγpos hγlt hγ2 hψpos hE5
    hXint hBias hF hF0

end Hurst
