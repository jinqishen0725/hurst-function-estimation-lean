import Hurst.P5LogHLayers
import Hurst.FirstScaleLongRates
import Hurst.GridErrorRate

/-!
# P5 truth-centering drift condition (file 24 E5, conservative `s = 1`)

`Hurst.P5LogHLayers.p5_transport_truthCentered_of_drift` (file 24 E4) turns the
EXPECTATION-centered known-scale H limit into the TRUTH-centered one given the
deterministic drift `c n (E Ĥ_n - h) → 0`; `Hurst.P5SeamClosed` instantiates the
transport at the actual chain objects with `c n = 2 S^ψ log n` (`S = n δ n`,
`ψ = 2 - 2 f t`, the `p5_YX_identity` scale) but keeps that drift EXPLICIT
(`hDrift`).  This file lands the E5 piece upstream: the drift condition itself.

## The bandwidth window and the drift algebra

Feasible bandwidth `δ n = n^{-γ}`, `0 < γ < 1`.  Then `S n = n δ n = n^{1-γ}`
and the transport scale is

`c n = 2 S n^ψ log n = 2 n^{ψ (1 - γ)} log n`,   `ψ = 2 - 2 f t > 0` (long memory),

so `|c n (E Ĥ_n - h)| ≤ 2 C * log n * n^{ψ (1 - γ) - γ}` whenever the bias
envelope `|E Ĥ_n - h| ≤ C n^{-γ}` holds eventually.  The exponent
`ψ (1 - γ) - γ < 0` is EXACTLY the E5 window condition
`(1 - γ) * ψ < γ * 1` with the conservative exponent `s = 1` (a bias rate of
one bandwidth power: `δ^1 = n^{-γ}`); the log-damped rate
`(1 + log (2 n))^k n^r → 0` (`r < 0`) of `Hurst.FirstScaleLongRates` then kills
the `log n` factor.  File 24's polynomial-degree route (`s = p` for a degree-`p`
polynomial correction) is NOT taken: any polynomial degree cannot directly
provide `s = p` here, so we conservatively take `s = 1`.

## Main statements

* `truthScaleC` — the transport scale `c n = 2 S^ψ log n` (identical formula to
  `Hurst.P5SeamClosed.seamScaleC`, which is not yet in the build; the output of
  `p5_truthCenter_drift_s1` is exactly the `hDrift` shape consumed by
  `Hurst.P5SeamClosed.logStatistic_knownScaleH_seam_truthCentered`).
* `drift_rate_s1` — the landed conservative rate: `log n * n^{ψ(1-γ) - γ} → 0`
  under the explicit E5 window `(1 - γ) * ψ < γ * 1`, via
  `FirstScaleLongRates.mesh_log_power_rpow_tendsto`.
* `drift_condition_s1` — the abstract drift condition
  `|c n (E Ĥ_n - h)| → 0` with `c n = 2 n^{ψ (1 - γ)} log n`, from the explicit
  bias envelope `|E Ĥ_n - h| ≤ C n^{-γ}` (eventually; the landed `s = 1`
  bias-rate shape) and the E5 window.
* `p5_truthCenter_drift_condition_s1` / `p5_truthCenter_drift_s1` — the chain
  instances at the P5 objects (`E Ĥ_n` = the mean of the clipped estimator
  `p5KnownScaleEstimator` under the D3 observation measure, `h = f t`,
  `ψ = 2 - 2 f t`, feasible bandwidth `δ n = n^{-γ}`), in absolute-value and
  plain (transport-consumable `hDrift`) form.

## Deviation note (honesty)

The bias envelope `|E Ĥ_n - h| ≤ C n^{-γ}` is kept EXPLICIT as a hypothesis of
`drift_condition_s1` / the chain instances: deriving it for the actual P5
log-statistic chain from the grid-error rate layer (`Hurst.GridErrorRate`,
whose linear `S^{ψ-1}`-form `card_gridError_S_psi_tendsto_zero` provides
envelope-shaped rates) is upstream work; what is PROVED here is that this
envelope, under the explicit window `(1 - γ) * ψ < γ * 1` and `0 < γ < 1`,
implies the E4 drift condition at the exact transport scale `c n = 2 S^ψ log n`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## The transport scale at the feasible bandwidth -/

/-- The known-scale transport scale of the truth-centering layer:
`c n = 2 S^ψ log n` with `S = n δ n` and `ψ = 2 - 2 f t`.  Identical formula to
`Hurst.P5SeamClosed.seamScaleC` (the `p5_YX_identity` scale of
`Hurst.P5LogHLayers`). -/
def truthScaleC (f : ℝ → ℝ) (t : ℝ) (δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * ((n : ℝ) * δ n) ^ (2 - 2 * f t) * Real.log n

/-- The feasible-bandwidth specialization: at `δ n = n^{-γ}` the scale is
`c n = 2 n^{ψ (1 - γ)} log n` with `ψ = 2 - 2 f t`. -/
theorem truthScaleC_feasible_eq (f : ℝ → ℝ) (t γ : ℝ) (n : ℕ) :
    truthScaleC f t (fun m => (m : ℝ) ^ (-γ)) n
      = 2 * (n : ℝ) ^ ((2 - 2 * f t) * (1 - γ)) * Real.log n := by
  unfold truthScaleC
  rcases Nat.eq_zero_or_pos n with rfl | hn'
  · simp only [Nat.cast_zero, Real.log_zero]
    ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'
  have hS : (n : ℝ) * (n : ℝ) ^ (-γ) = (n : ℝ) ^ (1 - γ) := by
    calc (n : ℝ) * (n : ℝ) ^ (-γ) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-γ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (-γ)) := (Real.rpow_add hn0 1 (-γ)).symm
      _ = (n : ℝ) ^ (1 - γ) := rfl
  have hpow : ((n : ℝ) ^ (1 - γ)) ^ (2 - 2 * f t)
      = (n : ℝ) ^ ((2 - 2 * f t) * (1 - γ)) := by
    rw [(Real.rpow_mul hn0.le (1 - γ) (2 - 2 * f t)).symm]
    congr 1
    ring
  rw [hS, hpow]

/-! ## The E5 window and the landed conservative rate -/

/-- The E5 window `(1 - γ) * ψ < γ * 1` is exactly negativity of the drift
exponent `ψ * (1 - γ) - γ`. -/
theorem drift_exponent_neg_s1 {γ ψ : ℝ} (hE5 : (1 - γ) * ψ < γ * 1) :
    ψ * (1 - γ) - γ < 0 := by
  have hE5' : ψ - γ * ψ < γ := by
    have hex : (1 - γ) * ψ = ψ - γ * ψ := by ring
    have hex2 : γ * 1 = γ := by ring
    rw [hex, hex2] at hE5
    exact hE5
  have hr : ψ * (1 - γ) = ψ - γ * ψ := by ring
  rw [hr]
  linarith

/-- **The landed conservative (`s = 1`) drift rate.**  Under the explicit E5
bandwidth window `(1 - γ) * ψ < γ * 1` the log-damped drift rate
`log n * n^{ψ (1 - γ) - γ}` tends to zero — the `k = 1`, `r = ψ (1 - γ) - γ`
instance of the conservative log-damped rate layer
`FirstScaleLongRates.mesh_log_power_rpow_tendsto`. -/
theorem drift_rate_s1 (γ ψ : ℝ) (hE5 : (1 - γ) * ψ < γ * 1) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) * (n : ℝ) ^ (ψ * (1 - γ) - γ))
      atTop (𝓝 0) := by
  have hr := drift_exponent_neg_s1 (γ := γ) (ψ := ψ) hE5
  have h := mesh_log_power_rpow_tendsto (ψ * (1 - γ) - γ) hr 1
  simp only [pow_one] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (Real.log_nonneg hn1) (Real.rpow_nonneg hn0.le _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have h2 : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    have hpow0 : 0 ≤ (n : ℝ) ^ (ψ * (1 - γ) - γ) := Real.rpow_nonneg hn0.le _
    calc Real.log (n : ℝ) * (n : ℝ) ^ (ψ * (1 - γ) - γ)
        ≤ (1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (ψ * (1 - γ) - γ) :=
          mul_le_mul_of_nonneg_right (by linarith) hpow0

/-! ## The drift condition (file 24 E5, conservative `s = 1`) -/

/-- **File 24 E5 (conservative `s = 1`): the truth-centering drift condition.**

At the feasible bandwidth `δ n = n^{-γ}` (`0 < γ < 1`) the transport scale of
`Hurst.P5LogHLayers.p5_transport_truthCentered_of_drift` is
`c n = 2 n^{ψ (1 - γ)} log n` (`ψ = 2 - 2 f t > 0`).  If the bias envelope

`|E Ĥ_n - h| ≤ C n^{-γ}`   (eventually; the landed `s = 1` bias rate, one
bandwidth power)

holds, then under the EXPLICIT E5 window condition `(1 - γ) * ψ < γ * 1` the
drift vanishes: `|c n * (E Ĥ_n - h)| → 0`. -/
theorem drift_condition_s1 (h : ℝ) (EĤ : ℕ → ℝ) (γ ψ : ℝ)
    (hγpos : 0 < γ) (hγlt : γ < 1) (hψpos : 0 < ψ)
    (hE5 : (1 - γ) * ψ < γ * 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop, |EĤ n - h| ≤ C * (n : ℝ) ^ (-γ)) :
    Tendsto (fun n : ℕ => |2 * (n : ℝ) ^ (ψ * (1 - γ)) * Real.log n * (EĤ n - h)|)
      atTop (𝓝 0) := by
  have hrate := drift_rate_s1 γ ψ hE5
  -- the dominating mesh rate, scaled by `2 * C`
  have hr : ψ * (1 - γ) - γ < 0 := drift_exponent_neg_s1 hE5
  have hmesh := mesh_log_power_rpow_tendsto (ψ * (1 - γ) - γ) hr 1
  simp only [pow_one] at hmesh
  have hbound : Tendsto
      (fun n : ℕ =>
        2 * C * ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (ψ * (1 - γ) - γ)))
      atTop (𝓝 0) := by
    have hbound0 := hmesh.const_mul (2 * C)
    simp only [mul_zero] at hbound0
    exact hbound0
  apply squeeze_zero' _ _ hbound
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1, hBias] with n hn hB
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hpow0 : 0 ≤ (n : ℝ) ^ (ψ * (1 - γ)) := Real.rpow_nonneg hn0.le _
    -- the absolute value factorizes
    have hA : 0 ≤ 2 * (n : ℝ) ^ (ψ * (1 - γ)) * Real.log n :=
      mul_nonneg (mul_nonneg (by norm_num) hpow0) hlog0
    have habs : |2 * (n : ℝ) ^ (ψ * (1 - γ)) * Real.log n * (EĤ n - h)|
        = 2 * (n : ℝ) ^ (ψ * (1 - γ)) * Real.log n * |EĤ n - h| := by
      rw [abs_mul, abs_of_nonneg hA]
    rw [habs]
    -- the bias envelope enters, and the two powers of `n` merge into the drift exponent
    have hmerge : (n : ℝ) ^ (ψ * (1 - γ)) * (n : ℝ) ^ (-γ)
        = (n : ℝ) ^ (ψ * (1 - γ) - γ) := by
      rw [← Real.rpow_add hn0 (ψ * (1 - γ)) (-γ)]
      congr 1
    calc 2 * (n : ℝ) ^ (ψ * (1 - γ)) * Real.log n * |EĤ n - h|
        ≤ 2 * (n : ℝ) ^ (ψ * (1 - γ)) * Real.log n * (C * (n : ℝ) ^ (-γ)) :=
          mul_le_mul_of_nonneg_left hB hA
      _ = 2 * C * (Real.log n * ((n : ℝ) ^ (ψ * (1 - γ)) * (n : ℝ) ^ (-γ))) := by ring
      _ = 2 * C * (Real.log n * (n : ℝ) ^ (ψ * (1 - γ) - γ)) := by rw [hmerge]
      _ ≤ 2 * C * ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (ψ * (1 - γ) - γ)) := by
          have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
          have h2 : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := by
            rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hn0.le _))
            (mul_nonneg (by norm_num) hC)

/-! ## The chain instances at the P5 known-scale estimator -/

/-- **The E5 drift condition at the actual P5 chain objects** (feasible
bandwidth `δ n = n^{-γ}`), absolute-value form.  `E Ĥ_n` is the mean of the
clipped known-scale H estimator `p5KnownScaleEstimator` under the D3
observation measure `featureGaussian (actualQ1Obs f n (midpointSampleHurst …))`,
`h = f t`, `ψ = 2 - 2 f t`, `c n = truthScaleC f t (fun m => m^{-γ}) n =
2 n^{ψ (1 - γ)} log n`.  The bias envelope `hBias` is the explicit landed
`s = 1` bias-rate hypothesis (see the deviation note in the module docstring). -/
theorem p5_truthCenter_drift_condition_s1
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (cσ : ℝ) (γ : ℝ)
    (hγpos : 0 < γ) (hγlt : γ < 1)
    (hlong : 3 / 4 < f t) (hfb : f t < 1)
    (hE5 : (1 - γ) * (2 - 2 * f t) < γ * 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * (n : ℝ) ^ (-γ)) :
    Tendsto (fun n : ℕ =>
      |truthScaleC f t (fun m => (m : ℝ) ^ (-γ)) n *
        (∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t)|)
      atTop (𝓝 0) := by
  have hψpos : 0 < 2 - 2 * f t := by linarith
  have h := drift_condition_s1 (f t)
    (fun n => ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    γ (2 - 2 * f t) hγpos hγlt hψpos hE5 C hC hBias
  refine Tendsto.congr (fun n => ?_) h
  rw [truthScaleC_feasible_eq]

/-- **The E5 drift condition at the actual P5 chain objects, plain form** —
exactly the `hDrift` shape consumed by
`Hurst.P5SeamClosed.logStatistic_knownScaleH_seam_truthCentered` (with the
feasible bandwidth `δ n = n^{-γ}`). -/
theorem p5_truthCenter_drift_s1
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (cσ : ℝ) (γ : ℝ)
    (hγpos : 0 < γ) (hγlt : γ < 1)
    (hlong : 3 / 4 < f t) (hfb : f t < 1)
    (hE5 : (1 - γ) * (2 - 2 * f t) < γ * 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * (n : ℝ) ^ (-γ)) :
    Tendsto (fun n : ℕ =>
      truthScaleC f t (fun m => (m : ℝ) ^ (-γ)) n *
        (∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t))
      atTop (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine Tendsto.congr
    (fun n => by simp only [Real.dist_eq, sub_zero])
    (p5_truthCenter_drift_condition_s1 f hf r t cσ γ hγpos hγlt hlong hfb hE5 C hC hBias)

end Hurst
