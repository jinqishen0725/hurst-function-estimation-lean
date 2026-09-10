import Hurst.SecondFrozenCrossLagCorrelation
import Hurst.SecondGridActual
import Hurst.CorrelationLimit
import Hurst.HilbertPerturbation

noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Along any local pair of q=2 grid increments with a fixed relative lag,
the actual nonstationary correlation converges to the frozen q=2 correlation
at the local Hurst parameter. -/
theorem hurstHolder_grid_second_fixedLag_correlation_tendsto
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (x : ℝ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (i j : ∀ n, Fin (N n - 2))
    (hi : Tendsto (fun n => grid (N n) (i n).val) atTop (𝓝 t))
    (hj : Tendsto (fun n => grid (N n) (j n).val) atTop (𝓝 t))
    (hlag : ∀ᶠ n in atTop,
      grid (N n) (j n).val =
        grid (N n) (i n).val + x * (1 / (N n : ℝ))) :
    Tendsto (fun n => vectorCorrelation
      (gridSecondActual (N n) (midpointSampleHurst f hf.1 (N n)) (i n))
      (gridSecondActual (N n) (midpointSampleHurst f hf.1 (N n)) (j n)))
      atTop (𝓝 (secondIncrementLagCorrelation (f t) x)) := by
  obtain ⟨C, hC, hrem⟩ :=
    hurstHolder_grid_second_remainder p a b M hp ha hb hab hM
  let H := fun n => midpointSampleHurst f hf.1 (N n)
  let U := fun n => gridSecondActual (N n) (H n) (i n)
  let W := fun n => gridSecondActual (N n) (H n) (j n)
  let V := fun n => normalizedFrozenSecondIncrement
    (H n (secondDiffLeft (N n) (i n)))
    (grid (N n) (i n).val) (1 / (N n : ℝ))
  let Z := fun n => normalizedFrozenSecondIncrement
    (H n (secondDiffLeft (N n) (j n)))
    (grid (N n) (j n).val) (1 / (N n : ℝ))
  let e := fun n => gridCovarianceError (1 / 2) C (N n)
  have hfcont : ContinuousAt f t := by
    simpa only [iteratedDeriv_zero] using
      (hf.2.1 0 (by have := hurstHolder_floor_pos p (by linarith); omega) t ht).continuousAt
  have hHi : Tendsto
      (fun n => (H n (secondDiffLeft (N n) (i n)) : ℝ))
      atTop (𝓝 (f t)) := by
    convert hfcont.tendsto.comp hi using 1
    ext n
    rfl
  have hHj : Tendsto
      (fun n => (H n (secondDiffLeft (N n) (j n)) : ℝ))
      atTop (𝓝 (f t)) := by
    convert hfcont.tendsto.comp hj using 1
    ext n
    rfl
  have hft := hf.1 ht
  have hcross := secondIncrementCrossLagCovariance_tendsto
    (f t) (f t) x hft.1 hft.2 hft.1 hft.2
    (fun n => (H n (secondDiffLeft (N n) (i n)) : ℝ))
    (fun n => (H n (secondDiffLeft (N n) (j n)) : ℝ)) hHi hHj
  have hNpos : ∀ᶠ n in atTop, 0 < N n := hN.eventually_gt_atTop 0
  have he : Tendsto e atTop (𝓝 0) := by
    dsimp only [e]
    exact (gridCovarianceError_tendsto (1 / 2) C (by norm_num)).comp hN
  have he0 : ∀ᶠ n in atTop, 0 ≤ e n := by
    filter_upwards [hNpos] with n hn
    dsimp only [e]
    unfold gridCovarianceError
    have hnR : (1 : ℝ) ≤ N n := by exact_mod_cast (show 1 ≤ N n by omega)
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (N n : ℝ) by linarith)
    positivity
  have hesmall : ∀ᶠ n in atTop, e n ≤ 1 :=
    he.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hfrozen : Tendsto (fun n => ⟪V n, Z n⟫)
      atTop (𝓝 (secondIncrementCrossLagCovariance (f t) (f t) x)) := by
    apply hcross.congr'
    filter_upwards [hlag, hNpos] with n hnlag hn
    dsimp only [V, Z]
    rw [hnlag]
    exact (normalizedFrozenSecondIncrement_cross_parameter_lag
      (H n (secondDiffLeft (N n) (i n)))
      (H n (secondDiffLeft (N n) (j n)))
      (grid (N n) (i n).val) (1 / (N n : ℝ)) x (by positivity)).symm
  have hinnerBound : ∀ᶠ n in atTop,
      |⟪U n, W n⟫ - ⟪V n, Z n⟫| ≤ 5 * e n := by
    filter_upwards [hNpos, he0, hesmall] with n hn hen hsmall
    have hUV : ‖U n - V n‖ ≤ e n := by
      exact hrem f hf hF (N n) hn (i n)
    have hWZ : ‖W n - Z n‖ ≤ e n := by
      exact hrem f hf hF (N n) hn (j n)
    have hb := inner_perturbation_norm_bound (U n) (W n) (V n) (Z n)
      2 (e n) (by norm_num) hen
      (normalizedFrozenSecondIncrement_norm_le _ _ _ (by positivity))
      (normalizedFrozenSecondIncrement_norm_le _ _ _ (by positivity)) hUV hWZ
    have he2 : e n ^ 2 ≤ e n := by nlinarith
    nlinarith
  have hinner : Tendsto (fun n => ⟪U n, W n⟫)
      atTop (𝓝 (secondIncrementCrossLagCovariance (f t) (f t) x)) := by
    apply tendsto_of_abs_sub_le_zero (fun n => ⟪U n, W n⟫)
      (fun n => ⟪V n, Z n⟫) (fun n => 5 * e n)
      (secondIncrementCrossLagCovariance (f t) (f t) x) hfrozen
      (by simpa only [mul_zero] using he.const_mul 5)
    · filter_upwards [he0] with n hn
      positivity
    · exact hinnerBound
  let q : ℝ := 4 - (2 : ℝ) ^ (2 * f t)
  have hqpos : 0 < q := by
    dsimp only [q]
    have hlt : 2 * f t < (2 : ℝ) := by
      simpa only [mul_one] using
        (mul_lt_mul_of_pos_left hft.2 (show (0 : ℝ) < 2 by norm_num))
    have hpw : (2 : ℝ) ^ (2 * f t) < (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
    have htwo : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    exact sub_pos.mpr (hpw.trans_eq htwo)
  have hlin : ContinuousAt (fun z : ℝ => 2 * z) (f t) :=
    continuousAt_const.mul continuousAt_id
  have hpowCont : ContinuousAt (fun z : ℝ => (2 : ℝ) ^ (2 * z)) (f t) :=
    continuousAt_const.rpow hlin (Or.inl (by norm_num : (2 : ℝ) ≠ 0))
  have hq : Tendsto (fun n => 4 - (2 : ℝ) ^
      (2 * (H n (secondDiffLeft (N n) (i n)) : ℝ))) atTop (𝓝 q) := by
    exact (continuousAt_const.sub hpowCont).tendsto.comp hHi
  have hqj : Tendsto (fun n => 4 - (2 : ℝ) ^
      (2 * (H n (secondDiffLeft (N n) (j n)) : ℝ))) atTop (𝓝 q) := by
    exact (continuousAt_const.sub hpowCont).tendsto.comp hHj
  have hVnorm : Tendsto (fun n => ‖V n‖) atTop (𝓝 (Real.sqrt q)) := by
    have hsquare : Tendsto (fun n => ‖V n‖ ^ 2) atTop (𝓝 q) := by
      apply hq.congr'
      filter_upwards [hNpos] with n hn
      exact (normalizedFrozenSecondIncrement_norm_sq _ _ _ (by positivity)).symm
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    convert hs using 1
    ext n
    simp only [Function.comp_apply, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hZnorm : Tendsto (fun n => ‖Z n‖) atTop (𝓝 (Real.sqrt q)) := by
    have hsquare : Tendsto (fun n => ‖Z n‖ ^ 2) atTop (𝓝 q) := by
      apply hqj.congr'
      filter_upwards [hNpos] with n hn
      exact (normalizedFrozenSecondIncrement_norm_sq _ _ _ (by positivity)).symm
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    convert hs using 1
    ext n
    simp only [Function.comp_apply, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hUnorm : Tendsto (fun n => ‖U n‖) atTop (𝓝 (Real.sqrt q)) := by
    apply tendsto_of_abs_sub_le_zero (fun n => ‖U n‖) (fun n => ‖V n‖) e
      (Real.sqrt q) hVnorm he he0
    filter_upwards [hNpos] with n hn
    exact (abs_norm_sub_norm_le (U n) (V n)).trans (hrem f hf hF (N n) hn (i n))
  have hWnorm : Tendsto (fun n => ‖W n‖) atTop (𝓝 (Real.sqrt q)) := by
    apply tendsto_of_abs_sub_le_zero (fun n => ‖W n‖) (fun n => ‖Z n‖) e
      (Real.sqrt q) hZnorm he he0
    filter_upwards [hNpos] with n hn
    exact (abs_norm_sub_norm_le (W n) (Z n)).trans (hrem f hf hF (N n) hn (j n))
  unfold vectorCorrelation
  have hdiv := hinner.div (hUnorm.mul hWnorm)
    (mul_ne_zero (Real.sqrt_pos.mpr hqpos).ne' (Real.sqrt_pos.mpr hqpos).ne')
  rw [show Real.sqrt q * Real.sqrt q = q by
    simpa only [pow_two] using Real.sq_sqrt hqpos.le] at hdiv
  have hself := secondIncrementCrossLagCovariance_self (f t) x hft.1 hft.2
  change Tendsto
    ((fun n => ⟪gridSecondActual (N n) (midpointSampleHurst f hf.1 (N n)) (i n),
      gridSecondActual (N n) (midpointSampleHurst f hf.1 (N n)) (j n)⟫) /
      (fun n => ‖gridSecondActual (N n) (midpointSampleHurst f hf.1 (N n)) (i n)‖ *
        ‖gridSecondActual (N n) (midpointSampleHurst f hf.1 (N n)) (j n)‖))
      atTop (𝓝 (secondIncrementLagCorrelation (f t) x))
  simpa only [U, W, H, q, secondIncrementLagCorrelation, hself] using hdiv

end Hurst
