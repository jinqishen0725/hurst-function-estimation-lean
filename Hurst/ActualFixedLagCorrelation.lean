import Hurst.FrozenCrossLagCorrelation
import Hurst.CorrelationLimit
import Hurst.FirstStrideGrid

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Along any local pair of stride-first increments whose base points converge
to `t` and whose relative lag is fixed, the actual nonstationary correlation
converges to the frozen correlation at `f t`. -/
theorem hurstHolder_stride_first_fixedLag_correlation_tendsto
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (d : ℕ) (hd : 0 < d) (x : ℝ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (i j : ∀ n, Fin (N n - d))
    (hi : Tendsto (fun n => grid (N n) (i n).val) atTop (𝓝 t))
    (hj : Tendsto (fun n => grid (N n) (j n).val) atTop (𝓝 t))
    (hlag : ∀ᶠ n in atTop,
      grid (N n) (j n).val =
        grid (N n) (i n).val + x * ((d : ℝ) / N n)) :
    Tendsto (fun n => vectorCorrelation
      (gridStrideFirstActual (N n) d
        (midpointSampleHurst f hf.1 (N n)) (i n))
      (gridStrideFirstActual (N n) d
        (midpointSampleHurst f hf.1 (N n)) (j n)))
      atTop (𝓝 (firstIncrementLagCorrelation (f t) x)) := by
  obtain ⟨C, hC, hcov⟩ :=
    hurstHolder_stride_first_covariance p a b M hp ha hb hab hM d hd
  let H := fun n => midpointSampleHurst f hf.1 (N n)
  let U := fun n => gridStrideFirstActual (N n) d (H n) (i n)
  let V := fun n => gridStrideFirstActual (N n) d (H n) (j n)
  let Ui := fun n => normalizedFrozenIncrement
    (H n (strideFirstLeft (N n) d (i n)))
    (grid (N n) (i n).val) ((d : ℝ) / N n)
  let Vj := fun n => normalizedFrozenIncrement
    (H n (strideFirstLeft (N n) d (j n)))
    (grid (N n) (j n).val) ((d : ℝ) / N n)
  have hfcont : ContinuousAt f t := by
    simpa only [iteratedDeriv_zero] using
      (hf.2.1 0 (by have := hurstHolder_floor_pos p hp; omega) t ht).continuousAt
  have hHi : Tendsto
      (fun n => (H n (strideFirstLeft (N n) d (i n)) : ℝ))
      atTop (𝓝 (f t)) := by
    convert hfcont.tendsto.comp hi using 1
    ext n
    rfl
  have hHj : Tendsto
      (fun n => (H n (strideFirstLeft (N n) d (j n)) : ℝ))
      atTop (𝓝 (f t)) := by
    convert hfcont.tendsto.comp hj using 1
    ext n
    rfl
  have hft := hf.1 ht
  have hcross := firstIncrementCrossLagCorrelation_tendsto_self
    (f t) x hft.1 hft.2
    (fun n => (H n (strideFirstLeft (N n) d (i n)) : ℝ))
    (fun n => (H n (strideFirstLeft (N n) d (j n)) : ℝ)) hHi hHj
  have hNpos : ∀ᶠ n in atTop, 0 < N n := hN.eventually_gt_atTop 0
  have he : Tendsto (fun n => gridCovarianceError b C (N n))
      atTop (𝓝 0) := (gridCovarianceError_tendsto b C hb).comp hN
  have he0 : ∀ᶠ n in atTop, 0 ≤ gridCovarianceError b C (N n) := by
    filter_upwards [hNpos] with n hn
    unfold gridCovarianceError
    have hnR : (1 : ℝ) ≤ N n := by exact_mod_cast (show 1 ≤ N n by omega)
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (N n : ℝ) by linarith)
    positivity
  have hfrozen : Tendsto (fun n => ⟪Ui n, Vj n⟫)
      atTop (𝓝 (firstIncrementLagCorrelation (f t) x)) := by
    apply hcross.congr'
    filter_upwards [hlag, hNpos] with n hnlag hn
    dsimp only [Ui, Vj]
    rw [hnlag]
    exact (normalizedFrozenIncrement_cross_parameter_lag
      (H n (strideFirstLeft (N n) d (i n)))
      (H n (strideFirstLeft (N n) d (j n)))
      (grid (N n) (i n).val) ((d : ℝ) / N n) x (by positivity)).symm
  have hinner : Tendsto (fun n => ⟪U n, V n⟫)
      atTop (𝓝 (firstIncrementLagCorrelation (f t) x)) := by
    apply tendsto_of_abs_sub_le_zero (fun n => ⟪U n, V n⟫)
      (fun n => ⟪Ui n, Vj n⟫) (fun n => gridCovarianceError b C (N n))
      _ hfrozen he he0
    filter_upwards [hNpos] with n hn
    exact hcov (N n) hn f hf hF (i n) (j n)
  have hUnorm : Tendsto (fun n => ‖U n‖) atTop (𝓝 1) := by
    apply norm_tendsto_one_of_sq_error U (fun n => gridCovarianceError b C (N n)) he he0
    filter_upwards [hNpos] with n hn
    have hh := hcov (N n) hn f hf hF (i n) (i n)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hh
    simpa only [U, H] using hh
  have hVnorm : Tendsto (fun n => ‖V n‖) atTop (𝓝 1) := by
    apply norm_tendsto_one_of_sq_error V (fun n => gridCovarianceError b C (N n)) he he0
    filter_upwards [hNpos] with n hn
    have hh := hcov (N n) hn f hf hF (j n) (j n)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hh
    simpa only [V, H] using hh
  exact vectorCorrelation_tendsto_of_inner_norm U V
    (firstIncrementLagCorrelation (f t) x) hinner hUnorm hVnorm

end Hurst
