import Hurst.FirstLongKernelAsymptotic
import Hurst.FirstStrideGrid
import Hurst.CorrelationLimit
import Hurst.FirstScaleLongRates

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- The explicit actual-to-frozen covariance error remains negligible at the
q=1 long-memory scale for the concrete choice `nδ = log(n)^2`. -/
theorem longMemoryScale_gridCovarianceError_tendsto
    (h b C : ℝ) (hlong : 3 / 4 < h) (hb : b < 1) (hC : 0 ≤ C) :
    Tendsto (fun n : ℕ => ((Real.log n) ^ 2) ^ (2 - 2 * h) *
      gridCovarianceError b C n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper := gridCovarianceError_mesh_log_sq_tendsto b C hb
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
      (by
        unfold gridCovarianceError
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hlog0 := Real.log_nonneg
          (show (1 : ℝ) ≤ 2 * n by linarith)
        positivity)
  · filter_upwards [eventually_ge_atTop 1,
      hlog.eventually_ge_atTop 1] with n hn hln
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hL : Real.log (n : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
      have := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      linarith
    have hmesh1 : (1 : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
      have hlog2n := Real.log_nonneg
        (show (1 : ℝ) ≤ 2 * n by
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith)
      linarith
    have hbase : (1 : ℝ) ≤ (Real.log n) ^ 2 := by nlinarith
    have hexp : 2 - 2 * h ≤ (1 / 2 : ℝ) := by linarith
    have hscale : ((Real.log n) ^ 2) ^ (2 - 2 * h) ≤
        (1 + Real.log (2 * (n : ℝ))) ^ 2 := by
      calc
        _ ≤ ((Real.log n) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hexp
        _ = Real.log n := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (by linarith)]
        _ ≤ 1 + Real.log (2 * (n : ℝ)) := hL
        _ ≤ (1 + Real.log (2 * (n : ℝ))) ^ 2 := by nlinarith
    have he0 : 0 ≤ gridCovarianceError b C n := by
      unfold gridCovarianceError
      have hlog0 := Real.log_nonneg
        (show (1 : ℝ) ≤ 2 * n by
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith)
      positivity
    exact mul_le_mul_of_nonneg_right hscale he0

/-- Transfer a scaled frozen-kernel entry limit to the corresponding actual
nonstationary q=1 correlation.  The only rate condition is that the explicit
actual-to-frozen covariance error is negligible at the requested scale. -/
theorem hurstHolder_stride_first_scaled_actual_correlation_of_frozen
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (d : ℕ) (hd : 0 < d) :
    ∃ C ≥ 0, ∀ (c : ℕ → ℝ) (K : ℝ)
      (i j : ∀ n, Fin (n - d)),
      (∀ᶠ n in atTop, 0 ≤ c n) →
      Tendsto (fun n => c n * gridCovarianceError b C n) atTop (𝓝 0) →
      Tendsto (fun n => c n *
        ⟪normalizedFrozenIncrement
            (midpointSampleHurst f hf.1 n (strideFirstLeft n d (i n)))
            (grid n (i n).val) ((d : ℝ) / n),
          normalizedFrozenIncrement
            (midpointSampleHurst f hf.1 n (strideFirstLeft n d (j n)))
            (grid n (j n).val) ((d : ℝ) / n)⟫) atTop (𝓝 K) →
      Tendsto (fun n => c n * vectorCorrelation
        (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) (i n))
        (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) (j n)))
        atTop (𝓝 K) := by
  obtain ⟨C, hC, hcov⟩ :=
    hurstHolder_stride_first_covariance p a b M hp ha hb hab hM d hd
  refine ⟨C, hC, ?_⟩
  intro c K i j hc hce hfrozen
  let H := fun n => midpointSampleHurst f hf.1 n
  let U := fun n => gridStrideFirstActual n d (H n) (i n)
  let V := fun n => gridStrideFirstActual n d (H n) (j n)
  let Ui := fun n => normalizedFrozenIncrement
    (H n (strideFirstLeft n d (i n))) (grid n (i n).val) ((d : ℝ) / n)
  let Vj := fun n => normalizedFrozenIncrement
    (H n (strideFirstLeft n d (j n))) (grid n (j n).val) ((d : ℝ) / n)
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have he : Tendsto (fun n => gridCovarianceError b C n) atTop (𝓝 0) :=
    gridCovarianceError_tendsto b C hb
  have he0 : ∀ᶠ n : ℕ in atTop, 0 ≤ gridCovarianceError b C n := by
    filter_upwards [hnpos] with n hn
    unfold gridCovarianceError
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  have hscaledInner : Tendsto (fun n => c n * ⟪U n, V n⟫)
      atTop (𝓝 K) := by
    apply tendsto_of_abs_sub_le_zero
      (fun n => c n * ⟪U n, V n⟫)
      (fun n => c n * ⟪Ui n, Vj n⟫)
      (fun n => c n * gridCovarianceError b C n)
      K (by simpa only [Ui, Vj, H] using hfrozen) hce
    · filter_upwards [hc, he0] with n hcn hen
      exact mul_nonneg hcn hen
    · filter_upwards [hc, hnpos] with n hcn hn
      have hpert := hcov n hn f hf hF (i n) (j n)
      rw [← mul_sub, abs_mul, abs_of_nonneg hcn]
      exact mul_le_mul_of_nonneg_left hpert hcn
  have hUnorm : Tendsto (fun n => ‖U n‖) atTop (𝓝 1) := by
    apply norm_tendsto_one_of_sq_error U (fun n => gridCovarianceError b C n) he he0
    filter_upwards [hnpos] with n hn
    have hpert := hcov n hn f hf hF (i n) (i n)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hpert
    simpa only [U, Ui, H] using hpert
  have hVnorm : Tendsto (fun n => ‖V n‖) atTop (𝓝 1) := by
    apply norm_tendsto_one_of_sq_error V (fun n => gridCovarianceError b C n) he he0
    filter_upwards [hnpos] with n hn
    have hpert := hcov n hn f hf hF (j n) (j n)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hpert
    simpa only [V, Vj, H] using hpert
  have hquot := hscaledInner.div (hUnorm.mul hVnorm)
    (by norm_num : (1 : ℝ) * 1 ≠ 0)
  have hquot' : Tendsto
      ((fun n => c n * ⟪U n, V n⟫) /
        (fun n => ‖U n‖ * ‖V n‖)) atTop (𝓝 K) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [] with n
  unfold vectorCorrelation
  dsimp only [U, V, H]
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Concrete `log(n)^2` local-window specialization of the actual correlation
transfer.  Thus the remaining pointwise step-kernel work is entirely the
frozen cross-parameter entry limit; the actual mBm perturbation is discharged. -/
theorem hurstHolder_stride_first_logSquared_actual_correlation_of_frozen
    (p a b M h : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (hlong : 3 / 4 < h)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (d : ℕ) (hd : 0 < d) (K : ℝ) (i j : ∀ n, Fin (n - d))
    (hfrozen : Tendsto (fun n : ℕ => ((Real.log n) ^ 2) ^ (2 - 2 * h) *
      ⟪normalizedFrozenIncrement
          (midpointSampleHurst f hf.1 n (strideFirstLeft n d (i n)))
          (grid n (i n).val) ((d : ℝ) / n),
        normalizedFrozenIncrement
          (midpointSampleHurst f hf.1 n (strideFirstLeft n d (j n)))
          (grid n (j n).val) ((d : ℝ) / n)⟫) atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => ((Real.log n) ^ 2) ^ (2 - 2 * h) *
      vectorCorrelation
        (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) (i n))
        (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) (j n)))
      atTop (𝓝 K) := by
  obtain ⟨C, hC, htransfer⟩ :=
    hurstHolder_stride_first_scaled_actual_correlation_of_frozen
      p a b M hp ha hb hab hM f hf hF d hd
  apply htransfer (fun n => ((Real.log n) ^ 2) ^ (2 - 2 * h)) K i j
  · exact Eventually.of_forall (fun _ => Real.rpow_nonneg (sq_nonneg _) _)
  · exact longMemoryScale_gridCovarianceError_tendsto h b C hlong hb hC
  · exact hfrozen

end Hurst
