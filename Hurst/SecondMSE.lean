import Hurst.SecondGridLogMean
import Hurst.GridMSE

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem weighted_nonlinear_bias_bound {ι : Type*} [Fintype ι]
    (w h m : ι → ℝ) (phi : ℝ → ℝ) (L c θ β γ D e : ℝ)
    (hL : 1 ≤ L) (hγ : 0 ≤ γ) (he : 0 ≤ e)
    (hw : ∑ i, w i = 1) (hD : ∑ i, |w i| ≤ D)
    (hbias : |smooth w h - θ| ≤ β) (hphi : |smooth w (phi ∘ h) - phi θ| ≤ γ)
    (hm : ∀ i, |m i - (-2 * L * h i + phi (h i) + c)| ≤ e) :
    |smooth w m - (c - 2 * L * θ + phi θ)| ≤ 2 * L * (β + γ) + D * e := by
  let z := fun i => m i - (-2 * L * h i + phi (h i) + c)
  have hz := smooth_residual_bound w z e hm
  have hde := mul_le_mul_of_nonneg_right hD he
  have hmrep : m = (fun i => -2 * L * h i + (phi (h i) + z i) + c) := by funext i; dsimp [z]; ring
  rw [hmrep, log_estimator_decomposition w h (fun i => phi (h i) + z i) L c hw, smooth_add]
  have hid : -2 * L * smooth w h + (smooth w (fun i => phi (h i)) + smooth w z) + c -
      (c - 2 * L * θ + phi θ) =
      -2 * L * (smooth w h - θ) + (smooth w (phi ∘ h) - phi θ) + smooth w z := by unfold Function.comp; ring
  rw [hid]
  have htri := (abs_add_le (-2 * L * (smooth w h - θ) + (smooth w (phi ∘ h) - phi θ)) (smooth w z)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  have habs : |-2 * L| = 2 * L := by rw [abs_of_nonpos (by nlinarith)]; ring
  rw [abs_mul, habs] at htri
  have hscale := mul_le_mul_of_nonneg_left hbias (show 0 ≤ 2 * L by positivity)
  have hscaleγ := mul_le_mul_of_nonneg_right hL hγ
  linarith

/-- Nonlinear q=2 calibration with separate H and log-variance smoothing biases. -/
theorem actual_q2_mse_from_mean_variance (n : ℕ) (hn : 1 < n) (hLn : 1 ≤ Real.log (n : ℝ))
    (H : Fin n → Ioo (0 : ℝ) 1) (w : Fin (n - 2) → ℝ)
    (u θ β γ D e V : ℝ) (hu : u < 1) (hθ : θ ∈ Icc (0 : ℝ) u)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hD0 : 0 ≤ D) (he : 0 ≤ e)
    (hw : ∑ i, w i = 1) (hD : ∑ i, |w i| ≤ D)
    (hfeat : ∀ i, ∑ j, gridSecondCoefficients n i j • gridObservationFeatures n H j ≠ 0)
    (hmean : ∀ i, |(∫ x, Real.log (⟪gridSecondCoefficients n i, x⟫ ^ 2) ∂featureGaussian (gridObservationFeatures n H)) -
      (-2 * (H (secondDiffLeft n i) : ℝ) * Real.log n + q2LogCorrection (H (secondDiffLeft n i)) + gaussianLogSquareMean)| ≤ e)
    (hbias : |smooth w (fun i => (H (secondDiffLeft n i) : ℝ)) - θ| ≤ β)
    (hphibias : |smooth w (fun i => q2LogCorrection (H (secondDiffLeft n i))) - q2LogCorrection θ| ≤ γ)
    (hvar : Var[gaussianLogStatistic w (gridSecondCoefficients n); featureGaussian (gridObservationFeatures n H)] ≤ V) :
    (∫ x, (boundedInverse (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u
        (gaussianLogStatistic w (gridSecondCoefficients n) x) - θ) ^ 2 ∂featureGaussian (gridObservationFeatures n H)) ≤
      V / (4 * Real.log n ^ 2) + 2 * (β + γ) ^ 2 + D ^ 2 * e ^ 2 / (2 * Real.log n ^ 2) := by
  have hL : 0 < Real.log (n : ℝ) := by linarith
  have hX := gaussianLogStatistic_memLp_two (gridObservationFeatures n H) w (gridSecondCoefficients n) hfeat
  have hmse := boundedInverse_mse (featureGaussian (gridObservationFeatures n H))
    (gaussianLogStatistic w (gridSecondCoefficients n)) (calibrationTwo (Real.log n) gaussianLogSquareMean)
    0 u (2 * Real.log n) θ (by positivity) (hθ.1.trans hθ.2)
    (calibrationTwo_continuousOn _ _ u hu) (calibrationTwo_strongDecrease _ _ u hu) hθ hX
  let m := fun i => ∫ x, Real.log (⟪gridSecondCoefficients n i, x⟫ ^ 2) ∂featureGaussian (gridObservationFeatures n H)
  have hmu : (∫ x, gaussianLogStatistic w (gridSecondCoefficients n) x ∂featureGaussian (gridObservationFeatures n H)) = smooth w m := by
    unfold gaussianLogStatistic smooth
    rw [integral_finsetSum _ (fun i _ => ((featureGaussian_log_square_memLp_two _ _ (hfeat i)).integrable (by norm_num)).const_mul (w i))]
    simp only [integral_const_mul]
    rfl
  have hmb := weighted_nonlinear_bias_bound w (fun i => (H (secondDiffLeft n i) : ℝ)) m q2LogCorrection
    (Real.log n) gaussianLogSquareMean θ β γ D e hLn hγ he hw hD hbias hphibias
    (by intro i; convert! hmean i using 1 <;> congr 1 <;> ring)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hmb 2
  rw [sq_abs] at hsq
  have hsq' : (smooth w m - (gaussianLogSquareMean - 2 * Real.log n * θ + q2LogCorrection θ)) ^ 2 ≤
      8 * Real.log n ^ 2 * (β + γ) ^ 2 + 2 * D ^ 2 * e ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.log n * (β + γ) - D * e)]
  rw [hmu] at hmse
  have heq : calibrationTwo (Real.log n) gaussianLogSquareMean θ =
      gaussianLogSquareMean - 2 * Real.log n * θ + q2LogCorrection θ := rfl
  rw [heq] at hmse
  have hbound := div_le_div_of_nonneg_right (add_le_add hvar hsq') (show 0 ≤ (2 * Real.log (n : ℝ)) ^ 2 by positivity)
  apply hmse.trans (hbound.trans_eq ?_)
  field_simp
  ring

end Hurst
