import Hurst.GridLogMeanSharp
import Hurst.InverseRepair
import Hurst.LocalBias

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem weighted_affine_bias_bound {ι : Type*} [Fintype ι]
    (w h m : ι → ℝ) (L c θ β D e : ℝ) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hw : ∑ i, w i = 1) (hD : ∑ i, |w i| ≤ D)
    (hbias : |smooth w h - θ| ≤ β)
    (hm : ∀ i, |m i - (-2 * L * h i + c)| ≤ e) :
    |smooth w m - (c - 2 * L * θ)| ≤ 2 * L * β + D * e := by
  let z := fun i => m i - (-2 * L * h i + c)
  have hz := smooth_residual_bound w z e hm
  have hde := mul_le_mul_of_nonneg_right hD he
  have hmrep : m = (fun i => -2 * L * h i + z i + c) := by funext i; dsimp [z]; ring
  rw [hmrep, log_estimator_decomposition w h z L c hw]
  have hid : -2 * L * smooth w h + smooth w z + c - (c - 2 * L * θ) =
      -2 * L * (smooth w h - θ) + smooth w z := by ring
  rw [hid]
  have htri := abs_add_le (-2 * L * (smooth w h - θ)) (smooth w z)
  have habs : |-2 * L| = 2 * L := by rw [abs_of_nonpos (by nlinarith)]; ring
  rw [abs_mul, habs] at htri
  have hscale := mul_le_mul_of_nonneg_left hbias (show 0 ≤ 2 * L by positivity)
  linarith

/-- Finite-sample MSE of the actual clipped first-difference estimator. -/
theorem actual_q1_mse_from_mean_variance (n : ℕ) (hn : 1 < n)
    (H : Fin n → Ioo (0 : ℝ) 1) (w : Fin (n - 1) → ℝ)
    (θ β D e V : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (hβ : 0 ≤ β) (hD0 : 0 ≤ D) (he : 0 ≤ e)
    (hw : ∑ i, w i = 1) (hD : ∑ i, |w i| ≤ D)
    (hfeat : ∀ i, ∑ j, gridDifferenceCoefficients n i j • gridObservationFeatures n H j ≠ 0)
    (hmean : ∀ i, |(∫ x, Real.log (⟪gridDifferenceCoefficients n i, x⟫ ^ 2) ∂featureGaussian (gridObservationFeatures n H)) -
      (-2 * (H (firstDiffLeft n i) : ℝ) * Real.log n + gaussianLogSquareMean)| ≤ e)
    (hbias : |smooth w (fun i => (H (firstDiffLeft n i) : ℝ)) - θ| ≤ β)
    (hvar : Var[gaussianLogStatistic w (gridDifferenceCoefficients n); featureGaussian (gridObservationFeatures n H)] ≤ V) :
    (∫ x, (boundedInverse (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1
        (gaussianLogStatistic w (gridDifferenceCoefficients n) x) - θ) ^ 2 ∂featureGaussian (gridObservationFeatures n H)) ≤
      V / (4 * Real.log n ^ 2) + 2 * β ^ 2 + D ^ 2 * e ^ 2 / (2 * Real.log n ^ 2) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hX := gaussianLogStatistic_memLp_two (gridObservationFeatures n H) w (gridDifferenceCoefficients n) hfeat
  have hmse := boundedInverse_mse (featureGaussian (gridObservationFeatures n H))
    (gaussianLogStatistic w (gridDifferenceCoefficients n)) (calibrationOne (Real.log n) gaussianLogSquareMean)
    0 1 (2 * Real.log n) θ (by positivity) (by norm_num)
    (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _) hθ hX
  let m := fun i => ∫ x, Real.log (⟪gridDifferenceCoefficients n i, x⟫ ^ 2) ∂featureGaussian (gridObservationFeatures n H)
  have hmu : (∫ x, gaussianLogStatistic w (gridDifferenceCoefficients n) x ∂featureGaussian (gridObservationFeatures n H)) = smooth w m := by
    unfold gaussianLogStatistic smooth
    rw [integral_finsetSum _ (fun i _ => ((featureGaussian_log_square_memLp_two _ _ (hfeat i)).integrable (by norm_num)).const_mul (w i))]
    simp only [integral_const_mul]
    rfl
  have hmb := weighted_affine_bias_bound w (fun i => (H (firstDiffLeft n i) : ℝ)) m
    (Real.log n) gaussianLogSquareMean θ β D e hL.le he hw hD hbias (by intro i; convert! hmean i using 1 <;> congr 1 <;> ring)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hmb 2
  rw [sq_abs] at hsq
  have hsq' : (smooth w m - (gaussianLogSquareMean - 2 * Real.log n * θ)) ^ 2 ≤
      8 * Real.log n ^ 2 * β ^ 2 + 2 * D ^ 2 * e ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.log n * β - D * e)]
  rw [hmu, calibrationOne] at hmse
  have hd : 0 < (2 * Real.log (n : ℝ)) ^ 2 := by positivity
  have hbound := div_le_div_of_nonneg_right (add_le_add hvar hsq') hd.le
  apply hmse.trans (hbound.trans_eq ?_)
  field_simp
  ring

end Hurst
