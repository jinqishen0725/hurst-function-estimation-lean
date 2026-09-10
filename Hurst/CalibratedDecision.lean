import Hurst.DecisionContinuity

noncomputable section
open Set MeasureTheory
namespace Hurst

/-- A spatially continuous weighted calibrated estimator is measurable as an Ls decision. -/
theorem calibrated_decision_measurable {ι : Type*} [Fintype ι]
    (s : {s : ℝ // 1 ≤ s}) (w : ℝ → ι → ℝ) (hw : ∀ i, Continuous (fun t => w t i))
    (G : ℝ → ℝ) (K : NNReal) (hG : LipschitzWith K G)
    (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, ∑ i, |w t i| ≤ D) :
    Measurable (fun z : ι → ℝ => continuousHurstDecision s
      (fun t => G (smooth (w t) z))
      (hG.continuous.comp (continuous_finsetSum _ (fun i _ => (hw i).mul continuous_const)))) := by
  apply (continuousHurstDecision_map_lipschitz s _ _ ((K : ℝ) * D) (mul_nonneg K.coe_nonneg hD) ?_).continuous.measurable
  intro z v t ht
  have hs : |smooth (w t) z - smooth (w t) v| ≤ D * dist z v := by
    have he := smooth_residual_bound (w t) (z - v) ‖z-v‖ (fun i => by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z-v) i)
    have hid : smooth (w t) z - smooth (w t) v = smooth (w t) (z-v) := by
      simp [smooth, mul_sub, Finset.sum_sub_distrib]
    rw [hid, dist_eq_norm]
    exact he.trans (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _))
  have hg := hG.dist_le_mul (smooth (w t) z) (smooth (w t) v)
  rw [Real.dist_eq, Real.dist_eq] at hg
  exact hg.trans (by nlinarith [mul_le_mul_of_nonneg_left hs K.coe_nonneg])

end Hurst
