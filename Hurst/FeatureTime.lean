import Hurst.FeatureSecondOrder
import Hurst.SpectralTime

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

theorem rawHarmonizableFeature_time_increment_norm (h : Ioo (0 : ℝ) 1) (t l : ℝ) (hl : 0 < l) :
    ‖rawHarmonizableFeature h (t + l) - rawHarmonizableFeature h t‖ =
      l ^ (h : ℝ) * ‖rawHarmonizableFeature h 1‖ := by
  let A := (Real.sqrt 2 * harmonizableD h)⁻¹
  have hA : 0 < A := inv_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by norm_num))
    (harmonizableD_pos h h.property.1 h.property.2))
  have hi := harmonizableFeature_increment_norm_sq h (t + l) t
  rw [harmonizableFeature_eq_normalized_raw, harmonizableFeature_eq_normalized_raw,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hA, add_sub_cancel_left, abs_of_pos hl] at hi
  have h1 := harmonizableFeature_norm_sq h 1
  rw [harmonizableFeature_eq_normalized_raw, norm_smul, Real.norm_eq_abs, abs_of_pos hA] at h1
  norm_num only [abs_one, Real.one_rpow] at h1
  have he : l ^ (2 * (h : ℝ)) = (l ^ (h : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast (l ^ (h : ℝ)) 2, ← Real.rpow_mul hl.le]
    congr 1
    ring
  rw [he] at hi
  have hsq : ‖rawHarmonizableFeature h (t + l) - rawHarmonizableFeature h t‖ ^ 2 =
      (l ^ (h : ℝ) * ‖rawHarmonizableFeature h 1‖) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hA.ne')
    calc
      A ^ 2 * ‖rawHarmonizableFeature h (t + l) - rawHarmonizableFeature h t‖ ^ 2 =
          (A * ‖rawHarmonizableFeature h (t + l) - rawHarmonizableFeature h t‖) ^ 2 := by ring
      _ = (l ^ (h : ℝ)) ^ 2 := hi
      _ = (l ^ (h : ℝ)) ^ 2 * (A * ‖rawHarmonizableFeature h 1‖) ^ 2 := by rw [h1, mul_one]
      _ = A ^ 2 * (l ^ (h : ℝ) * ‖rawHarmonizableFeature h 1‖) ^ 2 := by ring
  have hp := mul_nonneg (Real.rpow_nonneg hl.le (h : ℝ)) (norm_nonneg (rawHarmonizableFeature h 1))
  nlinarith [norm_nonneg (rawHarmonizableFeature h (t + l) - rawHarmonizableFeature h t)]

theorem harmonizableSlopeFeature_time_increment_bound (a b : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → ∀ t l : ℝ, 0 < l →
      ‖harmonizableSlopeFeature h (t + l) - harmonizableSlopeFeature h t‖ ≤
        C * l ^ (h : ℝ) * (1 + |Real.log l|) := by
  obtain ⟨A, hA, L, hL, ha', haLip⟩ := harmonizableNormalizer_uniform_control a b ha hb hab
  obtain ⟨D, hD, hd⟩ := harmonizableNormalizerSlope_uniform_bound a b ha hb
  obtain ⟨U, hU, Q, hQ, hu, huLip⟩ := rawHarmonizableFeature_uniform_control a b ha hb
  obtain ⟨V, hV, hv⟩ := rawHarmonizableSlopeFeature_time_increment_bound a b ha hb
  refine ⟨D * U + A * V, by positivity, ?_⟩
  intro h hh t l hl
  have he : harmonizableSlopeFeature h (t + l) - harmonizableSlopeFeature h t =
      harmonizableNormalizerSlope h • (rawHarmonizableFeature h (t + l) - rawHarmonizableFeature h t) +
      harmonizableNormalizer h • (rawHarmonizableSlopeFeature h (t + l) - rawHarmonizableSlopeFeature h t) := by
    unfold harmonizableSlopeFeature
    module
  rw [he]
  have hr : ‖rawHarmonizableFeature h (t + l) - rawHarmonizableFeature h t‖ ≤ l ^ (h : ℝ) * U := by
    rw [rawHarmonizableFeature_time_increment_norm h t l hl]
    exact mul_le_mul_of_nonneg_left (hu h hh 1 (by norm_num)) (Real.rpow_nonneg hl.le _)
  have h1 := mul_le_mul (hd h hh) hr (norm_nonneg _) hD
  have h2 := mul_le_mul (ha' h hh) (hv h hh t l hl) (norm_nonneg _) hA
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Real.norm_eq_abs]
  have h3 := add_le_add h1 h2
  have hp := mul_nonneg (mul_nonneg hD hU) (mul_nonneg (Real.rpow_nonneg hl.le (h : ℝ)) (abs_nonneg (Real.log l)))
  nlinarith

end Hurst
