import Hurst.SpectralSecondOrder
import Hurst.SmoothTaylor

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

theorem product_quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a0 a1 da d A R S U L D : ℝ) (u0 u1 du : E)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hU : 0 ≤ U) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (ha : |a1| ≤ A) (hu : ‖u0‖ ≤ U) (hd : ‖du‖ ≤ D)
    (hru : ‖u1 - u0 - d • du‖ ≤ R * |d| ^ 2)
    (hra : |a1 - a0 - d * da| ≤ S * |d| ^ 2) (hlip : |a1 - a0| ≤ L * |d|) :
    ‖a1 • u1 - a0 • u0 - d • (da • u0 + a0 • du)‖ ≤ (A * R + S * U + L * D) * |d| ^ 2 := by
  have he : a1 • u1 - a0 • u0 - d • (da • u0 + a0 • du) =
      a1 • (u1 - u0 - d • du) + (a1 - a0 - d * da) • u0 + (d * (a1 - a0)) • du := by module
  rw [he]
  have h1 := mul_le_mul ha hru (norm_nonneg _) hA
  have h2 := mul_le_mul hra hu (norm_nonneg _) (by positivity : 0 ≤ S * |d| ^ 2)
  have h3a := mul_le_mul_of_nonneg_left hlip (abs_nonneg d)
  have h3 := mul_le_mul h3a hd (norm_nonneg _) (by positivity : 0 ≤ |d| * (L * |d|))
  calc
    _ ≤ ‖a1 • (u1 - u0 - d • du)‖ + ‖(a1 - a0 - d * da) • u0‖ + ‖(d * (a1 - a0)) • du‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = |a1| * ‖u1 - u0 - d • du‖ + |a1 - a0 - d * da| * ‖u0‖ + (|d| * |a1 - a0|) * ‖du‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul]
    _ ≤ A * (R * |d| ^ 2) + S * |d| ^ 2 * U + (|d| * (L * |d|)) * D := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

def harmonizableSlopeFeature (h : Ioo (0 : ℝ) 1) (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  harmonizableNormalizerSlope h • rawHarmonizableFeature h t +
    harmonizableNormalizer h • rawHarmonizableSlopeFeature h t

/-- Quadratic parameter expansion of the fully normalized actual spectral feature. -/
theorem harmonizableFeature_uniform_quadratic_remainder (a b : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ t : ℝ, |t| ≤ 1 →
      ‖harmonizableFeature k t - harmonizableFeature h t - ((k : ℝ) - h) • harmonizableSlopeFeature h t‖ ≤
        C * |(k : ℝ) - h| ^ 2 := by
  obtain ⟨A, hA, L, hL, hnormal, hnormalLip⟩ := harmonizableNormalizer_uniform_control a b ha hb hab
  obtain ⟨R, hR, hraw⟩ := rawHarmonizableFeature_uniform_quadratic_remainder a b ha hb
  obtain ⟨S, hS, hscalar⟩ := harmonizableNormalizer_quadratic_remainder a b ha hb
  obtain ⟨U, hU, Q, hQ, hu, huLip⟩ := rawHarmonizableFeature_uniform_control a b ha hb
  obtain ⟨D, hD, hd⟩ := rawHarmonizableSlopeFeature_uniform_bound a b ha hb
  refine ⟨A * R + S * U + L * D, by positivity, ?_⟩
  intro h k hh hk t ht
  rw [harmonizableFeature_eq_normalized_raw, harmonizableFeature_eq_normalized_raw]
  exact product_quadratic_remainder (harmonizableNormalizer h) (harmonizableNormalizer k)
    (harmonizableNormalizerSlope h) ((k : ℝ) - h) A R S U L D
    (rawHarmonizableFeature h t) (rawHarmonizableFeature k t) (rawHarmonizableSlopeFeature h t)
    hA hS hU hL hD (hnormal k hk) (hu h hh t ht) (hd h hh t ht)
    (hraw h k hh hk t ht) (hscalar h k hh hk) (hnormalLip k hk h hh)

theorem harmonizableNormalizerSlope_uniform_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 0, ∀ h ∈ Icc a b, |harmonizableNormalizerSlope h| ≤ C := by
  obtain ⟨C, hC, hc⟩ := harmonizableNormalizer_all_derivatives_uniform a b ha hb 1
  refine ⟨C, hC, ?_⟩
  intro h hh
  have hd := (harmonizableNormalizer_hasDerivAt h (ha.trans_le hh.1) (hh.2.trans_lt hb)).deriv
  simpa only [iteratedDeriv_one, hd] using hc h hh

theorem harmonizableSlopeFeature_uniform_bound (a b : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → ∀ t : ℝ, |t| ≤ 1 →
      ‖harmonizableSlopeFeature h t‖ ≤ C := by
  obtain ⟨A, hA, L, hL, hnormal, hnormalLip⟩ := harmonizableNormalizer_uniform_control a b ha hb hab
  obtain ⟨D, hD, hnormalSlope⟩ := harmonizableNormalizerSlope_uniform_bound a b ha hb
  obtain ⟨U, hU, Q, hQ, hu, huLip⟩ := rawHarmonizableFeature_uniform_control a b ha hb
  obtain ⟨V, hV, hv⟩ := rawHarmonizableSlopeFeature_uniform_bound a b ha hb
  refine ⟨D * U + A * V, by positivity, ?_⟩
  intro h hh t ht
  unfold harmonizableSlopeFeature
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Real.norm_eq_abs]
  exact add_le_add (mul_le_mul (hnormalSlope h hh) (hu h hh t ht) (norm_nonneg _) hD)
    (mul_le_mul (hnormal h hh) (hv h hh t ht) (norm_nonneg _) hA)

end Hurst
