import Hurst.HurstVariation
import Hurst.GaussianLog
import Hurst.Analytic

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def normalizedFrozenIncrement (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (ℓ ^ (-(h : ℝ))) • (harmonizableFeature h (s + ℓ) - harmonizableFeature h s)

def normalizedVaryingIncrement (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (ℓ ^ (-(h : ℝ))) • (harmonizableFeature k (s + ℓ) - harmonizableFeature h s)

theorem normalizedFrozenIncrement_norm_sq (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) (hℓ : 0 < ℓ) :
    ‖normalizedFrozenIncrement h s ℓ‖ ^ 2 = 1 := by
  rw [normalizedFrozenIncrement, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    harmonizableFeature_increment_norm_sq, add_sub_cancel_left, abs_of_pos hℓ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le, ← Real.rpow_add hℓ]
  convert Real.rpow_zero ℓ using 1; congr 1; ring

theorem normalizedFrozenIncrement_norm (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) (hℓ : 0 < ℓ) :
    ‖normalizedFrozenIncrement h s ℓ‖ = 1 := by
  have he := normalizedFrozenIncrement_norm_sq h s ℓ hℓ
  nlinarith [norm_nonneg (normalizedFrozenIncrement h s ℓ)]

/-- A uniform first-order varying-Hurst remainder, valid even for intervals starting at zero. -/
theorem normalizedVaryingIncrement_uniform_remainder (a b : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s ℓ B : ℝ, |s + ℓ| ≤ 1 → 0 < ℓ → ℓ ≤ 1 → 0 ≤ B → |(k : ℝ) - h| ≤ B * ℓ →
      ‖normalizedVaryingIncrement h k s ℓ - normalizedFrozenIncrement h s ℓ‖ ≤
        C * B * ℓ ^ (1 - b) := by
  obtain ⟨C, hC, hLip⟩ := harmonizableFeature_uniform_parameter_lipschitz a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro h k hh hk s ℓ B hs hℓ hℓ1 hB hhk
  have he : normalizedVaryingIncrement h k s ℓ - normalizedFrozenIncrement h s ℓ =
      (ℓ ^ (-(h : ℝ))) • (harmonizableFeature k (s + ℓ) - harmonizableFeature h (s + ℓ)) := by
    unfold normalizedVaryingIncrement normalizedFrozenIncrement
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hℓ _)]
  calc
    _ ≤ ℓ ^ (-(h : ℝ)) * (C * (B * ℓ)) :=
      mul_le_mul_of_nonneg_left ((hLip k h hk hh (s + ℓ) hs).trans
        (mul_le_mul_of_nonneg_left hhk hC)) (Real.rpow_nonneg hℓ.le _)
    _ = C * B * ℓ ^ (1 - (h : ℝ)) := by
      rw [Real.rpow_sub hℓ, Real.rpow_one, Real.rpow_neg hℓ.le]
      ring
    _ ≤ C * B * ℓ ^ (1 - b) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hℓ hℓ1 (by linarith [hh.2])) (mul_nonneg hC hB)

theorem norm_square_error_from_unit {E : Type*} [SeminormedAddCommGroup E]
    (u v : E) (ε : ℝ) (hε : 0 ≤ ε) (hu : ‖u‖ = 1) (he : ‖v - u‖ ≤ ε) :
    |‖v‖ ^ 2 - 1| ≤ ε * (2 + ε) := by
  have hd : |‖v‖ - 1| ≤ ε := by simpa only [hu] using (abs_norm_sub_norm_le v u).trans he
  have hv : ‖v‖ ≤ 1 + ε := by linarith [(abs_le.mp hd).2]
  rw [show ‖v‖ ^ 2 - 1 = (‖v‖ - 1) * (‖v‖ + 1) by ring, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ‖v‖ + 1)]
  exact mul_le_mul hd (by linarith : ‖v‖ + 1 ≤ 2 + ε) (by positivity) hε

theorem norm_square_lower_from_unit {E : Type*} [SeminormedAddCommGroup E]
    (u v : E) (ε : ℝ) (hu : ‖u‖ = 1) (he : ‖v - u‖ ≤ ε) (hε : ε ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ ‖v‖ ^ 2 := by
  have hd : |‖v‖ - 1| ≤ ε := by simpa only [hu] using (abs_norm_sub_norm_le v u).trans he
  nlinarith [(abs_le.mp hd).1, norm_nonneg v]

theorem log_norm_square_error_from_unit {E : Type*} [SeminormedAddCommGroup E]
    (u v : E) (ε : ℝ) (hε : 0 ≤ ε) (hu : ‖u‖ = 1) (he : ‖v - u‖ ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    |Real.log (‖v‖ ^ 2)| ≤ 10 * ε := by
  have hlow := norm_square_lower_from_unit u v ε hu he hεhalf
  have hlog := log_lipschitz_from_below (‖v‖ ^ 2) 1 (1 / 4) (by norm_num) hlow (by norm_num)
  rw [Real.log_one, sub_zero] at hlog
  have herr := norm_square_error_from_unit u v ε hε hu he
  calc
    _ ≤ |‖v‖ ^ 2 - 1| / (1 / 4) := hlog
    _ ≤ (ε * (2 + ε)) / (1 / 4) := by gcongr
    _ ≤ 10 * ε := by nlinarith

def varyingPairFeatures (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Fin 2 → Lp ℂ 2 (volume : Measure ℝ) :=
  ![harmonizableFeature h s, harmonizableFeature k (s + ℓ)]

def firstDifferenceWeights : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-1, 1]

def varyingPair (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  featureGaussian (varyingPairFeatures h k s ℓ)

theorem firstDifferenceWeights_inner (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪firstDifferenceWeights, x⟫ = x 1 - x 0 := by
  simp [firstDifferenceWeights, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem firstDifferenceWeights_feature (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) :
    (∑ i : Fin 2, firstDifferenceWeights i • varyingPairFeatures h k s ℓ i) =
      harmonizableFeature k (s + ℓ) - harmonizableFeature h s := by
  simp [firstDifferenceWeights, varyingPairFeatures, Fin.sum_univ_two]
  module

theorem varyingIncrement_normalized_identity (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) (hℓ : 0 < ℓ) :
    harmonizableFeature k (s + ℓ) - harmonizableFeature h s =
      (ℓ ^ (h : ℝ)) • normalizedVaryingIncrement h k s ℓ := by
  rw [normalizedVaryingIncrement, smul_smul, ← Real.rpow_add hℓ, add_neg_cancel,
    Real.rpow_zero, one_smul]

theorem varyingPair_log_mean_from_remainder (h k : Ioo (0 : ℝ) 1) (s ℓ ε : ℝ)
    (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hrem : ‖normalizedVaryingIncrement h k s ℓ - normalizedFrozenIncrement h s ℓ‖ ≤ ε) :
    |(∫ x, Real.log ((x 1 - x 0) ^ 2) ∂varyingPair h k s ℓ) -
      (2 * (h : ℝ) * Real.log ℓ + gaussianLogSquareMean)| ≤ 10 * ε := by
  have hu := normalizedFrozenIncrement_norm h s ℓ hℓ
  have hlow := norm_square_lower_from_unit _ _ ε hu hrem hεhalf
  have hv : normalizedVaryingIncrement h k s ℓ ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hlow
    norm_num at hlow
  have hfeat : ∑ i : Fin 2, firstDifferenceWeights i • varyingPairFeatures h k s ℓ i ≠ 0 := by
    rw [firstDifferenceWeights_feature, varyingIncrement_normalized_identity h k s ℓ hℓ]
    exact smul_ne_zero (Real.rpow_pos_of_pos hℓ _).ne' hv
  have hm := featureGaussian_expected_log_square (varyingPairFeatures h k s ℓ) firstDifferenceWeights hfeat
  simp_rw [firstDifferenceWeights_inner] at hm
  rw [firstDifferenceWeights_feature, varyingIncrement_normalized_identity h k s ℓ hℓ,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.log_mul (pow_ne_zero 2 (Real.rpow_pos_of_pos hℓ _).ne') (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)),
    Real.log_pow, Real.log_rpow hℓ] at hm
  change (∫ x, Real.log ((x 1 - x 0) ^ 2) ∂varyingPair h k s ℓ) = _ at hm
  rw [hm]
  convert log_norm_square_error_from_unit _ _ ε hε hu hrem hεhalf using 1 <;> congr 1 <;> ring

/-- Actual Gaussian first-difference mean, with the parameter error obtained from spectral features. -/
theorem varyingPair_uniform_log_mean (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s ℓ B : ℝ, |s + ℓ| ≤ 1 → 0 < ℓ → ℓ ≤ 1 → 0 ≤ B → |(k : ℝ) - h| ≤ B * ℓ →
      C * B * ℓ ^ (1 - b) ≤ 1 / 2 →
      |(∫ x, Real.log ((x 1 - x 0) ^ 2) ∂varyingPair h k s ℓ) -
        (2 * (h : ℝ) * Real.log ℓ + gaussianLogSquareMean)| ≤ 10 * C * B * ℓ ^ (1 - b) := by
  obtain ⟨C, hC, hrem⟩ := normalizedVaryingIncrement_uniform_remainder a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro h k hh hk s ℓ B hs hℓ hℓ1 hB hhk hsmall
  simpa only [mul_assoc] using varyingPair_log_mean_from_remainder h k s ℓ (C * B * ℓ ^ (1 - b))
    hℓ (by positivity) hsmall (hrem h k hh hk s ℓ B hs hℓ hℓ1 hB hhk)

end Hurst
