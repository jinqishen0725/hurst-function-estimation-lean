import Hurst.Harmonizable
import Hurst.GaussianLog

/-! Actual first and second differences, the two orders retained on the main line. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Hurst

theorem harmonizableFeature_increment_inner (h : Ioo (0 : ℝ) 1) (a b c d : ℝ) :
    ⟪harmonizableFeature h a - harmonizableFeature h b,
      harmonizableFeature h c - harmonizableFeature h d⟫ =
      (|a - d| ^ (2 * (h : ℝ)) + |b - c| ^ (2 * (h : ℝ)) -
        |a - c| ^ (2 * (h : ℝ)) - |b - d| ^ (2 * (h : ℝ))) / 2 := by
  simp only [inner_sub_left, inner_sub_right, harmonizableFeature_inner_same]
  ring

def secondDifferenceFeature (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (harmonizableFeature h s - harmonizableFeature h (s + ℓ)) -
    (harmonizableFeature h (s + ℓ) - harmonizableFeature h (s + 2 * ℓ))

theorem secondDifferenceFeature_norm_sq (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) :
    ‖secondDifferenceFeature h s ℓ‖ ^ 2 =
      (4 - (2 : ℝ) ^ (2 * (h : ℝ))) * |ℓ| ^ (2 * (h : ℝ)) := by
  rw [secondDifferenceFeature, norm_sub_sq_real, harmonizableFeature_increment_norm_sq,
    harmonizableFeature_increment_norm_sq, harmonizableFeature_increment_inner]
  have h0 : 2 * (h : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num) h.property.1)
  rw [show s - (s + ℓ) = -ℓ by ring, show s + ℓ - (s + 2 * ℓ) = -ℓ by ring,
    show s - (s + 2 * ℓ) = -(2 * ℓ) by ring, sub_self]
  simp only [abs_neg, abs_zero, Real.zero_rpow h0, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg ℓ)]
  ring

theorem g_two_zero (h ℓ : ℝ) (hh : h ≠ 0) :
    g 2 h 0 ℓ = (4 - (2 : ℝ) ^ (2 * h)) * |ℓ| ^ (2 * h) := by
  norm_num [g, Finset.sum_range_succ, Real.zero_rpow (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hh),
    abs_mul, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg ℓ)]
  ring

theorem secondDifferenceFeature_norm_sq_eq_g (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) :
    ‖secondDifferenceFeature h s ℓ‖ ^ 2 = g 2 h 0 ℓ := by
  rw [secondDifferenceFeature_norm_sq, g_two_zero h ℓ (ne_of_gt h.property.1)]

theorem g_one_two_pos (q : ℕ) (hq : q = 1 ∨ q = 2) (h ℓ : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hl : ℓ ≠ 0) : 0 < g q h 0 ℓ := by
  rcases hq with rfl | rfl
  · rw [g_one_zero h ℓ hh.ne']
    exact Real.rpow_pos_of_pos (abs_pos.mpr hl) _
  · rw [g_two_zero h ℓ hh.ne']
    have hc := g_two_pos h hh hh1
    rw [g_two_unit h hh.ne'] at hc
    exact mul_pos hc (Real.rpow_pos_of_pos (abs_pos.mpr hl) _)

theorem g_one_two_continuousOn (q : ℕ) (hq : q = 1 ∨ q = 2) (ℓ : ℝ) (hl : ℓ ≠ 0) :
    ContinuousOn (fun h => g q h 0 ℓ) (Ioo 0 1) := by
  rcases hq with rfl | rfl
  · apply ContinuousOn.congr (f := fun h : ℝ => |ℓ| ^ (2 * h))
    · exact (Real.continuous_const_rpow (abs_ne_zero.mpr hl)).comp (continuous_const.mul continuous_id) |>.continuousOn
    · intro h hh
      exact g_one_zero h ℓ (ne_of_gt hh.1)
  · apply ContinuousOn.congr (f := fun h : ℝ => (4 - (2 : ℝ) ^ (2 * h)) * |ℓ| ^ (2 * h))
    · apply Continuous.continuousOn
      exact (continuous_const.sub ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
        (continuous_const.mul continuous_id))).mul
        ((Real.continuous_const_rpow (abs_ne_zero.mpr hl)).comp (continuous_const.mul continuous_id))
    · intro h hh
      exact g_two_zero h ℓ (ne_of_gt hh.1)

/-- Uniform nondegeneracy for both main-line orders and every fixed nonzero step. -/
theorem g_one_two_uniform_pos (q : ℕ) (hq : q = 1 ∨ q = 2) (a b ℓ : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hl : ℓ ≠ 0) :
    ∃ c > 0, ∀ h ∈ Icc a b, c ≤ g q h 0 ℓ := by
  have hc := (g_one_two_continuousOn q hq ℓ hl).mono
    (show Icc a b ⊆ Ioo (0 : ℝ) 1 from fun h hh => ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩)
  obtain ⟨h, hh, hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  exact ⟨g q h 0 ℓ, g_one_two_pos q hq h ℓ (ha.trans_le hh.1) (hh.2.trans_lt hb) hl, hm⟩

def secondDifferenceWeights : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1, -2, 1]

def stationaryTriple (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Measure (EuclideanSpace ℝ (Fin 3)) :=
  harmonizableGaussian (fun _ => h) (fun i => s + (i : ℝ) * ℓ)

theorem secondDifferenceWeights_inner (x : EuclideanSpace ℝ (Fin 3)) :
    ⟪secondDifferenceWeights, x⟫ = x 0 - 2 * x 1 + x 2 := by
  simp [secondDifferenceWeights, PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem secondDifferenceWeights_feature (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) :
    (∑ i : Fin 3, secondDifferenceWeights i • harmonizableFeature h (s + (i : ℝ) * ℓ)) =
      secondDifferenceFeature h s ℓ := by
  simp [secondDifferenceWeights, Fin.sum_univ_three, secondDifferenceFeature]
  module

theorem stationaryTriple_secondDifference_variance (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) :
    Var[fun x => x 0 - 2 * x 1 + x 2; stationaryTriple h s ℓ] = g 2 h 0 ℓ := by
  simp_rw [← secondDifferenceWeights_inner]
  rw [stationaryTriple, harmonizableGaussian, featureGaussian_linear_variance,
    secondDifferenceWeights_feature, secondDifferenceFeature_norm_sq_eq_g]

theorem secondDifferenceFeature_ne_zero (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) (hl : ℓ ≠ 0) :
    secondDifferenceFeature h s ℓ ≠ 0 := by
  intro he
  have hp := g_one_two_pos 2 (Or.inr rfl) h ℓ h.property.1 h.property.2 hl
  rw [← secondDifferenceFeature_norm_sq_eq_g h s ℓ, he, norm_zero, zero_pow (by norm_num)] at hp
  exact (lt_irrefl 0) hp

/-- Exact corrected log mean for an actual three-point Gaussian observation. -/
theorem stationaryTriple_secondDifference_log_mean (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) (hl : ℓ ≠ 0) :
    (∫ x, Real.log ((x 0 - 2 * x 1 + x 2) ^ 2) ∂stationaryTriple h s ℓ) =
      Real.log (g 2 h 0 ℓ) + gaussianLogSquareMean := by
  simp_rw [← secondDifferenceWeights_inner]
  rw [stationaryTriple, harmonizableGaussian, featureGaussian_expected_log_square]
  · rw [secondDifferenceWeights_feature, secondDifferenceFeature_norm_sq_eq_g]
  · rw [secondDifferenceWeights_feature]
    exact secondDifferenceFeature_ne_zero h s ℓ hl

theorem stationaryTriple_secondDifference_log_moments (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ)
    (hl : ℓ ≠ 0) (k : ℕ) :
    Integrable (fun x => |Real.log ((x 0 - 2 * x 1 + x 2) ^ 2)| ^ k) (stationaryTriple h s ℓ) := by
  simp_rw [← secondDifferenceWeights_inner]
  unfold stationaryTriple harmonizableGaussian
  have hi := featureGaussian_integrable_log_square_pow
    (fun i : Fin 3 => harmonizableFeature h (s + (i : ℝ) * ℓ)) secondDifferenceWeights
    (by rw [secondDifferenceWeights_feature]; exact secondDifferenceFeature_ne_zero h s ℓ hl) k
  simpa only [abs_pow] using hi.abs

end Hurst
