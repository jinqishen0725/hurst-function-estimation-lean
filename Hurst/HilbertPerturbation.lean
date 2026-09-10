import Hurst.GridCorrelationRows

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem inner_perturbation_norm_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v a b : E) (K e : ℝ) (hK : 0 ≤ K) (he : 0 ≤ e)
    (ha : ‖a‖ ≤ K) (hb : ‖b‖ ≤ K) (hu : ‖u - a‖ ≤ e) (hv : ‖v - b‖ ≤ e) :
    |⟪u, v⟫ - ⟪a, b⟫| ≤ 2 * K * e + e ^ 2 := by
  have hex : ⟪u, v⟫ - ⟪a, b⟫ = ⟪u - a, b⟫ + ⟪a, v - b⟫ + ⟪u - a, v - b⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [hex]
  have h1 := (abs_real_inner_le_norm (u - a) b).trans (mul_le_mul hu hb (norm_nonneg _) he)
  have h2 := (abs_real_inner_le_norm a (v - b)).trans (mul_le_mul ha hv (norm_nonneg _) hK)
  have h3 := (abs_real_inner_le_norm (u - a) (v - b)).trans (mul_le_mul hu hv (norm_nonneg _) he)
  apply ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
  exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)

theorem norm_floor_of_perturbation {E : Type*} [NormedAddCommGroup E]
    (u a : E) (c e : ℝ) (ha : c ≤ ‖a‖) (he : ‖u - a‖ ≤ e) : c - e ≤ ‖u‖ := by
  have hi := norm_sub_le u (u - a)
  rw [sub_sub_cancel] at hi
  linarith

theorem vectorCorrelation_bound_of_positive_floor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (c : ℝ) (hc : 0 < c) (hu : c ≤ ‖u‖) (hv : c ≤ ‖v‖) :
    |vectorCorrelation u v| ≤ (c ^ 2)⁻¹ * |⟪u, v⟫| := by
  have hd : c ^ 2 ≤ ‖u‖ * ‖v‖ := by simpa only [pow_two] using mul_le_mul hu hv hc.le (norm_nonneg u)
  unfold vectorCorrelation
  rw [abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hc) hd).trans_eq (by ring)

end Hurst
