import Hurst.FeatureSecondOrder

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

/-- Cancellation of the first parameter variation in a second time difference. -/
theorem second_difference_parameter_cancellation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u1 u2 v1 v2 s1 s2 : E) (d1 d2 R S T : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hr1 : ‖u1 - v1 - d1 • s1‖ ≤ R * |d1| ^ 2)
    (hr2 : ‖u2 - v2 - d2 • s2‖ ≤ R * |d2| ^ 2)
    (hs : ‖s2‖ ≤ S) (ht : ‖s2 - s1‖ ≤ T) :
    ‖(u2 - v2) - (2 : ℝ) • (u1 - v1)‖ ≤
      |d2 - 2 * d1| * S + 2 * |d1| * T + R * (|d2| ^ 2 + 2 * |d1| ^ 2) := by
  have he : (u2 - v2) - (2 : ℝ) • (u1 - v1) =
      (d2 - 2 * d1) • s2 + (2 * d1) • (s2 - s1) +
      ((u2 - v2 - d2 • s2) - (2 : ℝ) • (u1 - v1 - d1 • s1)) := by module
  rw [he]
  have h1 := mul_le_mul_of_nonneg_left hs (abs_nonneg (d2 - 2 * d1))
  have h2 := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * |d1| by positivity)
  have h3 := add_le_add hr2 (mul_le_mul_of_nonneg_left hr1 (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ (‖(d2 - 2 * d1) • s2‖ + ‖(2 * d1) • (s2 - s1)‖) +
        (‖u2 - v2 - d2 • s2‖ + ‖(2 : ℝ) • (u1 - v1 - d1 • s1)‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_sub_le _ _))
    _ = (|d2 - 2 * d1| * ‖s2‖ + 2 * |d1| * ‖s2 - s1‖) +
        (‖u2 - v2 - d2 • s2‖ + 2 * ‖u1 - v1 - d1 • s1‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)

/-- Explicit rate after the second parameter difference and first steps are bounded. -/
theorem second_difference_parameter_rate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u1 u2 v1 v2 s1 s2 : E) (d1 d2 R S T B D l z : ℝ)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hT : 0 ≤ T) (hB : 0 ≤ B) (hD : 0 ≤ D) (hl : 0 ≤ l) (hz : 0 ≤ z)
    (hr1 : ‖u1 - v1 - d1 • s1‖ ≤ R * |d1| ^ 2)
    (hr2 : ‖u2 - v2 - d2 • s2‖ ≤ R * |d2| ^ 2)
    (hs : ‖s2‖ ≤ S) (ht : ‖s2 - s1‖ ≤ T * z)
    (hd1 : |d1| ≤ B * l) (hd2 : |d2| ≤ 2 * B * l) (hdd : |d2 - 2 * d1| ≤ D * l ^ 2) :
    ‖(u2 - v2) - (2 : ℝ) • (u1 - v1)‖ ≤
      (D * S + 6 * R * B ^ 2) * l ^ 2 + 2 * B * T * l * z := by
  have hc := second_difference_parameter_cancellation u1 u2 v1 v2 s1 s2 d1 d2 R S (T * z) hR hS hr1 hr2 hs ht
  have h1 := mul_le_mul_of_nonneg_right hdd hS
  have h2 := mul_le_mul_of_nonneg_right hd1 (show 0 ≤ 2 * T * z by positivity)
  have hd1sq := pow_le_pow_left₀ (abs_nonneg d1) hd1 2
  have hd2sq := pow_le_pow_left₀ (abs_nonneg d2) hd2 2
  have h3 := mul_le_mul_of_nonneg_left (add_le_add hd2sq (mul_le_mul_of_nonneg_left hd1sq (by norm_num : (0 : ℝ) ≤ 2))) hR
  nlinarith

end Hurst
