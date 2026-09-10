import Hurst.HilbertPerturbation
import Hurst.GridLogMeanSharp

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem log_norm_square_perturbation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (c e : ℝ) (hc : 0 < c) (he : 0 ≤ e) (he1 : e ≤ 1) (hec : e ≤ c / 2)
    (hv : c ≤ ‖v‖) (hv2 : ‖v‖ ≤ 2) (huv : ‖u - v‖ ≤ e) :
    u ≠ 0 ∧ |Real.log (‖u‖ ^ 2) - Real.log (‖v‖ ^ 2)| ≤ (20 / c ^ 2) * e := by
  have hfloor := norm_floor_of_perturbation u v c e hv huv
  have hu : c / 2 ≤ ‖u‖ := by linarith
  have hn : u ≠ 0 := by intro hz; rw [hz, norm_zero] at hu; linarith
  refine ⟨hn, ?_⟩
  have hs := inner_perturbation_norm_bound u u v v 2 e (by norm_num) he hv2 hv2 huv huv
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hs
  have hesq : e ^ 2 ≤ e := by nlinarith
  have hdiff : |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 5 * e := by linarith
  have hu2 : (c / 2) ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (by positivity) hu 2
  have hv2' : (c / 2) ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith [pow_le_pow_left₀ hc.le hv 2]
  have hl := log_lipschitz_from_below (‖u‖ ^ 2) (‖v‖ ^ 2) ((c / 2) ^ 2) (by positivity) hu2 hv2'
  have hm := div_le_div_of_nonneg_right hdiff (sq_nonneg (c / 2))
  apply (hl.trans hm).trans_eq
  field_simp
  ring

end Hurst
