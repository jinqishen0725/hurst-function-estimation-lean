import Hurst.StationaryDifferences
import Hurst.VaryingIncrement

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

def firstIncrementLagCorrelation (h x : ℝ) : ℝ :=
  (|x + 1| ^ (2 * h) + |x - 1| ^ (2 * h) - 2 * |x| ^ (2 * h)) / 2

theorem firstIncrementLagCorrelation_continuousOn (x : ℝ) :
    ContinuousOn (fun h => firstIncrementLagCorrelation h x) (Ioi 0) := by
  have hc : ∀ y : ℝ, ContinuousOn (fun h : ℝ => |y| ^ (2 * h)) (Ioi 0) := by
    intro y
    apply continuousOn_const.rpow (continuousOn_const.mul continuousOn_id)
    intro h hh
    exact Or.inr (mul_pos (by norm_num) hh)
  unfold firstIncrementLagCorrelation
  fun_prop

theorem firstIncrementLagCorrelation_tendsto
    (x h : ℝ) (hh : 0 < h) (H : ℕ → ℝ)
    (hH : Tendsto H Filter.atTop (𝓝 h)) :
    Tendsto (fun n => firstIncrementLagCorrelation (H n) x)
      Filter.atTop (𝓝 (firstIncrementLagCorrelation h x)) :=
  ((firstIncrementLagCorrelation_continuousOn x).continuousAt
    (Ioi_mem_nhds hh)).tendsto.comp hH

theorem normalizedFrozenIncrement_same_parameter_lag
    (h : Ioo (0 : ℝ) 1) (s ℓ x : ℝ) (hℓ : 0 < ℓ) :
    ⟪normalizedFrozenIncrement h s ℓ,
      normalizedFrozenIncrement h (s + x * ℓ) ℓ⟫ =
      firstIncrementLagCorrelation h x := by
  unfold normalizedFrozenIncrement
  rw [real_inner_smul_left, real_inner_smul_right,
    harmonizableFeature_increment_inner]
  have habs1 : |s + ℓ - (s + x * ℓ)| = ℓ * |x - 1| := by
    rw [show s + ℓ - (s + x * ℓ) = -(x - 1) * ℓ by ring,
      abs_mul, abs_neg, abs_of_pos hℓ]
    ring
  have habs2 : |s - (s + x * ℓ + ℓ)| = ℓ * |x + 1| := by
    rw [show s - (s + x * ℓ + ℓ) = -(x + 1) * ℓ by ring,
      abs_mul, abs_neg, abs_of_pos hℓ]
    ring
  have habs3 : |s + ℓ - (s + x * ℓ + ℓ)| = ℓ * |x| := by
    rw [show s + ℓ - (s + x * ℓ + ℓ) = -x * ℓ by ring,
      abs_mul, abs_neg, abs_of_pos hℓ]
    ring
  have habs4 : |s - (s + x * ℓ)| = ℓ * |x| := by
    rw [show s - (s + x * ℓ) = -x * ℓ by ring,
      abs_mul, abs_neg, abs_of_pos hℓ]
    ring
  rw [habs1, habs2, habs3, habs4]
  simp_rw [Real.mul_rpow hℓ.le (abs_nonneg _)]
  have hcancel : ℓ ^ (-(h : ℝ)) *
      (ℓ ^ (-(h : ℝ)) * ℓ ^ (2 * (h : ℝ))) = 1 := by
    rw [← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
    convert Real.rpow_zero ℓ using 1
    congr 1
    ring
  unfold firstIncrementLagCorrelation
  calc
    _ = (ℓ ^ (-(h : ℝ)) *
        (ℓ ^ (-(h : ℝ)) * ℓ ^ (2 * (h : ℝ)))) *
        (|x + 1| ^ (2 * (h : ℝ)) + |x - 1| ^ (2 * (h : ℝ)) -
          2 * |x| ^ (2 * (h : ℝ))) / 2 := by ring
    _ = _ := by rw [hcancel]; ring

theorem normalizedFrozenIncrement_same_parameter_nat_lag
    (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) (k : ℕ) (hℓ : 0 < ℓ) :
    ⟪normalizedFrozenIncrement h s ℓ,
      normalizedFrozenIncrement h (s + k * ℓ) ℓ⟫ =
      firstIncrementLagCorrelation h k :=
  normalizedFrozenIncrement_same_parameter_lag h s ℓ k hℓ

end Hurst
