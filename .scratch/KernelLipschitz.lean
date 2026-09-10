import Hurst.ShiftedWeightEnergy

noncomputable section
open Set
namespace Hurst

theorem kernelMomentFunction_lipschitz (k : ℕ) :
    ∃ L : NNReal, LipschitzWith L (kernelMomentFunction k) := by
  obtain ⟨C, hC⟩ := (kernelMomentFunction_compactSupport k).deriv.exists_bound_of_continuousOn
    ((kernelMomentFunction_smooth k).continuous_deriv (by simp)).continuousOn
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨⟨B, hB⟩, ?_⟩
  rw [← lipschitzOnWith_univ]
  apply convex_univ.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact (kernelMomentFunction_smooth k).differentiable (by simp) x
  · intro x hx
    rw [← NNReal.coe_le_coe]
    change ‖deriv (kernelMomentFunction k) x‖ ≤ B
    by_cases hz : deriv (kernelMomentFunction k) x = 0
    · simp only [hz, norm_zero]
      exact hB
    · exact (hC x (subset_closure hz)).trans (le_max_left _ _)

end Hurst
