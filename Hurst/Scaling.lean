import Hurst.Analytic

noncomputable section
open scoped BigOperators
namespace Hurst

/-- Homogeneity of the original double sum, for every differencing order q. -/
theorem g_scale (q : ℕ) (H u h a : ℝ) :
    g q H (u*a) (h*a) = |a|^(2*H)*g q H u h := by
  have term : ∀ i j : ℕ,
      (-1:ℝ)^(i+j)*(q.choose i:ℝ)*(q.choose j:ℝ)*
          |u*a+((i:ℝ)-(j:ℝ))*(h*a)|^(2*H) =
      |a|^(2*H) * ((-1:ℝ)^(i+j)*(q.choose i:ℝ)*(q.choose j:ℝ)*
          |u+((i:ℝ)-(j:ℝ))*h|^(2*H)) := by
    intro i j
    rw [show u*a+((i:ℝ)-(j:ℝ))*(h*a) = (u+((i:ℝ)-(j:ℝ))*h)*a by ring,
      abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    ring
  unfold g
  simp_rw [term, ← Finset.mul_sum]
  ring

theorem g_scale_two (q : ℕ) (H h : ℝ) :
    g q H 0 (2*h) = (2:ℝ)^(2*H)*g q H 0 h := by
  simpa [mul_comm] using g_scale q H 0 h 2

/-- Exact identity underlying the unknown-variance pilot (4.1), all q. -/
theorem log_g_scale_two (q : ℕ) (H h : ℝ) (hg : g q H 0 h ≠ 0) :
    Real.log (g q H 0 (2*h))-Real.log (g q H 0 h) = 2*H*Real.log 2 := by
  rw [g_scale_two, Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _)) hg,
    Real.log_rpow (by norm_num : (0:ℝ)<2)]
  ring

/-- Corrected S.2.1 in the practical q=2, unit-direction case, with an
explicit compactness margin γ that the printed assumptions omit. -/
theorem g_two_uniform_lower (γ H : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hH : 0 < H) (hHγ : H ≤ 1-γ) :
    0 < 4-(2:ℝ)^(2*(1-γ)) ∧ 4-(2:ℝ)^(2*(1-γ)) ≤ g 2 H 0 1 := by
  constructor
  · have hg := g_two_pos (1-γ) (by linarith) (by linarith)
    rwa [g_two_unit (1-γ) (by linarith)] at hg
  · rw [g_two_unit H (ne_of_gt hH)]
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 2*H ≤ 2*(1-γ) by linarith)
    linarith

/-- Squaring the sign-reversed fluctuation preserves second moments, explaining
why the sign repair in 3.4 affects the long-memory law but not its MSE order. -/
theorem reflected_square (x : ℝ) : (-x)^2 = x^2 := by ring

end Hurst
