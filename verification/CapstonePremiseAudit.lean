import Hurst.ActualSecondChaosComplete

/-!
Independent nonvacuity audit of the claimed q1 long-memory capstone.
This file does not alter the original theorem. Both contradictions are checked
by Lean with the same definitions and inequalities as the capstone.
-/

namespace Hurst

/-- The capstone's all-row cardinality premise is false already at `n = 0`. -/
theorem capstone_all_rows_cardinality_impossible (t γ : ℝ) :
    ¬ (∀ n : ℕ,
      0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card) := by
  intro hcard
  have hzero := hcard 0
  simp [localWeightActiveSet] at hzero

/-- The capstone's cutoff and decay bandwidth inequalities cannot coexist
with the ordinary parameter bound `f(t) ≤ b < 1`. -/
theorem capstone_bandwidth_window_impossible (ft b γ : ℝ)
    (hftb : ft ≤ b) (hb : b < 1)
    (hγcut : γ < 4 * ft - 3)
    (hγdec : 4 * b + 1 - 4 * ft <
      γ * (2 * (2 - 2 * ft) + 1)) : False := by
  have hden : 0 < 2 * (2 - 2 * ft) + 1 := by linarith
  have hupper := mul_lt_mul_of_pos_right hγcut hden
  nlinarith [sq_nonneg (4 * ft - 4)]

/-- The model assumptions of `actualQ1LongStatistic_tendsto_secondChaos_complete`
contain the contradictory bandwidth subfamily above. -/
theorem capstone_model_bandwidth_impossible
    (a b : ℝ) (f : ℝ → ℝ)
    (hF : Set.MapsTo f (Set.Ioo (0 : ℝ) 1) (Set.Icc a b))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hb : b < 1) (γ : ℝ)
    (hγcut : γ < 4 * f t - 3)
    (hγdec : 4 * b + 1 - 4 * f t <
      γ * (2 * (2 - 2 * f t) + 1)) : False := by
  exact capstone_bandwidth_window_impossible (f t) b γ
    (hF ht).2 hb hγcut hγdec

end Hurst
