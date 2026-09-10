import Hurst.GridErrorLimit

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

def vectorCorrelation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) : ℝ :=
  ⟪u, v⟫ / (‖u‖ * ‖v‖)

theorem vectorCorrelation_bound_of_norm_floor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : (1 / 2 : ℝ) ≤ ‖u‖) (hv : (1 / 2 : ℝ) ≤ ‖v‖) :
    |vectorCorrelation u v| ≤ 4 * |⟪u, v⟫| := by
  have hd : (1 / 4 : ℝ) ≤ ‖u‖ * ‖v‖ := by nlinarith [mul_le_mul hu hv (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg u)]
  unfold vectorCorrelation
  rw [abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have he := div_le_div_of_nonneg_left (abs_nonneg ⟪u, v⟫) (by norm_num : (0 : ℝ) < 1 / 4) hd
  exact he.trans_eq (by ring)

theorem actual_grid_correlation_rows_finite (a b B : ℝ)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ A ≥ 1, ∃ C ≥ 0, ∀ n : ℕ, 0 < n → gridCovarianceError b C n ≤ 1 / 2 →
      ∀ H : Fin n → Ioo (0 : ℝ) 1, (∀ i, (H i : ℝ) ∈ Icc a b) →
      (∀ i : Fin (n - 1), |(H (firstDiffRight n i) : ℝ) - H (firstDiffLeft n i)| ≤ B / n) →
      (∀ i, (1 / 2 : ℝ) ≤ ‖gridActualIncrement n H i‖) ∧
      ∀ i : Fin (n - 1), (∑ j, (vectorCorrelation (gridActualIncrement n H i) (gridActualIncrement n H j)) ^ 2) ≤
        64 * A ^ 2 * (∑' k, (firstIncrementDecay b k) ^ 2) + 32 * n * (gridCovarianceError b C n) ^ 2 := by
  obtain ⟨A, hA, hfrozen⟩ := frozen_grid_correlation_decay a b ha (by linarith) hab
  obtain ⟨C, hC, hpert⟩ := actual_grid_covariance_perturbation a b B ha (by linarith) hab hB
  refine ⟨A, hA, C, hC, ?_⟩
  intro n hn hsmall H hH hstep
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have herr : 0 ≤ gridCovarianceError b C n := by
    unfold gridCovarianceError
    have hL := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  have hfloor : ∀ i, (1 / 2 : ℝ) ≤ ‖gridActualIncrement n H i‖ := by
    intro i
    have he := hpert n hn H hH hstep i i
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, gridFrozenIncrement,
      normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at he
    have hlow := (abs_le.mp he).1
    nlinarith [norm_nonneg (gridActualIncrement n H i)]
  refine ⟨hfloor, ?_⟩
  intro i
  have hdec : ∀ i j : Fin (n - 1), |vectorCorrelation (gridActualIncrement n H i) (gridActualIncrement n H j)| ≤
      (4 * A) * firstIncrementDecay b (Nat.dist j.val i.val) + 4 * gridCovarianceError b C n := by
    intro i j
    have hf := hfrozen n (n - 1) hn (fun i => H (firstDiffLeft n i)) (fun i => hH _) i j
    have he := hpert n hn H hH hstep i j
    have htri := abs_add_le
      (⟪gridActualIncrement n H i, gridActualIncrement n H j⟫ - ⟪gridFrozenIncrement n H i, gridFrozenIncrement n H j⟫)
      ⟪gridFrozenIncrement n H i, gridFrozenIncrement n H j⟫
    rw [sub_add_cancel] at htri
    have hf' : |⟪gridFrozenIncrement n H i, gridFrozenIncrement n H j⟫| ≤ A * firstIncrementDecay b (Nat.dist j.val i.val) := hf
    have hc := vectorCorrelation_bound_of_norm_floor (gridActualIncrement n H i) (gridActualIncrement n H j) (hfloor i) (hfloor j)
    linarith
  have hs := correlation_square_row_bound b (4 * A) (4 * gridCovarianceError b C n) hb (by linarith) (by positivity)
    (n - 1) (fun i j => vectorCorrelation (gridActualIncrement n H i) (gridActualIncrement n H j)) hdec i
  have hnle : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hm := mul_le_mul_of_nonneg_right hnle (sq_nonneg (gridCovarianceError b C n))
  nlinarith

/-- The actual full-grid correlation row bound has one constant for the whole fixed Lipschitz class. -/
theorem actual_grid_correlation_rows_eventually (a b B : ℝ)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ H : Fin n → Ioo (0 : ℝ) 1,
      (∀ i, (H i : ℝ) ∈ Icc a b) →
      (∀ i : Fin (n - 1), |(H (firstDiffRight n i) : ℝ) - H (firstDiffLeft n i)| ≤ B / n) →
      (∀ i, gridActualIncrement n H i ≠ 0) ∧
      ∀ i : Fin (n - 1), (∑ j, (vectorCorrelation (gridActualIncrement n H i) (gridActualIncrement n H j)) ^ 2) ≤ R := by
  obtain ⟨A, hA, C, hC, hc⟩ := actual_grid_correlation_rows_finite a b B ha hb hab hB
  let S := ∑' k, (firstIncrementDecay b k) ^ 2
  refine ⟨64 * A ^ 2 * S + 32, by dsimp [S]; positivity, ?_⟩
  have he := (gridCovarianceError_tendsto b C (by linarith)).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have he2 := (gridCovarianceError_square_row_tendsto b C hb).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1, he, he2] with n hn hsmall hsquare
  intro H hH hstep
  obtain ⟨hfloor, hrows⟩ := hc n (by omega) hsmall.le H hH hstep
  refine ⟨?_, ?_⟩
  · intro i hzero
    have := hfloor i
    rw [hzero, norm_zero] at this
    norm_num at this
  · intro i
    have := hrows i
    dsimp only [S]
    linarith

end Hurst
