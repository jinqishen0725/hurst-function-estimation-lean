import Hurst.SecondFrozen
import Hurst.SecondCorrelationSums
import Hurst.GridLogMean

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem grid_second_separated_gap (n i j : ℕ) (hn : 0 < n) (hij : i + 2 < j) :
    grid n j - (grid n i + 2 * (1 / n)) = ((j - i - 2 : ℕ) : ℝ) * (1 / n) := by
  have hji : i ≤ j := by omega
  have hji1 : 2 ≤ j - i := by omega
  rw [Nat.cast_sub hji1, Nat.cast_sub hji]
  unfold grid
  push_cast
  ring

theorem frozen_second_grid_correlation_decay (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 1, ∀ n m : ℕ, 0 < n → ∀ H : Fin m → Ioo (0 : ℝ) 1,
      (∀ i, (H i : ℝ) ∈ Icc a b) → ∀ i j : Fin m,
      |⟪normalizedFrozenSecondIncrement (H i) (grid n i.val) (1 / n),
        normalizedFrozenSecondIncrement (H j) (grid n j.val) (1 / n)⟫| ≤ C * secondIncrementDecay b (Nat.dist j.val i.val) := by
  obtain ⟨C, hC, hdec⟩ := normalizedFrozenSecondIncrement_uniform_decay a b ha hb hab
  refine ⟨C + 4, by linarith, ?_⟩
  intro n m hn H hH
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hord : ∀ i j : Fin m, i.val ≤ j.val →
      |⟪normalizedFrozenSecondIncrement (H i) (grid n i.val) (1 / n),
        normalizedFrozenSecondIncrement (H j) (grid n j.val) (1 / n)⟫| ≤ (C + 4) * secondIncrementDecay b (Nat.dist j.val i.val) := by
    intro i j hij
    rw [Nat.dist_eq_sub_of_le_right hij]
    by_cases hnear : j.val - i.val ≤ 2
    · have hcs := abs_real_inner_le_norm (normalizedFrozenSecondIncrement (H i) (grid n i.val) (1 / n))
        (normalizedFrozenSecondIncrement (H j) (grid n j.val) (1 / n))
      have h1 := normalizedFrozenSecondIncrement_norm_le (H i) (grid n i.val) (1 / n) (by positivity)
      have h2 := normalizedFrozenSecondIncrement_norm_le (H j) (grid n j.val) (1 / n) (by positivity)
      have hh := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      simp only [secondIncrementDecay, hnear, if_true, mul_one]
      linarith
    · have hgap : i.val + 2 < j.val := by omega
      have hd : (1 : ℝ) ≤ ((j.val - i.val - 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j.val - i.val - 2 by omega)
      have h := hdec (H i) (H j) (hH i) (hH j) (grid n i.val) (grid n j.val) (1 / n)
        ((j.val - i.val - 2 : ℕ) : ℝ) (by positivity) hd (grid_second_separated_gap n i.val j.val hn hgap)
      simp only [secondIncrementDecay, hnear, if_false]
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))
  intro i j
  rcases le_total i.val j.val with hij | hji
  · exact hord i j hij
  · rw [real_inner_comm, Nat.dist_comm]
    exact hord j i hji


end Hurst
