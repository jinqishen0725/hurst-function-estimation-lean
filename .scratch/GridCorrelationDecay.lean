import Hurst.FrozenCorrelation
import Hurst.CorrelationSums
import Hurst.GridCovariancePerturb
import Hurst.GridLogMean

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem grid_separated_gap (n i j : ℕ) (hn : 0 < n) (hij : i + 1 < j) :
    grid n j - (grid n i + 1 / n) = ((j - i - 1 : ℕ) : ℝ) * (1 / n) := by
  have hji : i ≤ j := by omega
  have hji1 : 1 ≤ j - i := by omega
  rw [Nat.cast_sub hji1, Nat.cast_sub hji]
  unfold grid
  push_cast
  ring

theorem frozen_grid_correlation_decay (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 1, ∀ n m : ℕ, 0 < n → ∀ H : Fin m → Ioo (0 : ℝ) 1,
      (∀ i, (H i : ℝ) ∈ Icc a b) → ∀ i j : Fin m,
      |⟪normalizedFrozenIncrement (H i) (grid n i.val) (1 / n),
        normalizedFrozenIncrement (H j) (grid n j.val) (1 / n)⟫| ≤ C * firstIncrementDecay b (Nat.dist j.val i.val) := by
  obtain ⟨C, hC, hdec⟩ := normalizedFrozenIncrement_uniform_decay a b ha hb hab
  refine ⟨C + 1, by linarith, ?_⟩
  intro n m hn H hH
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hord : ∀ i j : Fin m, i.val ≤ j.val →
      |⟪normalizedFrozenIncrement (H i) (grid n i.val) (1 / n),
        normalizedFrozenIncrement (H j) (grid n j.val) (1 / n)⟫| ≤ (C + 1) * firstIncrementDecay b (Nat.dist j.val i.val) := by
    intro i j hij
    rw [Nat.dist_eq_sub_of_le_right hij]
    by_cases hnear : j.val - i.val ≤ 1
    · have hcs := abs_real_inner_le_norm (normalizedFrozenIncrement (H i) (grid n i.val) (1 / n))
        (normalizedFrozenIncrement (H j) (grid n j.val) (1 / n))
      rw [normalizedFrozenIncrement_norm _ _ _ (by positivity), normalizedFrozenIncrement_norm _ _ _ (by positivity)] at hcs
      simp only [firstIncrementDecay, hnear, if_true, mul_one]
      linarith
    · have hgap : i.val + 1 < j.val := by omega
      have hd : (1 : ℝ) ≤ ((j.val - i.val - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j.val - i.val - 1 by omega)
      have h := hdec (H i) (H j) (hH i) (hH j) (grid n i.val) (grid n j.val) (1 / n)
        ((j.val - i.val - 1 : ℕ) : ℝ) (by positivity) hd (grid_separated_gap n i.val j.val hn hgap)
      simp only [firstIncrementDecay, hnear, if_false]
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))
  intro i j
  rcases le_total i.val j.val with hij | hji
  · exact hord i j hij
  · rw [real_inner_comm, Nat.dist_comm]
    exact hord j i hji

def gridActualIncrement (n : ℕ) (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin (n - 1)) : Lp ℂ 2 (volume : Measure ℝ) :=
  normalizedVaryingIncrement (H (firstDiffLeft n i)) (H (firstDiffRight n i)) (grid n i.val) (1 / n)

def gridFrozenIncrement (n : ℕ) (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin (n - 1)) : Lp ℂ 2 (volume : Measure ℝ) :=
  normalizedFrozenIncrement (H (firstDiffLeft n i)) (grid n i.val) (1 / n)

def gridCovarianceError (b C : ℝ) (n : ℕ) : ℝ :=
  C * (1 + Real.log (2 * (n : ℝ))) * ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))

theorem actual_grid_covariance_perturbation (a b B : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → ∀ H : Fin n → Ioo (0 : ℝ) 1,
      (∀ i, (H i : ℝ) ∈ Icc a b) →
      (∀ i : Fin (n - 1), |(H (firstDiffRight n i) : ℝ) - H (firstDiffLeft n i)| ≤ B / n) →
      ∀ i j : Fin (n - 1),
      |⟪gridActualIncrement n H i, gridActualIncrement n H j⟫ -
        ⟪gridFrozenIncrement n H i, gridFrozenIncrement n H j⟫| ≤ gridCovarianceError b C n := by
  obtain ⟨C, hC, hc⟩ := grid_increment_covariance_perturbation a b B ha hb hab hB
  refine ⟨C, hC, ?_⟩
  intro n hn H hH hstep i j
  have hloc (i : Fin (n - 1)) : grid n i.val ∈ Icc (0 : ℝ) 1 ∧ grid n i.val + 1 / n ∈ Icc (0 : ℝ) 1 := by
    have hleft := grid_mem n (firstDiffLeft n i).val hn (firstDiffLeft n i).isLt
    have hright := grid_mem n (firstDiffRight n i).val hn (firstDiffRight n i).isLt
    have he := grid_firstDifference_step n i
    dsimp only [firstDiffLeft] at he
    refine ⟨⟨hleft.1.le, hleft.2.le⟩, ?_⟩
    rw [← he]
    exact ⟨hright.1.le, hright.2.le⟩
  have hmesh (i : Fin (n - 1)) : halfMeshPoint n (grid n i.val + 1 / n) := by
    have he := grid_firstDifference_step n i
    dsimp only [firstDiffLeft] at he
    rw [← he]
    exact halfMeshPoint_grid n _
  exact hc n hn (H (firstDiffLeft n i)) (H (firstDiffRight n i))
    (H (firstDiffLeft n j)) (H (firstDiffRight n j)) (hH _) (hH _) (hH _) (hH _)
    (grid n i.val) (grid n j.val) (hloc i).1 (hloc i).2 (hloc j).1 (hloc j).2
    (halfMeshPoint_grid n _) (hmesh i) (halfMeshPoint_grid n _) (hmesh j) (hstep i) (hstep j)

end Hurst
