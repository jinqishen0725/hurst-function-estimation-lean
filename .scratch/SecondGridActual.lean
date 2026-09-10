import Hurst.HolderSecondIncrement
import Hurst.SecondFrozen
import Hurst.GridCorrelationRows

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def secondDiffLeft (n : ℕ) (i : Fin (n - 2)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def secondDiffMiddle (n : ℕ) (i : Fin (n - 2)) : Fin n := ⟨i.val + 1, by have := i.isLt; omega⟩
def secondDiffRight (n : ℕ) (i : Fin (n - 2)) : Fin n := ⟨i.val + 2, by have := i.isLt; omega⟩

theorem grid_second_middle_step (n : ℕ) (i : Fin (n - 2)) :
    grid n (secondDiffMiddle n i).val = grid n i.val + 1 / (n : ℝ) := by
  simp only [grid, secondDiffMiddle, Nat.cast_add, Nat.cast_one]
  ring

theorem grid_second_right_step (n : ℕ) (i : Fin (n - 2)) :
    grid n (secondDiffRight n i).val = grid n i.val + 2 * (1 / (n : ℝ)) := by
  simp only [grid, secondDiffRight, Nat.cast_add, Nat.cast_ofNat]
  ring

def gridSecondActual (n : ℕ) (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin (n - 2)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (1 / (n : ℝ)) ^ (-(H (secondDiffLeft n i) : ℝ)) •
    varyingSecondIncrement (H (secondDiffLeft n i)) (H (secondDiffMiddle n i)) (H (secondDiffRight n i))
      (grid n i.val) (1 / n)

theorem reciprocal_log_error_le_grid_error (C : ℝ) (hC : 0 ≤ C) (n : ℕ) (hn : 0 < n) :
    C * (1 / (n : ℝ)) * (1 + |Real.log (1 / (n : ℝ))|) ≤ gridCovarianceError (1 / 2) C n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [one_div, Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg hn1)]
  have hlog := Real.log_le_log hn0 (show (n : ℝ) ≤ 2 * n by linarith)
  have he := mul_le_mul_of_nonneg_left (add_le_add_left hlog 1) (show 0 ≤ C * (n : ℝ)⁻¹ by positivity)
  have hpos : 0 ≤ C * (n : ℝ)⁻¹ * (1 + Real.log (2 * n)) := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  unfold gridCovarianceError
  norm_num only [show (2 : ℝ) * (1 / 2) - 2 = -1 by norm_num, Real.rpow_neg_one]
  nlinarith

/-- Every actual q=2 grid feature is uniformly close to its frozen feature over the original class. -/
theorem hurstHolder_grid_second_remainder (p a b M : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ n : ℕ, 0 < n → ∀ i : Fin (n - 2),
      ‖gridSecondActual n (midpointSampleHurst f hf.1 n) i -
        normalizedFrozenSecondIncrement (midpointSampleHurst f hf.1 n (secondDiffLeft n i)) (grid n i.val) (1 / n)‖ ≤
          gridCovarianceError (1 / 2) C n := by
  obtain ⟨C, hC, hc⟩ := hurstHolder_second_increment_remainder p a b M hp ha hb hab hM
  refine ⟨C, hC, ?_⟩
  intro f hf hF n hn i
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := grid_mem n i.val hn (secondDiffLeft n i).isLt
  have ht2 : grid n i.val + 2 * (1 / (n : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
    rw [← grid_second_right_step]
    exact grid_mem n _ hn (secondDiffRight n i).isLt
  let H := midpointSampleHurst f hf.1 n
  have he := hc f hf hF (grid n i.val) (1 / n) (by positivity) ht ht2
    (H (secondDiffLeft n i)) (H (secondDiffMiddle n i)) (H (secondDiffRight n i))
    rfl (by dsimp [H, midpointSampleHurst]; rw [grid_second_middle_step])
    (by dsimp [H, midpointSampleHurst]; rw [grid_second_right_step])
  have hid : gridSecondActual n H i - normalizedFrozenSecondIncrement (H (secondDiffLeft n i)) (grid n i.val) (1 / n) =
      (1 / (n : ℝ)) ^ (-(H (secondDiffLeft n i) : ℝ)) •
        (varyingSecondIncrement (H (secondDiffLeft n i)) (H (secondDiffMiddle n i)) (H (secondDiffRight n i))
          (grid n i.val) (1 / n) - frozenSecondIncrement (H (secondDiffLeft n i)) (grid n i.val) (1 / n)) := by
    unfold gridSecondActual normalizedFrozenSecondIncrement
    rw [smul_sub]
  rw [hid]
  exact he.trans (reciprocal_log_error_le_grid_error C hC n hn)

end Hurst
