import Hurst.FixedRangeUpper
import Hurst.MinimaxSquaredLower

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Hurst

/-- Matching squared-Ls minimax bounds on one fixed original parameter class, including p=1. -/
theorem fixedRange_q1_minimax_matched (s : {s : ℝ // 1 ≤ s}) (hs : s.val ≤ 2)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha0 : 0 < a) (ha : a < 1/2)
    (hb0 : 1/2 < b) (hb : b < 3/4) (hM : 0 < M) :
    ∃ c > 0, ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ σ : ℝ, σ ≠ 0 →
      ENNReal.ofReal (c * (lowerBoundRate p n)^2) ≤
        minimaxRiskDist (fun d => d^2) (subclassHurstTarget s hp (fixedRangeHurstClass p M a b))
          (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ∧
      minimaxRiskDist (fun d => d^2) (subclassHurstTarget s hp (fixedRangeHurstClass p M a b))
          (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ≤
        ENNReal.ofReal (C * (lowerBoundRate p n)^2) := by
  obtain ⟨c, hc, hl⟩ := fixedRange_minimax_squared_lower s p M a b hp hM ha hb0
  obtain ⟨K, hK⟩ := eventually_atTop.mp hl
  obtain ⟨C, hC, N, hN, hu⟩ := fixedRange_q1_minimax_upper p a b M hp ha0 hb (by linarith) hM.le
  refine ⟨c, hc, C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro n hn σ hσ
  exact ⟨hK n ((le_max_right N K).trans hn) σ hσ, hu σ hσ s hs n ((le_max_left N K).trans hn)⟩

/-- Matching squared-Ls minimax bounds for q=2 and all p>=2 on a fixed range spanning one half. -/
theorem fixedRange_q2_minimax_matched (s : {s : ℝ // 1 ≤ s}) (hs : s.val ≤ 2)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha0 : 0 < a) (ha : a < 1/2)
    (hb0 : 1/2 < b) (hb : b < 1) (hM : 0 < M) :
    ∃ c > 0, ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ σ : ℝ, σ ≠ 0 →
      ENNReal.ofReal (c * (lowerBoundRate p n)^2) ≤
        minimaxRiskDist (fun d => d^2) (subclassHurstTarget s (by linarith : 1 ≤ p) (fixedRangeHurstClass p M a b))
          (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ∧
      minimaxRiskDist (fun d => d^2) (subclassHurstTarget s (by linarith : 1 ≤ p) (fixedRangeHurstClass p M a b))
          (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ≤
        ENNReal.ofReal (C * (lowerBoundRate p n)^2) := by
  obtain ⟨c, hc, hl⟩ := fixedRange_minimax_squared_lower s p M a b (by linarith) hM ha hb0
  obtain ⟨K, hK⟩ := eventually_atTop.mp hl
  obtain ⟨C, hC, N, hN, hu⟩ := fixedRange_q2_minimax_upper p a b M hp ha0 hb (by linarith) hM.le
  refine ⟨c, hc, C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro n hn σ hσ
  exact ⟨hK n ((le_max_right N K).trans hn) σ hσ, hu σ hσ s hs n ((le_max_left N K).trans hn)⟩

end Hurst
