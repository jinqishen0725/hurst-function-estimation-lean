import Hurst.FirstUnknownMinimax

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Hurst

/-- Matching minimax bounds with a single decision kernel for every unknown common scale. -/
theorem unknownScale_q1_minimax_matched (s : {s : ℝ // 1 ≤ s}) (hs : s.val ≤ 2)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha0 : 0 < a) (ha : a < 1/2)
    (hb0 : 1/2 < b) (hb : b < 3/4) (hM : 0 < M) :
    ∃ c > 0, ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal (c * (lowerBoundRate p n)^2) ≤
        minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a := a) (b := b) s (by linarith : 1 ≤ p))
          (unknownHurstExperiment p M a b n) ∧
      minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a := a) (b := b) s (by linarith : 1 ≤ p))
          (unknownHurstExperiment p M a b n) ≤
        ENNReal.ofReal (C * (lowerBoundRate p n)^2) := by
  obtain ⟨c, hc, hl⟩ := unknownScale_minimax_squared_lower s p M a b (by linarith) hM ha hb0
  obtain ⟨K, hK⟩ := eventually_atTop.mp hl
  obtain ⟨C, hC, N, hN, hu⟩ := unknownScale_q1_minimax_upper p a b M hp ha0 hb (by linarith) hM.le
  refine ⟨c, hc, C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro n hn
  exact ⟨hK n ((le_max_right N K).trans hn), hu s hs n ((le_max_left N K).trans hn)⟩

end Hurst
