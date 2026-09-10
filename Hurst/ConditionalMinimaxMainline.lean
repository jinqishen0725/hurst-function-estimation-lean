import Hurst.ConditionalMomentMinimax
import Hurst.FirstUnknownMatched
import Hurst.UnknownMatchedMinimax

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Hurst

theorem q1_conditional_allfinite_minimax_mainline (s : {s : ℝ // 1≤s})
    (p a b M : ℝ) (hp : 1≤p) (ha0 : 0<a) (ha : a<1/2)
    (hb0 : 1/2<b) (hb : b<3/4) (hM : 0<M)
    (hraw : 2≤s.val → Q1RawMomentBound p a b M s.val) :
    ∃ c>0,∃ C>0,∃ N : ℕ,2≤N ∧ ∀ n : ℕ,N≤n → ∀ σ : ℝ,σ≠0 →
      ENNReal.ofReal (c*(lowerBoundRate p n)^2)≤
        minimaxRiskDist (fun d => d^2) (subclassHurstTarget s (by linarith : 1≤p) (fixedRangeHurstClass p M a b))
          (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ∧
      minimaxRiskDist (fun d => d^2) (subclassHurstTarget s (by linarith : 1≤p) (fixedRangeHurstClass p M a b))
          (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b))≤
        minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a:=a) (b:=b) s (by linarith : 1≤p))
          (unknownHurstExperiment p M a b n) ∧
      minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a:=a) (b:=b) s (by linarith : 1≤p))
          (unknownHurstExperiment p M a b n)≤ENNReal.ofReal (C*(lowerBoundRate p n)^2) := by
  have hp1 : 1≤p := by linarith
  have hab : a≤b := by linarith
  have hu : ∃ C>0,∃ N : ℕ,2≤N ∧ ∀ n : ℕ,N≤n →
      minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a:=a) (b:=b) s hp1)
        (unknownHurstExperiment p M a b n)≤ENNReal.ofReal (C*(lowerBoundRate p n)^2) := by
    by_cases hs : s.val≤2
    · obtain ⟨C,hC,N,hN,hbound⟩ := unknownScale_q1_minimax_upper p a b M hp ha0 hb hab hM.le
      exact ⟨C,hC,N,by omega,fun n hn => hbound s hs n hn⟩
    · have hs' : 2≤s.val := le_of_lt (lt_of_not_ge hs)
      obtain ⟨C,hC,N,hN,hbound⟩ := unknownScale_q1_minimax_upper_of_raw_moments p a b M hp ha0 hb hab hM.le s hs' (hraw hs')
      exact ⟨C,hC,N,by omega,hbound⟩
  obtain ⟨C,hC,N,hN,hupper⟩ := hu
  obtain ⟨c,hc,hlower⟩ := fixedRange_minimax_squared_lower s p M a b hp1 hM ha hb0
  obtain ⟨K,hK⟩ := eventually_atTop.mp hlower
  refine ⟨c,hc,C,hC,max N K,hN.trans (le_max_left _ _),?_⟩
  intro n hn σ hσ
  exact ⟨hK n ((le_max_right _ _).trans hn) σ hσ,
    knownScale_minimax_le_unknown s p M a b σ hp1 hσ n _,hupper n ((le_max_left _ _).trans hn)⟩

theorem q2_conditional_allfinite_minimax_mainline (s : {s : ℝ // 1≤s})
    (p a b M : ℝ) (hp : 2≤p) (ha0 : 0<a) (ha : a<1/2)
    (hb0 : 1/2<b) (hb : b<1) (hM : 0<M)
    (hraw : 2≤s.val → Q2RawMomentBound p a b M s.val) :
    ∃ c>0,∃ C>0,∃ N : ℕ,2≤N ∧ ∀ n : ℕ,N≤n → ∀ σ : ℝ,σ≠0 →
      ENNReal.ofReal (c*(lowerBoundRate p n)^2)≤
        minimaxRiskDist (fun d => d^2) (subclassHurstTarget s (by linarith : 1≤p) (fixedRangeHurstClass p M a b))
          (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ∧
      minimaxRiskDist (fun d => d^2) (subclassHurstTarget s (by linarith : 1≤p) (fixedRangeHurstClass p M a b))
          (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b))≤
        minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a:=a) (b:=b) s (by linarith : 1≤p))
          (unknownHurstExperiment p M a b n) ∧
      minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a:=a) (b:=b) s (by linarith : 1≤p))
          (unknownHurstExperiment p M a b n)≤ENNReal.ofReal (C*(lowerBoundRate p n)^2) := by
  have hp1 : 1≤p := by linarith
  have hab : a≤b := by linarith
  have hu : ∃ C>0,∃ N : ℕ,2≤N ∧ ∀ n : ℕ,N≤n →
      minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a:=a) (b:=b) s hp1)
        (unknownHurstExperiment p M a b n)≤ENNReal.ofReal (C*(lowerBoundRate p n)^2) := by
    by_cases hs : s.val≤2
    · obtain ⟨C,hC,N,hN,hbound⟩ := unknownScale_q2_minimax_upper p a b M hp ha0 hb hab hM.le
      exact ⟨C,hC,N,by omega,fun n hn => hbound s hs n hn⟩
    · have hs' : 2≤s.val := le_of_lt (lt_of_not_ge hs)
      obtain ⟨C,hC,N,hN,hbound⟩ := unknownScale_q2_minimax_upper_of_raw_moments p a b M hp ha0 hb hab hM.le s hs' (hraw hs')
      exact ⟨C,hC,N,by omega,hbound⟩
  obtain ⟨C,hC,N,hN,hupper⟩ := hu
  obtain ⟨c,hc,hlower⟩ := fixedRange_minimax_squared_lower s p M a b hp1 hM ha hb0
  obtain ⟨K,hK⟩ := eventually_atTop.mp hlower
  refine ⟨c,hc,C,hC,max N K,hN.trans (le_max_left _ _),?_⟩
  intro n hn σ hσ
  exact ⟨hK n ((le_max_right _ _).trans hn) σ hσ,
    knownScale_minimax_le_unknown s p M a b σ hp1 hσ n _,hupper n ((le_max_left _ _).trans hn)⟩

end Hurst
