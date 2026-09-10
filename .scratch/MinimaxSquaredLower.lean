import Hurst.SubclassMinimax

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Hurst

theorem minimax_squared_ge_tail {Θ X Y : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
    [PseudoEMetricSpace Y] [OpensMeasurableSpace Y]
    (P : Kernel Θ X) (g : Θ → Y) (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    r ^ 2 * minimaxRiskDist (tailLoss r) g P ≤ minimaxRiskDist (fun d => d ^ 2) g P := by
  have hr20 : r ^ 2 ≠ 0 := pow_ne_zero _ hr0
  have hr2t : r ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hrt
  unfold minimaxRiskDist minimaxRisk
  rw [ENNReal.mul_iInf_of_ne hr20 hr2t]
  apply iInf_mono
  intro κ
  rw [ENNReal.mul_iInf_of_ne hr20 hr2t]
  apply iInf_mono
  intro hκ
  rw [ENNReal.mul_iSup]
  apply iSup_mono
  intro θ
  rw [← lintegral_const_mul' _ _ hr2t]
  apply lintegral_mono
  intro y
  unfold distortionLoss tailLoss
  dsimp only
  split_ifs with h
  · simpa using pow_le_pow_left₀ (show 0 ≤ r from zero_le) h.le 2
  · simp

theorem fixedRange_minimax_squared_lower (s : {s : ℝ // 1 ≤ s}) (p M a b : ℝ)
    (hp : 1 ≤ p) (hM : 0 < M) (ha : a < 1 / 2) (hb : 1 / 2 < b) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ σ : ℝ, σ ≠ 0 →
    ENNReal.ofReal (c * (lowerBoundRate p n) ^ 2) ≤
      minimaxRiskDist (fun d => d ^ 2) (subclassHurstTarget s hp (fixedRangeHurstClass p M a b))
        (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) := by
  obtain ⟨δ, hδ, hlow⟩ := hurst_minimax_subclass_lower_eventually s p M (1/2) hp hM
    (by norm_num) (by norm_num) (fixedRangeHurstClass p M a b) (fixedRange_bump_inclusion p M a b hp ha hb)
  refine ⟨(3/4) * δ^2, by positivity, ?_⟩
  filter_upwards [hlow, eventually_ge_atTop 2] with n hn hn2
  intro σ hσ
  have hr : 0 < lowerBoundRate p n := by
    unfold lowerBoundRate
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn2
    have hl := Real.log_pos hnR
    positivity
  have he := minimax_squared_ge_tail
    (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b))
    (subclassHurstTarget s hp (fixedRangeHurstClass p M a b))
    (ENNReal.ofReal (δ * lowerBoundRate p n)) (by positivity) ENNReal.ofReal_ne_top
  apply le_trans _ he
  have hl := mul_le_mul_left' (hn σ hσ) (ENNReal.ofReal (δ * lowerBoundRate p n) ^ 2)
  change _ ≤ ENNReal.ofReal (δ * lowerBoundRate p n) ^ 2 * _
  change _ ≤ ENNReal.ofReal (δ * lowerBoundRate p n) ^ 2 * subclassHurstTailRisk s p M σ hp n (fixedRangeHurstClass p M a b) (ENNReal.ofReal (δ * lowerBoundRate p n))
  convert hl using 1
  norm_num only [show (1 + (1/2:ℝ))/2 = 3/4 by norm_num]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end Hurst
