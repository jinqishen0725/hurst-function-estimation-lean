import Hurst.HurstExperiment

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace Hurst

def tailLoss (r x : ℝ≥0∞) : ℝ≥0∞ := if r < x then 1 else 0

theorem tailLoss_monotone (r : ℝ≥0∞) : Monotone (tailLoss r) := by
  intro x y hxy
  unfold tailLoss
  split_ifs with hx hy hy
  · rfl
  · exact (hy (hx.trans_le hxy)).elim
  · exact zero_le
  · rfl

def hurstTailRisk (s : {s : ℝ // 1 ≤ s}) (p M σ : ℝ) (hp : 1 ≤ p) (n : ℕ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  minimaxRiskDist (tailLoss r) (hurstTarget s hp) (hurstExperiment p M σ n)

theorem real_fano_fraction_bound (K L γ : ℝ) (hK : 0 ≤ K) (hL : 0 < L)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hbound : K + Real.log 2 ≤ (1 - γ) * L) :
    ENNReal.ofReal γ ≤ 1 - (ENNReal.ofReal K + ENNReal.ofReal (Real.log 2)) / ENNReal.ofReal L := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfrac : (ENNReal.ofReal K + ENNReal.ofReal (Real.log 2)) / ENNReal.ofReal L ≤
      ENNReal.ofReal (1 - γ) := by
    rw [← ENNReal.ofReal_add hK hlog, ← ENNReal.ofReal_div_of_pos hL]
    apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ hL).mpr hbound
  have hsum : ENNReal.ofReal γ + ENNReal.ofReal (1 - γ) = 1 := by
    rw [← ENNReal.ofReal_add hγ (by linarith), add_sub_cancel, ENNReal.ofReal_one]
  apply ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfrac)
  calc
    _ ≤ ENNReal.ofReal γ + ENNReal.ofReal (1 - γ) := by gcongr
    _ = 1 := hsum

theorem positive_tailLoss (r : ℝ) (hr : 0 < r) : tailLoss (ENNReal.ofReal r) (ENNReal.ofReal (2 * r)) = 1 := by
  unfold tailLoss
  rw [if_pos ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))]

/-- The decision-theoretic quantity is exactly an infimum of supremum tail probabilities. -/
theorem hurstTailRisk_eq_probability (s : {s : ℝ // 1 ≤ s}) (p M σ : ℝ) (hp : 1 ≤ p) (n : ℕ) (r : ℝ≥0∞) :
    hurstTailRisk s p M σ hp n r =
      ⨅ (κ : Kernel (EuclideanSpace ℝ (Fin n)) (HurstDecision s)) (_ : IsMarkovKernel κ),
        ⨆ H : HurstParameter p M, (κ ∘ₖ hurstExperiment p M σ n) H
          {y | r < edist (hurstTarget s hp H) y} := by
  unfold hurstTailRisk minimaxRiskDist minimaxRisk distortionLoss
  congr 1
  ext κ
  congr 1
  ext hκ
  congr 1
  ext H
  have hm : MeasurableSet {y : HurstDecision s | r < edist (hurstTarget s hp H) y} :=
    measurableSet_lt measurable_const (continuous_const.edist continuous_id).measurable
  simpa only [tailLoss, Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using!
    lintegral_indicator_one (μ := (κ ∘ₖ hurstExperiment p M σ n) H) hm

end Hurst
