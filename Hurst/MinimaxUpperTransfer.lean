import Hurst.UnitLpRisk
import Hurst.DecisionContinuity
import Hurst.SubclassMinimax

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem minimaxRisk_le_deterministic {Θ X Y : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Kernel Θ X) (loss : Θ → Y → ℝ≥0∞) (hloss : ∀ θ, Measurable (loss θ))
    (T : X → Y) (hT : Measurable T) (C : ℝ≥0∞)
    (hrisk : ∀ θ, (∫⁻ x, loss θ (T x) ∂P θ) ≤ C) :
    minimaxRisk loss P ≤ C := by
  unfold minimaxRisk
  refine (iInf_le_of_le (Kernel.deterministic T hT) (iInf_le_of_le inferInstance ?_))
  apply iSup_le
  intro θ
  rw [Kernel.deterministic_comp_eq_map, Kernel.map_apply _ hT, lintegral_map (hloss θ) hT]
  exact hrisk θ

/-- The original target is compared with a continuous extension only almost everywhere. -/
theorem hurstTarget_continuous_distance (s : {s : ℝ // 1 ≤ s}) {p M : ℝ} (hp : 1 ≤ p)
    (H : HurstParameter p M) (g F : ℝ → ℝ) (hg : Continuous g) (hF : Continuous F)
    (heq : EqOn H.value g (Ioo (0 : ℝ) 1)) :
    edist (hurstTarget s hp H) (continuousHurstDecision s F hF) =
      ENNReal.ofReal (unitLpLoss s.val F g) := by
  rw [edist_comm]
  have he : edist (continuousHurstDecision s F hF) (hurstTarget s hp H) =
      edist (continuousHurstDecision s F hF) (continuousHurstDecision s g hg) := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change F t - H.value t = F t - g t
    rw [heq ht]
  rw [he, continuousHurstDecision_distance_integral]
  rfl

theorem continuous_decision_squared_risk {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (s : {s : ℝ // 1 ≤ s}) (hs2 : s.val ≤ 2)
    {p M : ℝ} (hp : 1 ≤ p) (H : HurstParameter p M) (g : ℝ → ℝ) (hg : Continuous g)
    (heq : EqOn H.value g (Ioo (0 : ℝ) 1))
    (F : X → ℝ → ℝ) (hFc : ∀ x, Continuous (F x))
    (hFm : Measurable (fun z : X × ℝ => F z.1 z.2))
    (hFb : ∀ x t, F x t ∈ Icc (0 : ℝ) 1) (hgb : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) :
    (∫⁻ x, edist (hurstTarget s hp H) (continuousHurstDecision s (F x) (hFc x)) ^ 2 ∂P) =
      ENNReal.ofReal (∫ x, (unitLpLoss s.val (F x) g) ^ 2 ∂P) := by
  have hbd : ∀ x, (unitLpLoss s.val (F x) g) ^ 2 ≤ 1 := by
    intro x
    have he := continuousHurstDecision_edist_le_bound s (F x) g (hFc x) hg 1 (by
      intro t ht
      have hx := hFb x t
      have hy := hgb ⟨ht.1.le, ht.2.le⟩
      exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩)
    rw [continuousHurstDecision_distance_integral] at he
    have hr : unitLpLoss s.val (F x) g ≤ 1 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp he
    simpa only [one_pow] using pow_le_pow_left₀ (unitLpLoss_nonneg _ _ _) hr 2
  have hi : Integrable (fun x => (unitLpLoss s.val (F x) g) ^ 2) P := by
    apply Integrable.of_bound ((unitLpLoss_measurable s.val F g hFm hg.measurable).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbd x
  simp_rw [hurstTarget_continuous_distance s hp H g _ hg _ heq, ← ENNReal.ofReal_pow (unitLpLoss_nonneg _ _ _)]
  exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

end Hurst
