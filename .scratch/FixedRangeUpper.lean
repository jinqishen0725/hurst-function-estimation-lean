import Hurst.EstimatorDecision
import Hurst.MinimaxUpperTransfer
import Hurst.HolderLpRisk
import Hurst.HolderQ2LpRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Hurst
set_option maxHeartbeats 1600000

/-- Actual known-scale q=1 minimax upper bound over all randomized measurable decisions. -/
theorem fixedRange_q1_minimax_upper (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧ ∀ σ : ℝ, σ ≠ 0 →
    ∀ s : {s : ℝ // 1 ≤ s}, s.val ≤ 2 → ∀ n : ℕ, N ≤ n →
    minimaxRiskDist (fun d => d ^ 2) (subclassHurstTarget s hp (fixedRangeHurstClass p M a b))
      (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ≤
      ENNReal.ofReal (C * (lowerBoundRate p n) ^ 2) := by
  obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q1_known_scale_Lp_risk p a b M hp ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨K, hK⟩ := eventually_atTop.mp (optimalLocalBandwidth_eventual_design p Nw hp)
  refine ⟨C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro σ hσ s hs n hn
  obtain ⟨hn1, hδ, hδhalf, hnd, _, _⟩ := hK n ((le_max_right N K).trans hn)
  have hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram (Nat.ceil p - 1) n 1 (optimalLocalBandwidth p n) t).det :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).1
  have hwb : ∀ t ∈ Icc (0 : ℝ) 1, ∑ i, |localPolynomialWeights (Nat.ceil p - 1) n 1 (optimalLocalBandwidth p n) t i| ≤ D :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).2.2.1
  let F := fun x => q1SpatialEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) (σ⁻¹ • x)
  have hFc : ∀ x, Continuous (F x) := fun x => q1SpatialEstimator_continuous _ n hn1 _ hdet _
  let T := fun x => continuousHurstDecision s (F x) (hFc x)
  have hT : Measurable T := (q1SpatialEstimator_decision_measurable s _ n hn1 _ D hD.le hdet hwb).comp (by fun_prop)
  unfold minimaxRiskDist
  apply minimaxRisk_le_deterministic _ _ (fun θ => by unfold distortionLoss; fun_prop) T hT
  intro H
  haveI : IsProbabilityMeasure (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val)) := by
    unfold scaledHarmonizableGaussian
    infer_instance
  obtain ⟨g, hg, heq, hgb, hgRisk⟩ := hrisk H.val.value H.val.property H.property
  have hFm : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => F z.1 z.2) :=
    (q1SpatialEstimator_joint_measurable _ n hn1 _ hdet).comp (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => (σ⁻¹ • z.1, z.2)))
  have he := continuous_decision_squared_risk
    (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val))
    s hs hp H.val g hg heq F hFc hFm (fun x t => q1SpatialEstimator_mem _ _ _ _ _) hgb
  change (∫⁻ x, edist (hurstTarget s hp H.val) (T x) ^ 2
    ∂scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val)) ≤ _
  rw [he]
  exact ENNReal.ofReal_le_ofReal (hgRisk σ hσ s.val ⟨s.property, hs⟩ n ((le_max_left N K).trans hn))

/-- Actual known-scale q=2 minimax upper bound for every original p>=2 and b<1. -/
theorem fixedRange_q2_minimax_upper (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧ ∀ σ : ℝ, σ ≠ 0 →
    ∀ s : {s : ℝ // 1 ≤ s}, s.val ≤ 2 → ∀ n : ℕ, N ≤ n →
    minimaxRiskDist (fun d => d ^ 2) (subclassHurstTarget s (by linarith : 1 ≤ p) (fixedRangeHurstClass p M a b))
      (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ≤
      ENNReal.ofReal (C * (lowerBoundRate p n) ^ 2) := by
  have hp1 : 1 ≤ p := by linarith
  have hb0 : 0 ≤ b := ha.le.trans hab
  obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q2_known_scale_Lp_risk p a b M hp ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 2
  obtain ⟨K, hK⟩ := eventually_atTop.mp (optimalLocalBandwidth_eventual_design p Nw hp1)
  refine ⟨C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro σ hσ s hs n hn
  obtain ⟨hn1, hδ, hδhalf, hnd, _, _⟩ := hK n ((le_max_right N K).trans hn)
  have hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram (Nat.ceil p - 1) n 2 (optimalLocalBandwidth p n) t).det :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).1
  have hwb : ∀ t ∈ Icc (0 : ℝ) 1, ∑ i, |localPolynomialWeights (Nat.ceil p - 1) n 2 (optimalLocalBandwidth p n) t i| ≤ D :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).2.2.1
  let F := fun x => q2SpatialEstimator b (Nat.ceil p - 1) n (optimalLocalBandwidth p n) (σ⁻¹ • x)
  have hFc : ∀ x, Continuous (F x) := fun x => q2SpatialEstimator_continuous b hb0 hb _ n hn1 _ hdet _
  let T := fun x => continuousHurstDecision s (F x) (hFc x)
  have hT : Measurable T := (q2SpatialEstimator_decision_measurable s b hb0 hb _ n hn1 _ D hD.le hdet hwb).comp (by fun_prop)
  unfold minimaxRiskDist
  apply minimaxRisk_le_deterministic _ _ (fun θ => by unfold distortionLoss; fun_prop) T hT
  intro H
  haveI : IsProbabilityMeasure (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val)) := by
    unfold scaledHarmonizableGaussian
    infer_instance
  obtain ⟨g, hg, heq, hgb, hgRisk⟩ := hrisk H.val.value H.val.property H.property
  have hFm : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => F z.1 z.2) :=
    (q2SpatialEstimator_joint_measurable b hb0 hb _ n hn1 _ hdet).comp (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => (σ⁻¹ • z.1, z.2)))
  have hFb : ∀ x t, F x t ∈ Icc (0 : ℝ) 1 := by
    intro x t
    have he := q2SpatialEstimator_mem b hb0 hb (Nat.ceil p - 1) n (optimalLocalBandwidth p n) (σ⁻¹ • x) t
    exact ⟨he.1, he.2.trans hb.le⟩
  have he := continuous_decision_squared_risk
    (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val))
    s hs hp1 H.val g hg heq F hFc hFm hFb (fun t ht => ⟨ha.le.trans (hgb ht).1, (hgb ht).2.trans hb.le⟩)
  change (∫⁻ x, edist (hurstTarget s hp1 H.val) (T x) ^ 2
    ∂scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val)) ≤ _
  rw [he]
  exact ENNReal.ofReal_le_ofReal (hgRisk σ hσ s.val ⟨s.property, hs⟩ n ((le_max_left N K).trans hn))

end Hurst
