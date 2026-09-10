import Hurst.ActualMomentRisk
import Hurst.FirstUnknownMinimax
import Hurst.UnknownMinimaxUpper

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Hurst

def Q1RawMomentBound (p a b M s : ℝ) : Prop :=
  ∃ C>0,∃ N : ℕ,4≤N ∧ ∀ f : ℝ → ℝ,∀ hf : f∈hurstHolderClass p M,
    MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
    ∃ g : ℝ → ℝ,Continuous g ∧ EqOn f g (Ioo (0:ℝ) 1) ∧ MapsTo g (Icc (0:ℝ) 1) (Icc a b) ∧
    ∀ σ : ℝ,σ≠0 → ∀ n : ℕ,N≤n → ∀ t∈Ioo (0:ℝ) 1,
      MemLp (fun x => gaussianLogStatistic (localPolynomialWeights (Nat.ceil p-1) n 1 (optimalLocalBandwidth p n) t) (gridDifferenceCoefficients n) x-q1LogScaleEstimator (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x) (ENNReal.ofReal s)
        (scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ∧
      (∫ x,|(gaussianLogStatistic (localPolynomialWeights (Nat.ceil p-1) n 1 (optimalLocalBandwidth p n) t) (gridDifferenceCoefficients n) x-q1LogScaleEstimator (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x)-calibrationOne (Real.log n) gaussianLogSquareMean (g t)|^s
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val))≤
        (2*Real.log n*(C*lowerBoundRate p n))^s

def Q2RawMomentBound (p a b M s : ℝ) : Prop :=
  ∃ C>0,∃ N : ℕ,4≤N ∧ ∀ f : ℝ → ℝ,∀ hf : f∈hurstHolderClass p M,
    MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
    ∃ g : ℝ → ℝ,Continuous g ∧ EqOn f g (Ioo (0:ℝ) 1) ∧ MapsTo g (Icc (0:ℝ) 1) (Icc a b) ∧
    ∀ σ : ℝ,σ≠0 → ∀ n : ℕ,N≤n → ∀ t∈Ioo (0:ℝ) 1,
      MemLp (fun x => gaussianLogStatistic (localPolynomialWeights (Nat.ceil p-1) n 2 (optimalLocalBandwidth p n) t) (gridSecondCoefficients n) x-q2LogScaleEstimator a b (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x) (ENNReal.ofReal s)
        (scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ∧
      (∫ x,|(gaussianLogStatistic (localPolynomialWeights (Nat.ceil p-1) n 2 (optimalLocalBandwidth p n) t) (gridSecondCoefficients n) x-q2LogScaleEstimator a b (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x)-calibrationTwo (Real.log n) gaussianLogSquareMean (g t)|^s
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val))≤
        (2*Real.log n*(C*lowerBoundRate p n))^s

theorem continuous_decision_squared_risk_allfinite {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (s : {s : ℝ // 1 ≤ s})
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


theorem unknownScale_q1_minimax_upper_of_raw_moments (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M) (s : {s : ℝ // 1≤s}) (hs : 2≤s.val)
    (hraw : Q1RawMomentBound p a b M s.val) :
    ∃ C > 0, ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    minimaxRiskDist (fun d => d ^ 2) (unknownHurstTarget (a := a) (b := b) s (by linarith : 1 ≤ p))
      (unknownHurstExperiment p M a b n) ≤
      ENNReal.ofReal (C * (lowerBoundRate p n) ^ 2) := by
  have hp1 : 1 ≤ p := by linarith
  have hb0 : 0 ≤ b := ha.le.trans hab
  obtain ⟨C, hC, N, hN, hrisk⟩ := hraw
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨K, hK⟩ := eventually_atTop.mp (optimalLocalBandwidth_eventual_design p Nw hp1)
  refine ⟨C^2, sq_pos_of_pos hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro n hn
  obtain ⟨hn1, hδ, hδhalf, hnd, _, _⟩ := hK n ((le_max_right N K).trans hn)
  have hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram (Nat.ceil p - 1) n 1 (optimalLocalBandwidth p n) t).det :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).1
  have hwb : ∀ t ∈ Icc (0 : ℝ) 1, ∑ i, |localPolynomialWeights (Nat.ceil p - 1) n 1 (optimalLocalBandwidth p n) t i| ≤ D :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).2.2.1
  let F := q1UnknownSpatialEstimator (Nat.ceil p - 1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n)
  have hFc : ∀ x, Continuous (F x) := fun x => q1UnknownSpatialEstimator_continuous _ n (scaleAverageResolution p n) hn1 _ hdet _
  let T := fun x => continuousHurstDecision s (F x) (hFc x)
  have hT : Measurable T := q1UnknownSpatialEstimator_decision_measurable s _ n (scaleAverageResolution p n) hn1 _ D hD.le hdet hwb
  unfold minimaxRiskDist
  apply minimaxRisk_le_deterministic _ _ (fun θ => by unfold distortionLoss; fun_prop) T hT
  intro θ
  let H := θ.hurst
  let σ := θ.scale
  have hσ : σ ≠ 0 := θ.scale_ne_zero
  haveI : IsProbabilityMeasure (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val)) := by
    unfold scaledHarmonizableGaussian
    infer_instance
  obtain ⟨g, hg, heq, hgb, hgRisk⟩ := hrisk H.val.value H.val.property H.property
  have hFm : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => F z.1 z.2) :=
    q1UnknownSpatialEstimator_joint_measurable _ n (scaleAverageResolution p n) hn1 _ hdet
  have hFb : ∀ x t, F x t ∈ Icc (0 : ℝ) 1 := by
    intro x t
    have he := q1UnknownSpatialEstimator_mem (Nat.ceil p - 1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x t
    exact he
  have he := continuous_decision_squared_risk_allfinite
    (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val))
    s hp1 H.val g hg heq F hFc hFm hFb (fun t ht => ⟨ha.le.trans (hgb ht).1,(hgb ht).2.trans (by linarith : b≤1)⟩)
  change (∫⁻ x, edist (hurstTarget s hp1 H.val) (T x) ^ 2
    ∂scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val)) ≤ _
  rw [he]
  have hrate : 0≤lowerBoundRate p n := by unfold lowerBoundRate; positivity
  have hh := q1_unknown_spatial_risk_of_raw_moments (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) hn1 
    (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val))
    s.val (C*lowerBoundRate p n) hs (mul_nonneg hC.le hrate) g hg (fun t ht => ⟨ha.le.trans (hgb ht).1,(hgb ht).2.trans (by linarith : b≤1)⟩)
    hdet (hgRisk σ hσ n ((le_max_left N K).trans hn))
  apply ENNReal.ofReal_le_ofReal
  convert hh using 1 <;> first | rfl | ring



theorem unknownScale_q2_minimax_upper_of_raw_moments (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) (s : {s : ℝ // 1≤s}) (hs : 2≤s.val)
    (hraw : Q2RawMomentBound p a b M s.val) :
    ∃ C > 0, ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    minimaxRiskDist (fun d => d ^ 2) (unknownHurstTarget (a := a) (b := b) s (by linarith : 1 ≤ p))
      (unknownHurstExperiment p M a b n) ≤
      ENNReal.ofReal (C * (lowerBoundRate p n) ^ 2) := by
  have hp1 : 1 ≤ p := by linarith
  have hb0 : 0 ≤ b := ha.le.trans hab
  obtain ⟨C, hC, N, hN, hrisk⟩ := hraw
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 2
  obtain ⟨K, hK⟩ := eventually_atTop.mp (optimalLocalBandwidth_eventual_design p Nw hp1)
  refine ⟨C^2, sq_pos_of_pos hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro n hn
  obtain ⟨hn1, hδ, hδhalf, hnd, _, _⟩ := hK n ((le_max_right N K).trans hn)
  have hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram (Nat.ceil p - 1) n 2 (optimalLocalBandwidth p n) t).det :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).1
  have hwb : ∀ t ∈ Icc (0 : ℝ) 1, ∑ i, |localPolynomialWeights (Nat.ceil p - 1) n 2 (optimalLocalBandwidth p n) t i| ≤ D :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).2.2.1
  let F := q2UnknownSpatialEstimator a b (Nat.ceil p - 1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n)
  have hFc : ∀ x, Continuous (F x) := fun x => q2UnknownSpatialEstimator_continuous a b hb0 hb _ n (scaleAverageResolution p n) hn1 _ hdet _
  let T := fun x => continuousHurstDecision s (F x) (hFc x)
  have hT : Measurable T := q2UnknownSpatialEstimator_decision_measurable s a b hb0 hb _ n (scaleAverageResolution p n) hn1 _ D hD.le hdet hwb
  unfold minimaxRiskDist
  apply minimaxRisk_le_deterministic _ _ (fun θ => by unfold distortionLoss; fun_prop) T hT
  intro θ
  let H := θ.hurst
  let σ := θ.scale
  have hσ : σ ≠ 0 := θ.scale_ne_zero
  haveI : IsProbabilityMeasure (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val)) := by
    unfold scaledHarmonizableGaussian
    infer_instance
  obtain ⟨g, hg, heq, hgb, hgRisk⟩ := hrisk H.val.value H.val.property H.property
  have hFm : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => F z.1 z.2) :=
    q2UnknownSpatialEstimator_joint_measurable a b hb0 hb _ n (scaleAverageResolution p n) hn1 _ hdet
  have hFb : ∀ x t, F x t ∈ Icc (0 : ℝ) 1 := by
    intro x t
    have he := q2UnknownSpatialEstimator_mem a b hb0 hb (Nat.ceil p - 1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x t
    exact ⟨he.1, he.2.trans hb.le⟩
  have he := continuous_decision_squared_risk_allfinite
    (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val))
    s hp1 H.val g hg heq F hFc hFm hFb (fun t ht => ⟨ha.le.trans (hgb ht).1, (hgb ht).2.trans hb.le⟩)
  change (∫⁻ x, edist (hurstTarget s hp1 H.val) (T x) ^ 2
    ∂scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val)) ≤ _
  rw [he]
  have hrate : 0≤lowerBoundRate p n := by unfold lowerBoundRate; positivity
  have hh := q2_unknown_spatial_risk_of_raw_moments (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) hn1 a b hb0 hb 
    (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val))
    s.val (C*lowerBoundRate p n) hs (mul_nonneg hC.le hrate) g hg (fun t ht => ⟨ha.le.trans (hgb ht).1,(hgb ht).2⟩)
    hdet (hgRisk σ hσ n ((le_max_left N K).trans hn))
  apply ENNReal.ofReal_le_ofReal
  convert hh using 1 <;> first | rfl | ring



end Hurst
