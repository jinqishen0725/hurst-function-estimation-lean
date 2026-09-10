import Hurst.MinimaxSquaredLower

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Hurst

structure UnknownHurstParameter (p M a b : ℝ) where
  hurst : fixedRangeHurstClass p M a b
  scale : ℝ
  scale_ne_zero : scale ≠ 0

instance (p M a b : ℝ) : MeasurableSpace (UnknownHurstParameter p M a b) := ⊤

def unknownHurstExperiment (p M a b : ℝ) (n : ℕ) :
    Kernel (UnknownHurstParameter p M a b) (EuclideanSpace ℝ (Fin n)) where
  toFun θ := scaledHarmonizableGaussian θ.scale
    (midpointSampleHurst θ.hurst.val.value θ.hurst.val.property.1 n) (fun i => grid n i.val)
  measurable' := by intro t ht; trivial

instance unknownHurstExperiment_isMarkov (p M a b : ℝ) (n : ℕ) :
    IsMarkovKernel (unknownHurstExperiment p M a b n) where
  isProbabilityMeasure θ := by
    change IsProbabilityMeasure (scaledHarmonizableGaussian _ _ _)
    unfold scaledHarmonizableGaussian
    infer_instance

def unknownHurstTarget (s : {s : ℝ // 1 ≤ s}) {p M a b : ℝ} (hp : 1 ≤ p) :
    UnknownHurstParameter p M a b → HurstDecision s := fun θ => hurstTarget s hp θ.hurst.val

theorem minimaxRisk_restrict_le {Θ X Y I : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]
    (loss : Θ → Y → ℝ≥0∞) (P : Kernel Θ X) (e : I → Θ) (he : Measurable e) :
    minimaxRisk (fun i => loss (e i)) (P.comap e he) ≤ minimaxRisk loss P := by
  refine iInf₂_mono fun κ _ => iSup_le fun i => le_iSup_of_le (e i) ?_
  have hcomp : (κ ∘ₖ (P.comap e he)) i = (κ ∘ₖ P) (e i) := by
    rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.comap_apply]
  rw [hcomp]

theorem knownScale_minimax_le_unknown (s : {s : ℝ // 1 ≤ s})
    (p M a b σ : ℝ) (hp : 1 ≤ p) (hσ : σ ≠ 0) (n : ℕ) (Φ : ℝ≥0∞ → ℝ≥0∞) :
    minimaxRiskDist Φ (subclassHurstTarget s hp (fixedRangeHurstClass p M a b))
      (subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b)) ≤
    minimaxRiskDist Φ (unknownHurstTarget (a := a) (b := b) s hp) (unknownHurstExperiment p M a b n) := by
  let e : fixedRangeHurstClass p M a b → UnknownHurstParameter p M a b := fun H => ⟨H, σ, hσ⟩
  have he : Measurable e := by
    intro t ht
    refine ⟨Subtype.val '' (e ⁻¹' t), trivial, ?_⟩
    exact Set.preimage_image_eq _ Subtype.val_injective
  have hP : (unknownHurstExperiment p M a b n).comap e he =
      subclassHurstExperiment p M σ n (fixedRangeHurstClass p M a b) := by
    ext H S hS
    rfl
  have hr := minimaxRisk_restrict_le (distortionLoss Φ (unknownHurstTarget (a := a) (b := b) s hp))
    (unknownHurstExperiment p M a b n) e he
  rw [hP] at hr
  exact hr

theorem unknownScale_minimax_squared_lower (s : {s : ℝ // 1 ≤ s}) (p M a b : ℝ)
    (hp : 1 ≤ p) (hM : 0 < M) (ha : a < 1/2) (hb : 1/2 < b) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (lowerBoundRate p n)^2) ≤
        minimaxRiskDist (fun d => d^2) (unknownHurstTarget (a := a) (b := b) s hp)
          (unknownHurstExperiment p M a b n) := by
  obtain ⟨c, hc, hl⟩ := fixedRange_minimax_squared_lower s p M a b hp hM ha hb
  refine ⟨c, hc, ?_⟩
  filter_upwards [hl] with n hn
  exact (hn 1 (by norm_num)).trans (knownScale_minimax_le_unknown s p M a b 1 hp (by norm_num) n _)

end Hurst
