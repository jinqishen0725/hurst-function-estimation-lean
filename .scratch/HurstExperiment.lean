import Hurst.LossGeometry

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace Hurst

structure HurstParameter (p M : ℝ) where
  value : ℝ → ℝ
  property : value ∈ hurstHolderClass p M

instance (p M : ℝ) : MeasurableSpace (HurstParameter p M) := ⊤

theorem hurstParameter_continuousOn {p M : ℝ} (hp : 1 ≤ p) (H : HurstParameter p M) :
    ContinuousOn H.value (Ioo (0 : ℝ) 1) := by
  have hr : 0 < Nat.floor p := by
    have h : 1 ≤ Nat.floor p := (Nat.one_le_floor_iff p).mpr hp
    omega
  intro x hx
  have hd := H.property.2.1 0 hr x hx
  simp only [iteratedDeriv_zero] at hd
  exact hd.continuousAt.continuousWithinAt

def hurstTarget (s : {s : ℝ // 1 ≤ s}) {p M : ℝ} (hp : 1 ≤ p) (H : HurstParameter p M) :
    HurstDecision s := ⟨H.value, (hurstParameter_continuousOn hp H).aestronglyMeasurable measurableSet_Ioo⟩

def hurstExperiment (p M σ : ℝ) (n : ℕ) : Kernel (HurstParameter p M) (EuclideanSpace ℝ (Fin n)) where
  toFun H := scaledHarmonizableGaussian σ (midpointSampleHurst H.value H.property.1 n) (fun i => grid n i.val)
  measurable' := by
    intro t ht
    trivial

instance hurstExperiment_isMarkov (p M σ : ℝ) (n : ℕ) : IsMarkovKernel (hurstExperiment p M σ n) where
  isProbabilityMeasure H := by
    change IsProbabilityMeasure (scaledHarmonizableGaussian σ _ _)
    unfold scaledHarmonizableGaussian
    infer_instance

def bumpHurstParameter (p M ε : ℝ) (m : ℕ) (θ : Fin m → Bool)
    (hθ : bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M) : HurstParameter p M :=
  ⟨bumpAlternative m p ε (booleanBumpWeights θ), hθ⟩

theorem hurstTarget_bump (s : {s : ℝ // 1 ≤ s}) {p M ε : ℝ} (hp : 1 ≤ p)
    (m : ℕ) (θ : Fin m → Bool)
    (hθ : bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M) :
    hurstTarget s hp (bumpHurstParameter p M ε m θ hθ) =
      continuousHurstDecision s (bumpAlternative m p ε (booleanBumpWeights θ))
        (bumpAlternative_smooth m p ε _).continuous := rfl

/-- Finite-sample lower bound for the actual Hurst experiment, with the constructed code and no abstract model premise. -/
theorem hurst_minimax_finite_code (s : {s : ℝ // 1 ≤ s}) (p M : ℝ) (hp : 1 ≤ p) :
    ∃ A > 0, ∃ D > 0, ∃ c₀ > 0, ∃ b₀ > 0, ∃ C > 0,
      ∀ n : ℕ, 0 < n → ∀ m : ℕ, 0 < m → ∀ ε : ℝ, 0 ≤ ε →
      ∀ S : Finset (Fin m → Bool), 2 ≤ S.card →
      (∀ θ ∈ S, bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M) →
      (∀ θ ∈ S, ∀ η ∈ S, θ ≠ η → (m : ℝ) / 8 ≤ (hammingDist θ η : ℝ)) →
      ∀ σ : ℝ, σ ≠ 0 →
      A * ε * (m : ℝ) ^ (-p) * Real.log (2 * (n : ℝ)) ≤ c₀ →
      D * ε * (m : ℝ) ^ (1 - p) ≤ b₀ →
      ∀ (Φ : ℝ≥0∞ → ℝ≥0∞), Monotone Φ → ∀ δ : ℝ≥0∞,
      2 * δ ≤ ENNReal.ofReal (((∫ x : ℝ, |correctedBump x| ^ s.val) / 8) ^ s.val⁻¹ * ε * (m : ℝ) ^ (-p)) →
      Φ δ * (1 - (ENNReal.ofReal (C * ε ^ 2 * ((n : ℝ) * (m : ℝ) ^ (-2 * p) + (m : ℝ) ^ (2 - 2 * p)) *
          Real.log (2 * (n : ℝ)) ^ 2) + ENNReal.ofReal (Real.log 2)) / ENNReal.ofReal (Real.log (S.card : ℝ))) ≤
        minimaxRiskDist Φ (hurstTarget s hp) (hurstExperiment p M σ n) := by
  classical
  obtain ⟨A, hA, D, hD, c₀, hc₀, b₀, hb₀, C, hC, hk⟩ := bumpAlternative_klDiv_rate
  refine ⟨A, hA, D, hD, c₀, hc₀, b₀, hb₀, C, hC, ?_⟩
  intro n hn m hm ε hε S hS hclass hsep σ hσ hsmall hB Φ hΦ δ hδ
  letI : NeZero S.card := ⟨by omega⟩
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp : Fintype.card S = S.card)).symm
  let θfam : Fin S.card → HurstParameter p M := fun j =>
    bumpHurstParameter p M ε m (e j).val (hclass _ (e j).property)
  have hθ : Measurable θfam := measurable_of_countable _
  let R := scaledHarmonizableGaussian σ (fun _ : Fin n => brownianHurst) (fun i => grid n i.val)
  haveI : IsProbabilityMeasure R := by unfold R scaledHarmonizableGaussian; infer_instance
  refine minimax_subfamily_reference (hurstExperiment p M σ n) θfam hθ R _ ?_ hS Φ hΦ (hurstTarget s hp) δ ?_
  · intro j
    exact hk n hn m hm p ε hε (booleanBumpWeights (e j).val) (booleanBumpWeights_bound _)
      (hclass _ (e j).property).1 σ hσ hsmall hB
  · intro j k hjk
    have he : (e j).val ≠ (e k).val := fun h => hjk (e.injective (Subtype.ext h))
    exact hδ.trans (bumpAlternative_distance_separation s m hm p ε hε _ _
      (hsep _ (e j).property _ (e k).property he))

end Hurst
