/-
Adapted from StatLean/Stat-Lean, commit 855b6afb69fead1bef066111732ed44df181040e,
StatLean/Minimaxity/ForMathlib/KLDivergence.lean. Apache-2.0; see third_party/StatLean/LICENSE.
Local changes: only measurable-equivalence and two-factor product proof extracted; namespace changed.
-/
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace Hurst

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- KL divergence is invariant under pushforward by a measurable equivalence. This is the
standard reparametrization-invariance of an `f`-divergence; we prove it from the
log-likelihood-ratio integral form together with `MeasurableEmbedding.rnDeriv_map`. -/
private lemma klDiv_map_measurableEquiv (e : α ≃ᵐ γ) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  have hf := e.measurableEmbedding
  haveI : IsFiniteMeasure (μ.map e) := μ.isFiniteMeasure_map e
  haveI : IsFiniteMeasure (ν.map e) := ν.isFiniteMeasure_map e
  by_cases hμν : μ ≪ ν
  · have hμν' : μ.map e ≪ ν.map e := hf.absolutelyContinuous_map hμν
    rw [klDiv_eq_lintegral_klFun_of_ac hμν', klDiv_eq_lintegral_klFun_of_ac hμν,
      hf.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hf.rnDeriv_map μ ν] with x hx
    rw [hx]
  · have hne : ¬ (μ.map e ≪ ν.map e) := by
      intro hac
      apply hμν
      have h := hac.map e.symm.measurable
      rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at h
    rw [klDiv_of_not_ac hμν, klDiv_of_not_ac hne]

/-- The residual term in the product chain rule: for product measures with a common first
factor `μ₁` (a probability measure), the KL divergence collapses to the second-factor
divergence. Proved by swapping coordinates (`Measure.prod_swap`) so the common factor becomes
the conditional kernel, then applying `klDiv_compProd_left`. -/
private lemma klDiv_prod_const_fst (μ₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) = klDiv μ₂ ν₂ := by
  rw [← klDiv_map_measurableEquiv (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)
    (μ₁.prod μ₂) (μ₁.prod ν₂),
    show ⇑(MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) = Prod.swap from rfl,
    Measure.prod_swap, Measure.prod_swap, ← Measure.compProd_const, ← Measure.compProd_const,
    klDiv_compProd_left]

/-- **Additivity of KL over products** (Wainwright Eq. (15.11a), two-factor case):
`D(ℙ₁⊗ℙ₂ ‖ ℚ₁⊗ℚ₂) = D(ℙ₁ ‖ ℚ₁) + D(ℙ₂ ‖ ℚ₂)`. Follows from the Mathlib chain rule
`klDiv_compProd_eq_add` applied to the product written as a composition–product with a
constant kernel.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.11a). -/
theorem klDiv_prod_eq_add
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  rw [← Measure.compProd_const (μ := μ₁) (ν := μ₂),
    ← Measure.compProd_const (μ := ν₁) (ν := ν₂), klDiv_compProd_eq_add,
    Measure.compProd_const, Measure.compProd_const, klDiv_prod_const_fst]

end Hurst
