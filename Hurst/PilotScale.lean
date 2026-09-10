import Hurst.PilotTransfer
import Hurst.KnownScaleRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem gaussianLogStatistic_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι)
    (σ : ℝ) (hσ : σ ≠ 0) (hx : ∀ i, ⟪a i, x⟫ ≠ 0) :
    gaussianLogStatistic w a (σ • x) = Real.log (σ^2)*(∑ i, w i)+gaussianLogStatistic w a x := by
  unfold gaussianLogStatistic
  simp only [real_inner_smul_right]
  simp_rw [log_square_scale σ _ hσ (hx _), mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem twoScalePilot_scale_invariant_ae {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a₁ a₂ : κ → EuclideanSpace ℝ ι)
    (h₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0) (h₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ x ∂featureGaussian v,
      twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) (σ • x) =
      twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) x := by
  have h₁ae : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪a₁ i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v (a₁ i) (h₁ i))
  have h₂ae : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪a₂ i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v (a₂ i) (h₂ i))
  filter_upwards [h₁ae, h₂ae] with x hx₁ hx₂
  unfold twoScalePilot
  rw [gaussianLogStatistic_smul w a₂ x σ hσ hx₂, gaussianLogStatistic_smul w a₁ x σ hσ hx₁]
  ring

/-- Unknown common scale cancels from every pilot loss functional in the actual experiment. -/
theorem twoScalePilot_scale_integral {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a₁ a₂ : κ → EuclideanSpace ℝ ι)
    (h₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0) (h₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (Φ : ℝ → ℝ) :
    (∫ x, Φ (twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) x)
      ∂featureGaussian (fun i => σ • v i)) =
    ∫ x, Φ (twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) x) ∂featureGaussian v := by
  let P := twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂)
  have he := featureGaussian_known_scale_integral v σ hσ (fun x => Φ (P (σ • x)))
  simp only [smul_smul, mul_inv_cancel₀ hσ, one_smul] at he
  apply he.trans
  apply integral_congr_ae
  filter_upwards [twoScalePilot_scale_invariant_ae v w a₁ a₂ h₁ h₂ σ hσ] with x hx
  exact congrArg Φ hx

end Hurst
