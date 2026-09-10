import Hurst.FirstScale

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem q1LogScaleEstimator_scale_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ : ℝ) (v : Fin n → E)
    (hw : ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₁ : ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (Φ : ℝ → ℝ) :
    (∫ x, Φ (q1LogScaleEstimator r n m δ x-Real.log (σ^2)) ∂featureGaussian (fun i => σ • v i)) =
      ∫ x, Φ (q1LogScaleEstimator r n m δ x) ∂featureGaussian v := by
  have he := featureGaussian_known_scale_integral v σ hσ
    (fun x => Φ (q1LogScaleEstimator r n m δ (σ • x)-Real.log (σ^2)))
  simp only [smul_smul,mul_inv_cancel₀ hσ,one_smul] at he
  apply he.trans
  apply integral_congr_ae
  filter_upwards [q1LogScaleEstimator_scale_ae r n m δ v hw h₁ h₂ σ hσ] with x hx
  rw [hx,add_sub_cancel_right]

end Hurst
