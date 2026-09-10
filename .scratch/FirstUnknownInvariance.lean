import Hurst.FirstUnknownEstimator
import Hurst.ScaleEquivariance

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem q1UnknownLocalEstimator_scale_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ t : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 1 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridDifferenceCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ x ∂featureGaussian v,
      q1UnknownLocalEstimator r n m δ t (σ • x) = q1UnknownLocalEstimator r n m δ t x := by
  have hz : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪gridDifferenceCoefficients n i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v (gridDifferenceCoefficients n i) (h₀ i))
  filter_upwards [hz, q1LogScaleEstimator_scale_ae r n m δ v hwm h₁ h₂ σ hσ] with x hx hs
  unfold q1UnknownLocalEstimator
  rw [gaussianLogStatistic_smul _ _ x σ hσ hx, hw, mul_one, hs]
  congr 1
  ring

theorem q1UnknownLocalEstimator_scale_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ t : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 1 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridDifferenceCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (Φ : ℝ → ℝ) :
    (∫ x, Φ (q1UnknownLocalEstimator r n m δ t x) ∂featureGaussian (fun i => σ • v i)) =
      ∫ x, Φ (q1UnknownLocalEstimator r n m δ t x) ∂featureGaussian v := by
  have he := featureGaussian_known_scale_integral v σ hσ (fun x => Φ (q1UnknownLocalEstimator r n m δ t (σ • x)))
  simp only [smul_smul, mul_inv_cancel₀ hσ, one_smul] at he
  apply he.trans
  apply integral_congr_ae
  filter_upwards [q1UnknownLocalEstimator_scale_ae r n m δ t v hw hwm h₀ h₁ h₂ σ hσ] with x hx
  exact congrArg Φ hx

end Hurst
