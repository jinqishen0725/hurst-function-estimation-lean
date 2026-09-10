import Hurst.UnknownEstimator
import Hurst.ScaleEquivariance

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem q2UnknownLocalEstimator_scale_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ t a b : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 2 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 4 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridSecondCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonStrideCoefficients n 1 4 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonStrideCoefficients n 2 4 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ x ∂featureGaussian v,
      q2UnknownLocalEstimator a b r n m δ t (σ • x) = q2UnknownLocalEstimator a b r n m δ t x := by
  have hz : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪gridSecondCoefficients n i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v (gridSecondCoefficients n i) (h₀ i))
  filter_upwards [hz, q2LogScaleEstimator_scale_ae r n m δ a b v hwm h₁ h₂ σ hσ] with x hx hs
  unfold q2UnknownLocalEstimator
  rw [gaussianLogStatistic_smul _ _ x σ hσ hx, hw, mul_one, hs]
  congr 1
  ring

theorem q2UnknownLocalEstimator_scale_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ t a b : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 2 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 4 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridSecondCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonStrideCoefficients n 1 4 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonStrideCoefficients n 2 4 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (Φ : ℝ → ℝ) :
    (∫ x, Φ (q2UnknownLocalEstimator a b r n m δ t x) ∂featureGaussian (fun i => σ • v i)) =
      ∫ x, Φ (q2UnknownLocalEstimator a b r n m δ t x) ∂featureGaussian v := by
  have he := featureGaussian_known_scale_integral v σ hσ (fun x => Φ (q2UnknownLocalEstimator a b r n m δ t (σ • x)))
  simp only [smul_smul, mul_inv_cancel₀ hσ, one_smul] at he
  apply he.trans
  apply integral_congr_ae
  filter_upwards [q2UnknownLocalEstimator_scale_ae r n m δ t a b v hw hwm h₀ h₁ h₂ σ hσ] with x hx
  exact congrArg Φ hx

end Hurst
