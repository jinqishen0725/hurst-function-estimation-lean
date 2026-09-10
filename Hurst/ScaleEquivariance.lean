import Hurst.ScaleAverage
import Hurst.PilotScale

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem averagedLocalWeights_sum (r n q m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hw : ∀ j : Fin m, ∑ i, localPolynomialWeights r n q δ (grid m j.val) i = 1) :
    (∑ i, averagedLocalWeights r n q m δ i) = 1 := by
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold averagedLocalWeights
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self hmR

theorem q2LogScaleEstimator_scale_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ a b : ℝ) (v : Fin n → E)
    (hw : ∑ i, averagedLocalWeights r n 4 m δ i = 1)
    (h₁ : ∀ i, ∑ j, commonStrideCoefficients n 1 4 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonStrideCoefficients n 2 4 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ x ∂featureGaussian v,
      q2LogScaleEstimator a b r n m δ (σ • x) = q2LogScaleEstimator a b r n m δ x+Real.log (σ^2) := by
  let a₁ := commonStrideCoefficients n 1 4 (by norm_num)
  let a₂ := commonStrideCoefficients n 2 4 (by norm_num)
  have hz₁ : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪a₁ i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v (a₁ i) (h₁ i))
  have hz₂ : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪a₂ i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v (a₂ i) (h₂ i))
  have hp : ∀ᵐ x ∂featureGaussian v, ∀ j : Fin m, q2Pilot r n δ (grid m j.val) (σ • x) = q2Pilot r n δ (grid m j.val) x :=
    ae_all_iff.mpr (fun j => twoScalePilot_scale_invariant_ae v (localPolynomialWeights r n 4 δ (grid m j.val)) a₁ a₂ h₁ h₂ σ hσ)
  filter_upwards [hz₁, hz₂, hp] with x hx₁ hx₂ hpx
  unfold q2LogScaleEstimator
  simp only [hpx]
  unfold q2LinearScale linearScaleCombination
  rw [gaussianLogStatistic_smul _ a₁ x σ hσ hx₁, gaussianLogStatistic_smul _ a₂ x σ hσ hx₂, hw]
  ring

theorem q2LogScaleEstimator_scale_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ a b : ℝ) (v : Fin n → E)
    (hw : ∑ i, averagedLocalWeights r n 4 m δ i = 1)
    (h₁ : ∀ i, ∑ j, commonStrideCoefficients n 1 4 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonStrideCoefficients n 2 4 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (Φ : ℝ → ℝ) :
    (∫ x, Φ (q2LogScaleEstimator a b r n m δ x-Real.log (σ^2)) ∂featureGaussian (fun i => σ • v i)) =
      ∫ x, Φ (q2LogScaleEstimator a b r n m δ x) ∂featureGaussian v := by
  have he := featureGaussian_known_scale_integral v σ hσ
    (fun x => Φ (q2LogScaleEstimator a b r n m δ (σ • x)-Real.log (σ^2)))
  simp only [smul_smul, mul_inv_cancel₀ hσ, one_smul] at he
  apply he.trans
  apply integral_congr_ae
  filter_upwards [q2LogScaleEstimator_scale_ae r n m δ a b v hw h₁ h₂ σ hσ] with x hx
  rw [hx, add_sub_cancel_right]

end Hurst
