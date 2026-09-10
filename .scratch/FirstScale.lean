import Hurst.CommonFirstMean
import Hurst.MergedFirstVariance
import Hurst.LinearScale
import Hurst.ScaleEquivariance

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

def q1LinearScale (r n m : ℕ) (δ : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  linearScaleCombination (Real.log n)
    (gaussianLogStatistic (averagedLocalWeights r n 2 m δ) (commonFirstStrideCoefficients n 1 2 (by norm_num)))
    (gaussianLogStatistic (averagedLocalWeights r n 2 m δ) (commonFirstStrideCoefficients n 2 2 (by norm_num)))

def q1LogScaleEstimator (r n m : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  q1LinearScale r n m δ x - gaussianLogSquareMean

theorem q1LogScaleEstimator_measurable (r n m : ℕ) (δ : ℝ) :
    Measurable (q1LogScaleEstimator r n m δ) := by
  unfold q1LogScaleEstimator q1LinearScale linearScaleCombination gaussianLogStatistic
  fun_prop

theorem q1LogScaleEstimator_scale_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ : ℝ) (v : Fin n → E)
    (hw : ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₁ : ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ x ∂featureGaussian v, q1LogScaleEstimator r n m δ (σ • x) =
      q1LogScaleEstimator r n m δ x + Real.log (σ^2) := by
  have hz₁ : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪commonFirstStrideCoefficients n 1 2 (by norm_num) i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v _ (h₁ i))
  have hz₂ : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪commonFirstStrideCoefficients n 2 2 (by norm_num) i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v _ (h₂ i))
  filter_upwards [hz₁,hz₂] with x hx₁ hx₂
  unfold q1LogScaleEstimator q1LinearScale linearScaleCombination
  rw [gaussianLogStatistic_smul _ _ x σ hσ hx₁,gaussianLogStatistic_smul _ _ x σ hσ hx₂,hw,mul_one]
  ring

end Hurst
