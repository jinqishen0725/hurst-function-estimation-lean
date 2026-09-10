import Hurst.RealMomentTransfer
import Hurst.FirstUnknownInvariance
import Hurst.UnknownInvariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

def q1RawLogDifference (r n m : ℕ) (δ t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  gaussianLogStatistic (localPolynomialWeights r n 1 δ t)
    (gridDifferenceCoefficients n) x - q1LogScaleEstimator r n m δ x

def q2RawLogDifference (a b : ℝ) (r n m : ℕ) (δ t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  gaussianLogStatistic (localPolynomialWeights r n 2 δ t)
    (gridSecondCoefficients n) x - q2LogScaleEstimator a b r n m δ x

theorem q1RawLogDifference_measurable (r n m : ℕ) (δ t : ℝ) :
    Measurable (q1RawLogDifference r n m δ t) := by
  unfold q1RawLogDifference gaussianLogStatistic
  have hs := q1LogScaleEstimator_measurable r n m δ
  fun_prop

theorem q2RawLogDifference_measurable (a b : ℝ) (r n m : ℕ) (δ t : ℝ) :
    Measurable (q2RawLogDifference a b r n m δ t) := by
  unfold q2RawLogDifference gaussianLogStatistic
  have hs := q2LogScaleEstimator_measurable a b r n m δ
  fun_prop

theorem q1RawLogDifference_scale_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r n m : ℕ) (δ t : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 1 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridDifferenceCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ x ∂featureGaussian v,
      q1RawLogDifference r n m δ t (σ • x) = q1RawLogDifference r n m δ t x := by
  have hz : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪gridDifferenceCoefficients n i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v
      (gridDifferenceCoefficients n i) (h₀ i))
  filter_upwards [hz, q1LogScaleEstimator_scale_ae r n m δ v hwm h₁ h₂ σ hσ] with x hx hs
  unfold q1RawLogDifference
  rw [gaussianLogStatistic_smul _ _ x σ hσ hx, hw, mul_one, hs]
  ring

theorem q2RawLogDifference_scale_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a b : ℝ) (r n m : ℕ) (δ t : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 2 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 4 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridSecondCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonStrideCoefficients n 1 4 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonStrideCoefficients n 2 4 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ x ∂featureGaussian v,
      q2RawLogDifference a b r n m δ t (σ • x) =
        q2RawLogDifference a b r n m δ t x := by
  have hz : ∀ᵐ x ∂featureGaussian v, ∀ i, ⟪gridSecondCoefficients n i, x⟫ ≠ 0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v
      (gridSecondCoefficients n i) (h₀ i))
  filter_upwards [hz, q2LogScaleEstimator_scale_ae r n m δ a b v hwm h₁ h₂ σ hσ] with x hx hs
  unfold q2RawLogDifference
  rw [gaussianLogStatistic_smul _ _ x σ hσ hx, hw, mul_one, hs]
  ring

theorem q1RawLogDifference_scale_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r n m : ℕ) (δ t : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 1 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridDifferenceCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (Φ : ℝ → ℝ) :
    (∫ x, Φ (q1RawLogDifference r n m δ t x) ∂featureGaussian (fun i => σ • v i)) =
      ∫ x, Φ (q1RawLogDifference r n m δ t x) ∂featureGaussian v := by
  have he := featureGaussian_known_scale_integral v σ hσ
    (fun x => Φ (q1RawLogDifference r n m δ t (σ • x)))
  simp only [smul_smul, mul_inv_cancel₀ hσ, one_smul] at he
  apply he.trans
  apply integral_congr_ae
  filter_upwards [q1RawLogDifference_scale_ae r n m δ t v hw hwm h₀ h₁ h₂ σ hσ] with x hx
  exact congrArg Φ hx

theorem q2RawLogDifference_scale_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a b : ℝ) (r n m : ℕ) (δ t : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 2 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 4 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridSecondCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonStrideCoefficients n 1 4 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonStrideCoefficients n 2 4 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (Φ : ℝ → ℝ) :
    (∫ x, Φ (q2RawLogDifference a b r n m δ t x) ∂featureGaussian (fun i => σ • v i)) =
      ∫ x, Φ (q2RawLogDifference a b r n m δ t x) ∂featureGaussian v := by
  have he := featureGaussian_known_scale_integral v σ hσ
    (fun x => Φ (q2RawLogDifference a b r n m δ t (σ • x)))
  simp only [smul_smul, mul_inv_cancel₀ hσ, one_smul] at he
  apply he.trans
  apply integral_congr_ae
  filter_upwards [q2RawLogDifference_scale_ae a b r n m δ t v hw hwm h₀ h₁ h₂ σ hσ] with x hx
  exact congrArg Φ hx

theorem q1RawLogDifference_scale_memLp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r n m : ℕ) (δ t : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 1 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridDifferenceCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (s : ENNReal)
    (hmem : MemLp (q1RawLogDifference r n m δ t) s (featureGaussian v)) :
    MemLp (q1RawLogDifference r n m δ t) s
      (featureGaussian (fun i => σ • v i)) := by
  rw [← featureGaussian_map_smul v σ]
  apply (memLp_map_measure_iff
    (q1RawLogDifference_measurable r n m δ t).aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) => σ • x)
      (featureGaussian v))).mpr
  exact (memLp_congr_ae
    (q1RawLogDifference_scale_ae r n m δ t v hw hwm h₀ h₁ h₂ σ hσ)).mpr hmem

theorem q2RawLogDifference_scale_memLp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a b : ℝ) (r n m : ℕ) (δ t : ℝ) (v : Fin n → E)
    (hw : ∑ i, localPolynomialWeights r n 2 δ t i = 1)
    (hwm : ∑ i, averagedLocalWeights r n 4 m δ i = 1)
    (h₀ : ∀ i, ∑ j, gridSecondCoefficients n i j • v j ≠ 0)
    (h₁ : ∀ i, ∑ j, commonStrideCoefficients n 1 4 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonStrideCoefficients n 2 4 (by norm_num) i j • v j ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (s : ENNReal)
    (hmem : MemLp (q2RawLogDifference a b r n m δ t) s (featureGaussian v)) :
    MemLp (q2RawLogDifference a b r n m δ t) s
      (featureGaussian (fun i => σ • v i)) := by
  rw [← featureGaussian_map_smul v σ]
  apply (memLp_map_measure_iff
    (q2RawLogDifference_measurable a b r n m δ t).aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) => σ • x)
      (featureGaussian v))).mpr
  exact (memLp_congr_ae
    (q2RawLogDifference_scale_ae a b r n m δ t v hw hwm h₀ h₁ h₂ σ hσ)).mpr hmem

end Hurst
