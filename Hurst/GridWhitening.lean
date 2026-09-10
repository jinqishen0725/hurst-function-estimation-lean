import Hurst.GaussianLinearMap
import Hurst.HurstVariation
import Mathlib.LinearAlgebra.Matrix.Block

/-! The invertible first-difference whitening matrix, including its first row. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set InformationTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def previousGridIndex {n : ℕ} (i : Fin n) : Fin n :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

def differenceWhiteningMatrix {n : ℕ} (ℓ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if j = i then (Real.sqrt (ℓ i))⁻¹ else 0) -
    (if i.val = 0 then 0 else if j = previousGridIndex i then (Real.sqrt (ℓ i))⁻¹ else 0)

theorem differenceWhiteningMatrix_diagonal {n : ℕ} (ℓ : Fin n → ℝ) (i : Fin n) :
    differenceWhiteningMatrix ℓ i i = (Real.sqrt (ℓ i))⁻¹ := by
  by_cases hi : i.val = 0
  · simp [differenceWhiteningMatrix, hi]
  · have hp : i ≠ previousGridIndex i := by
      intro he
      have hv := congrArg Fin.val he
      simp only [previousGridIndex] at hv
      omega
    simp [differenceWhiteningMatrix, hi, hp]

theorem differenceWhiteningMatrix_lowerTriangular {n : ℕ} (ℓ : Fin n → ℝ) :
    (differenceWhiteningMatrix ℓ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hv : i.val < j.val := hij
  have hji : j ≠ i := by intro he; subst j; omega
  have hjp : j ≠ previousGridIndex i := by
    intro he
    have he' := congrArg Fin.val he
    simp only [previousGridIndex] at he'
    omega
  simp [differenceWhiteningMatrix, hji, hjp]

theorem differenceWhiteningMatrix_det_ne_zero {n : ℕ} (ℓ : Fin n → ℝ) (hl : ∀ i, 0 < ℓ i) :
    (differenceWhiteningMatrix ℓ).det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular _ (differenceWhiteningMatrix_lowerTriangular ℓ)]
  simp only [differenceWhiteningMatrix_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (Real.sqrt_pos.mpr (hl i)).ne'

theorem differenceWhiteningMatrix_feature {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin n → E) (ℓ : Fin n → ℝ) (i : Fin n) :
    (∑ j, differenceWhiteningMatrix ℓ i j • v j) =
      (Real.sqrt (ℓ i))⁻¹ • (v i - if i.val = 0 then 0 else v (previousGridIndex i)) := by
  by_cases hi : i.val = 0
  · simp [differenceWhiteningMatrix, hi, ite_smul]
  · simp [differenceWhiteningMatrix, hi, sub_smul, smul_sub, ite_smul, Finset.sum_sub_distrib]

/-- The first transformed observation is X(t₁)/√ℓ₁; subsequent rows are adjacent differences. -/
theorem differenceWhiteningMatrix_apply {n : ℕ} (ℓ : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (differenceWhiteningMatrix ℓ) x) i =
      (Real.sqrt (ℓ i))⁻¹ * (x i - if i.val = 0 then 0 else x (previousGridIndex i)) := by
  change (WithLp.ofLp (Matrix.toEuclideanCLM (𝕜 := ℝ) (differenceWhiteningMatrix ℓ) x)) i = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simpa only [smul_eq_mul, Matrix.mulVec, dotProduct] using differenceWhiteningMatrix_feature (fun j => x j) ℓ i

/-- Whitening is now an equality of observation laws, rather than only a covariance calculation. -/
theorem featureGaussian_map_differenceWhitening {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : Fin n → E) (ℓ : Fin n → ℝ) :
    (featureGaussian v).map (Matrix.toEuclideanCLM (𝕜 := ℝ) (differenceWhiteningMatrix ℓ)) =
      featureGaussian (fun i => (Real.sqrt (ℓ i))⁻¹ •
        (v i - if i.val = 0 then 0 else v (previousGridIndex i))) := by
  rw [featureGaussian_map_matrix]
  simp_rw [differenceWhiteningMatrix_feature]

theorem featureGaussian_klDiv_differenceWhitening {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v w : Fin n → E) (ℓ : Fin n → ℝ)
    (hl : ∀ i, 0 < ℓ i) :
    klDiv (featureGaussian (fun i => (Real.sqrt (ℓ i))⁻¹ •
      (v i - if i.val = 0 then 0 else v (previousGridIndex i))))
      (featureGaussian (fun i => (Real.sqrt (ℓ i))⁻¹ •
      (w i - if i.val = 0 then 0 else w (previousGridIndex i)))) =
      klDiv (featureGaussian v) (featureGaussian w) := by
  have he := featureGaussian_klDiv_matrix v w (differenceWhiteningMatrix ℓ)
    (isUnit_iff_ne_zero.mpr (differenceWhiteningMatrix_det_ne_zero ℓ hl))
  simpa only [differenceWhiteningMatrix_feature] using he

end Hurst
