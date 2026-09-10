import Hurst.FiniteGaussianSpectral
import Hurst.FeatureObservationMap
import Hurst.FeatureQuadraticLimit
import Mathlib.Analysis.Matrix.Order

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder
namespace Hurst

variable {iota kappa E : Type*} [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The symmetric matrix of a weighted centered quadratic form after the
correlated standard Gaussian vector is represented as `R^(1/2) Z`. -/
def weightedFeatureQuadraticMatrix (v : iota → E)
    (a : kappa → EuclideanSpace ℝ iota) (w : kappa → ℝ) :
    Matrix kappa kappa ℝ :=
  let R := Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k))
  CFC.sqrt R * Matrix.diagonal w * CFC.sqrt R

theorem weightedFeatureQuadraticMatrix_isHermitian
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota)
    (w : kappa → ℝ) :
    (weightedFeatureQuadraticMatrix v a w).IsHermitian := by
  let R := Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k))
  have hs : (CFC.sqrt R).IsHermitian :=
    (CFC.sqrt_nonneg R).isSelfAdjoint.isHermitian
  simpa only [weightedFeatureQuadraticMatrix, R, hs.eq,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose (CFC.sqrt R)
      (Matrix.isHermitian_diagonal w)

/-- Algebraic identity for the quadratic form obtained by conjugating a
diagonal weight matrix by a ℝ symmetric matrix. -/
theorem matrixQuadratic_symmetric_diagonal_conjugate
    (S : Matrix kappa kappa ℝ) (hS : S.IsHermitian)
    (w : kappa → ℝ) (x : EuclideanSpace ℝ kappa) :
    dotProduct (WithLp.ofLp x)
        ((S * Matrix.diagonal w * S) *ᵥ WithLp.ofLp x) =
      ∑ i, w i * ((Matrix.toEuclideanCLM (𝕜 := ℝ) S x) i) ^ 2 := by
  rw [Matrix.mul_assoc]
  rw [← Matrix.mulVec_mulVec (WithLp.ofLp x) S (Matrix.diagonal w * S)]
  rw [← Matrix.mulVec_mulVec (WithLp.ofLp x) (Matrix.diagonal w) S]
  rw [Matrix.dotProduct_mulVec]
  rw [show (WithLp.ofLp x ᵥ* S) = S *ᵥ WithLp.ofLp x by
    rw [← Matrix.mulVec_transpose]
    rw [show Sᵀ = S by simpa [Matrix.IsHermitian] using hS]]
  simp only [dotProduct, Matrix.mulVec_diagonal,
    Matrix.ofLp_toEuclideanCLM]
  congr 1
  funext i
  ring

theorem weightedFeatureQuadraticMatrix_trace
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota)
    (w : kappa → ℝ) (ha : ∀ k, ∑ i, a k i • v i ≠ 0) :
    Matrix.trace (weightedFeatureQuadraticMatrix v a w) = ∑ k, w k := by
  let g : kappa → E := fun k ↦ standardizedFeatureVector v (a k)
  let R : Matrix kappa kappa ℝ := Matrix.gram ℝ g
  let S : Matrix kappa kappa ℝ := CFC.sqrt R
  have hR : R.PosSemidef := Matrix.posSemidef_gram ℝ g
  have hsquare : S * S = R := by
    exact CFC.sqrt_mul_sqrt_self R (ha := hR.nonneg)
  have hdiag : ∀ k, R k k = 1 := by
    intro k
    dsimp [R, g]
    rw [real_inner_self_eq_norm_sq,
      norm_standardizedFeatureVector v (a k) (ha k)]
    norm_num
  rw [weightedFeatureQuadraticMatrix]
  change Matrix.trace (S * Matrix.diagonal w * S) = _
  rw [Matrix.trace_mul_cycle, hsquare]
  rw [Matrix.trace_mul_comm R (Matrix.diagonal w)]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, hdiag]

/-- Pulling the weighted coordinate statistic back through the covariance
square root gives the centered symmetric matrix quadratic form pointwise. -/
theorem centeredSpectralSquares_covarianceSqrt_eq_centeredMatrixQuadratic
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota)
    (w : kappa → ℝ) (ha : ∀ k, ∑ i, a k i • v i ≠ 0)
    (x : EuclideanSpace ℝ kappa) :
    centeredSpectralSquares w
        (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (CFC.sqrt (Matrix.gram ℝ
            (fun k ↦ standardizedFeatureVector v (a k)))) x) =
      centeredMatrixQuadratic (weightedFeatureQuadraticMatrix v a w) x := by
  let R := Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k))
  let S := CFC.sqrt R
  have hS : S.IsHermitian := (CFC.sqrt_nonneg R).isSelfAdjoint.isHermitian
  rw [centeredSpectralSquares, centeredMatrixQuadratic,
    weightedFeatureQuadraticMatrix_trace v a w ha]
  rw [show weightedFeatureQuadraticMatrix v a w =
      S * Matrix.diagonal w * S by rfl]
  rw [matrixQuadratic_symmetric_diagonal_conjugate S hS w x]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]

/-- The feature-space quadratic statistic factors through the finite vector
of standardized observations. -/
theorem gaussianLogQuadraticStatistic_factor_observationMap
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota)
    (w : kappa → ℝ) (x : EuclideanSpace ℝ iota) :
    gaussianLogQuadraticStatistic v w a x =
      centeredSpectralSquares w (standardizedFeatureObservationMap v a x) := by
  unfold gaussianLogQuadraticStatistic centeredSpectralSquares
  apply Finset.sum_congr rfl
  intro k hk
  rw [standardizedFeatureObservationMap_apply]

/-- Replacing the original feature Gaussian by the finite vector of its
standardized observations preserves the law of the quadratic statistic. -/
theorem gaussianLogQuadraticStatistic_identDistrib_normalizedCoordinates
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota)
    (w : kappa → ℝ) :
    IdentDistrib (gaussianLogQuadraticStatistic v w a)
      (centeredSpectralSquares w)
      (featureGaussian v)
      (featureGaussian
        (fun k ↦ standardizedFeatureVector v (a k))) := by
  let L := standardizedFeatureObservationMap v a
  let F := centeredSpectralSquares w
  have hL : Measurable L := L.continuous.measurable
  have hF : Measurable F := by
    dsimp only [F]
    unfold centeredSpectralSquares
    exact Finset.measurable_sum _ fun k _ => by fun_prop
  refine ⟨(gaussianLogQuadraticStatistic_memLp_two v w a).1.aemeasurable,
    hF.aemeasurable, ?_⟩
  have hpoint : gaussianLogQuadraticStatistic v w a = F ∘ L := by
    funext x
    exact gaussianLogQuadraticStatistic_factor_observationMap v a w x
  rw [hpoint, ← Measure.map_map hF hL,
    featureGaussian_map_standardizedFeatureObservationMap]

/-- A weighted coordinate square statistic under its correlated Gaussian law
is the centered symmetric matrix quadratic form obtained by pulling back
through the positive covariance square root. -/
theorem centeredSpectralSquares_featureGaussian_identDistrib_centeredMatrixQuadratic
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota)
    (w : kappa → ℝ) (ha : ∀ k, ∑ i, a k i • v i ≠ 0) :
    IdentDistrib (centeredSpectralSquares w)
      (centeredMatrixQuadratic (weightedFeatureQuadraticMatrix v a w))
      (featureGaussian
        (fun k ↦ standardizedFeatureVector v (a k)))
      (stdGaussian (EuclideanSpace ℝ kappa)) := by
  let R : Matrix kappa kappa ℝ :=
    Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k))
  let T : EuclideanSpace ℝ kappa → EuclideanSpace ℝ kappa :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)
  let F := centeredSpectralSquares w
  let Q := centeredMatrixQuadratic (weightedFeatureQuadraticMatrix v a w)
  have hT : Measurable T := by
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)).continuous.measurable
  have hF : Measurable F := by
    dsimp only [F]
    unfold centeredSpectralSquares
    exact Finset.measurable_sum _ fun k _ => by fun_prop
  have hQ : Measurable Q := by
    dsimp only [Q]
    unfold centeredMatrixQuadratic
    fun_prop
  refine ⟨hF.aemeasurable, hQ.aemeasurable, ?_⟩
  change Measure.map F (multivariateGaussian 0 R) =
    Measure.map Q (stdGaussian (EuclideanSpace ℝ kappa))
  rw [multivariateGaussian]
  simp only [zero_add]
  rw [Measure.map_map hF hT]
  apply Measure.map_congr
  filter_upwards [] with x
  exact centeredSpectralSquares_covarianceSqrt_eq_centeredMatrixQuadratic
    v a w ha x

/-- Exact finite-dimensional spectral representation of the actual feature
quadratic statistic.  The target uses independent standard Gaussian
coordinates and the eigenvalues of the symmetric weighted covariance
matrix. -/
theorem gaussianLogQuadraticStatistic_identDistrib_eigenvalueSquares
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota)
    (w : kappa → ℝ) (ha : ∀ k, ∑ i, a k i • v i ≠ 0) :
    IdentDistrib (gaussianLogQuadraticStatistic v w a)
      (centeredSpectralSquares
        (weightedFeatureQuadraticMatrix_isHermitian v a w).eigenvalues)
      (featureGaussian v)
      (stdGaussian (EuclideanSpace ℝ kappa)) := by
  exact (gaussianLogQuadraticStatistic_identDistrib_normalizedCoordinates
    v a w).trans
      ((centeredSpectralSquares_featureGaussian_identDistrib_centeredMatrixQuadratic
        v a w ha).trans
        (centeredMatrixQuadratic_identDistrib_eigenvalueSquares
          (weightedFeatureQuadraticMatrix_isHermitian v a w)))

/-- The trace-square of the symmetric weighted covariance matrix is exactly
the signed weighted Hilbert--Schmidt energy of the correlation matrix. -/
theorem weightedFeatureQuadraticMatrix_trace_square
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota)
    (w : kappa → ℝ) :
    Matrix.trace
        (weightedFeatureQuadraticMatrix v a w *
          weightedFeatureQuadraticMatrix v a w) =
      ∑ i, ∑ j, w i * w j * (featureCorrelation v (a i) (a j)) ^ 2 := by
  let g : kappa → E := fun k ↦ standardizedFeatureVector v (a k)
  let R : Matrix kappa kappa ℝ := Matrix.gram ℝ g
  let S : Matrix kappa kappa ℝ := CFC.sqrt R
  let D : Matrix kappa kappa ℝ := Matrix.diagonal w
  have hR : R.PosSemidef := Matrix.posSemidef_gram ℝ g
  have hsquare : S * S = R := by
    exact CFC.sqrt_mul_sqrt_self R (ha := hR.nonneg)
  have hA : weightedFeatureQuadraticMatrix v a w = S * D * S := by
    rfl
  rw [hA]
  have hcycle :
      Matrix.trace ((S * D * S) * (S * D * S)) =
        Matrix.trace ((D * S * S * D) * S * S) := by
    calc
      Matrix.trace ((S * D * S) * (S * D * S)) =
          Matrix.trace (S * (D * S * S * D * S)) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((D * S * S * D * S) * S) :=
        Matrix.trace_mul_comm S (D * S * S * D * S)
      _ = Matrix.trace ((D * S * S * D) * S * S) := by
        congr 1
  rw [hcycle]
  have hreassoc : (D * S * S * D) * S * S =
      D * (S * S) * D * (S * S) := by
    simp only [Matrix.mul_assoc]
  rw [hreassoc, hsquare]
  have hgroup : D * R * D * R = (D * R) * (D * R) := by
    simp only [Matrix.mul_assoc]
  rw [hgroup]
  change Matrix.trace
      ((Matrix.diagonal w * R) * (Matrix.diagonal w * R)) = _
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mul_apply]
  simp_rw [Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [R, g]
  rw [standardizedFeatureVector_inner, standardizedFeatureVector_inner]
  have hcorr : featureCorrelation v (a j) (a i) =
      featureCorrelation v (a i) (a j) := by
    unfold featureCorrelation
    rw [real_inner_comm, mul_comm]
  rw [hcorr]
  ring

end Hurst
