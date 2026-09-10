import Hurst.GaussianQuadraticVariance
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Probability.Distributions.Gaussian.Multivariate

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

namespace Hurst

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinates of a Euclidean vector in the orthonormal eigenbasis of a
real symmetric matrix. -/
def hermitianEigenCoordinates {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  hA.eigenvectorBasis.repr

/-- Orthogonal eigenbasis coordinates preserve the canonical standard
multivariate Gaussian measure. -/
theorem stdGaussian_map_hermitianEigenCoordinates
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (hermitianEigenCoordinates hA) =
      stdGaussian (EuclideanSpace ℝ ι) := by
  exact stdGaussian_map (hermitianEigenCoordinates hA)

/-- Orthogonal eigenbasis coordinates are measure preserving for the standard
multivariate Gaussian measure. -/
theorem hermitianEigenCoordinates_measurePreserving
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    MeasurePreserving (hermitianEigenCoordinates hA)
      (stdGaussian (EuclideanSpace ℝ ι))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  refine ⟨(hermitianEigenCoordinates hA).continuous.measurable, ?_⟩
  exact stdGaussian_map_hermitianEigenCoordinates hA

/-- The centered quadratic form associated with a real matrix. -/
def centeredMatrixQuadratic (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  dotProduct (WithLp.ofLp x) (A *ᵥ WithLp.ofLp x) - A.trace

/-- A finite centered second-chaos spectral sum. -/
def centeredSpectralSquares (lam : ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, lam i * (x i ^ 2 - 1)

theorem hermitianEigenvector_toEuclideanLin
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i : ι) :
    A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply WithLp.ofLp_injective
  exact hA.mulVec_eigenvectorBasis i

/-- In eigenbasis coordinates, a symmetric matrix acts by coordinatewise
multiplication by its eigenvalues. -/
theorem hermitianEigenCoordinates_toEuclideanLin_apply
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    hermitianEigenCoordinates hA (A.toEuclideanLin x) i =
      hA.eigenvalues i * hermitianEigenCoordinates hA x i := by
  rw [hermitianEigenCoordinates, OrthonormalBasis.repr_apply_apply,
    ← (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (hA.eigenvectorBasis i) x,
    hermitianEigenvector_toEuclideanLin hA i, real_inner_smul_left,
    OrthonormalBasis.repr_apply_apply]

/-- Pointwise spectral expansion of a real symmetric quadratic form. -/
theorem matrixQuadratic_eq_eigenvalue_sum
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ ι) :
    dotProduct (WithLp.ofLp x) (A *ᵥ WithLp.ofLp x) =
      ∑ i, hA.eigenvalues i * (hermitianEigenCoordinates hA x i) ^ 2 := by
  rw [dotProduct_comm]
  have hxstar : star (WithLp.ofLp x) = WithLp.ofLp x := by
    ext i
    simp
  conv_lhs =>
    rhs
    rw [← hxstar]
  rw [← EuclideanSpace.inner_eq_star_dotProduct]
  change inner ℝ x (A.toEuclideanLin x) = _
  rw [← (hermitianEigenCoordinates hA).inner_map_map x (A.toEuclideanLin x)]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hermitianEigenCoordinates_toEuclideanLin_apply hA x i]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The pointwise centered spectral decomposition. -/
theorem centeredMatrixQuadratic_eq_centeredSpectralSquares_eigenCoordinates
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ ι) :
    centeredMatrixQuadratic A x =
      centeredSpectralSquares hA.eigenvalues (hermitianEigenCoordinates hA x) := by
  have htrace : A.trace = ∑ i, hA.eigenvalues i := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using hA.trace_eq_sum_eigenvalues
  rw [centeredMatrixQuadratic, matrixQuadratic_eq_eigenvalue_sum hA x, htrace]
  unfold centeredSpectralSquares
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]

/-- A centered quadratic form of a standard Gaussian vector has exactly the
law of the eigenvalue-weighted sum of independent centered Gaussian squares.

Independence is encoded by the canonical `stdGaussian` law on Euclidean
space: its coordinate law is the product of one-dimensional standard Gaussian
measures. -/
theorem centeredMatrixQuadratic_identDistrib_eigenvalueSquares
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    IdentDistrib (centeredMatrixQuadratic A)
      (centeredSpectralSquares hA.eigenvalues)
      (stdGaussian (EuclideanSpace ℝ ι))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let R := hermitianEigenCoordinates hA
  let S := centeredSpectralSquares hA.eigenvalues
  have hR : IdentDistrib R id
      (stdGaussian (EuclideanSpace ℝ ι))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    refine ⟨(hermitianEigenCoordinates hA).continuous.measurable.aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    simpa [R] using stdGaussian_map_hermitianEigenCoordinates hA
  have hS := hR.comp (show Measurable S by
    dsimp [S, centeredSpectralSquares]
    exact Finset.measurable_sum _ fun i _ => by fun_prop)
  have hpoint : centeredMatrixQuadratic A = S ∘ R := by
    funext x
    exact centeredMatrixQuadratic_eq_centeredSpectralSquares_eigenCoordinates hA x
  rw [hpoint]
  convert hS using 1
  · funext x
    rfl

theorem euclidean_coordinate_eq_basisFun_inner
    (x : EuclideanSpace ℝ ι) (i : ι) :
    x i = inner ℝ (EuclideanSpace.basisFun ι ℝ i) x :=
  (EuclideanSpace.basisFun_inner ι ℝ x i).symm

/-- Each coordinate of the canonical finite-dimensional standard Gaussian is
a standard one-dimensional Gaussian. -/
theorem stdGaussian_coordinate_measurePreserving (i : ι) :
    MeasurePreserving (fun x : EuclideanSpace ℝ ι => x i)
      (stdGaussian (EuclideanSpace ℝ ι)) (gaussianReal 0 1) := by
  let e := EuclideanSpace.basisFun ι ℝ i
  have hG : HasGaussianLaw (fun x : EuclideanSpace ℝ ι => x i)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    convert IsGaussian.hasGaussianLaw_id.map_fun (innerSL ℝ e) using 1 <;>
      first
      | rfl
      | infer_instance
      | (funext x; exact euclidean_coordinate_eq_basisFun_inner x i)
  have hm : (∫ x : EuclideanSpace ℝ ι, x i ∂stdGaussian (EuclideanSpace ℝ ι)) = 0 := by
    simp_rw [euclidean_coordinate_eq_basisFun_inner]
    change (∫ x, (innerSL ℝ e) x ∂stdGaussian (EuclideanSpace ℝ ι)) = 0
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]
  have hv : Var[fun x : EuclideanSpace ℝ ι => x i;
      stdGaussian (EuclideanSpace ℝ ι)] = 1 := by
    have he : (fun x : EuclideanSpace ℝ ι => x i) =
      fun x => inner ℝ e x := by
      funext x
      exact euclidean_coordinate_eq_basisFun_inner x i
    rw [he, ← covariance_self (by fun_prop),
      ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian]
    change inner ℝ e e = 1
    simp [e]
  refine ⟨by fun_prop, ?_⟩
  rw [hG.map_eq_gaussianReal, hm, hv]
  norm_num

/-- Every pair of canonical standard-Gaussian coordinates is jointly
Gaussian. -/
theorem stdGaussian_coordinate_pair_hasGaussianLaw (i j : ι) :
    HasGaussianLaw
      (fun x : EuclideanSpace ℝ ι => (x i, x j))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let ei := EuclideanSpace.basisFun ι ℝ i
  let ej := EuclideanSpace.basisFun ι ℝ j
  convert IsGaussian.hasGaussianLaw_id.map_fun
    ((innerSL ℝ ei).prod (innerSL ℝ ej)) using 1 <;>
      first
      | rfl
      | infer_instance
      | (funext x; ext <;> first
          | exact euclidean_coordinate_eq_basisFun_inner x i
          | exact euclidean_coordinate_eq_basisFun_inner x j)

/-- The covariance matrix of the canonical standard-Gaussian coordinates is
the identity matrix. -/
theorem stdGaussian_coordinate_covariance (i j : ι) :
    cov[fun x : EuclideanSpace ℝ ι => x i,
        fun x : EuclideanSpace ℝ ι => x j;
        stdGaussian (EuclideanSpace ℝ ι)] = if i = j then 1 else 0 := by
  let ei := EuclideanSpace.basisFun ι ℝ i
  let ej := EuclideanSpace.basisFun ι ℝ j
  have hei : (fun x : EuclideanSpace ℝ ι => x i) =
      fun x => inner ℝ ei x := by
    funext x
    exact euclidean_coordinate_eq_basisFun_inner x i
  have hej : (fun x : EuclideanSpace ℝ ι => x j) =
      fun x => inner ℝ ej x := by
    funext x
    exact euclidean_coordinate_eq_basisFun_inner x j
  rw [hei, hej, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  change inner ℝ (EuclideanSpace.basisFun ι ℝ i)
    (EuclideanSpace.basisFun ι ℝ j) = if i = j then 1 else 0
  rw [EuclideanSpace.basisFun_inner]
  simp [EuclideanSpace.basisFun_apply]

/-- Exact second moment of a finite centered spectral sum. -/
theorem centeredSpectralSquares_secondMoment (lam : ι → ℝ) :
    (∫ x, (centeredSpectralSquares lam x) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ ι)) =
      2 * ∑ i, lam i ^ 2 := by
  unfold centeredSpectralSquares
  rw [jointStandardGaussian_weightedCenteredSquares_secondMoment
    (stdGaussian (EuclideanSpace ℝ ι))
    (fun i x => x i)
    stdGaussian_coordinate_measurePreserving
    stdGaussian_coordinate_pair_hasGaussianLaw lam]
  simp [stdGaussian_coordinate_covariance, apply_ite, pow_two]

/-- The centered Gaussian quadratic form has second moment twice the sum of
the squared eigenvalues. -/
theorem centeredMatrixQuadratic_secondMoment_eigenvalues
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∫ x, (centeredMatrixQuadratic A x) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ ι)) =
      2 * ∑ i, hA.eigenvalues i ^ 2 := by
  calc
    (∫ x, (centeredMatrixQuadratic A x) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι)) =
        ∫ x, (centeredSpectralSquares hA.eigenvalues x) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι) :=
      (centeredMatrixQuadratic_identDistrib_eigenvalueSquares hA).sq.integral_eq
    _ = 2 * ∑ i, hA.eigenvalues i ^ 2 :=
      centeredSpectralSquares_secondMoment hA.eigenvalues

/-- For a real symmetric matrix, the trace of its square is the entrywise
sum of squares. -/
theorem hermitian_trace_square_eq_sum_entries_sq
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ∑ j, A i j ^ 2 := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hs : A j i = A i j := by
    simpa using hA.apply i j
  rw [hs, pow_two]

/-- Spectral invariance of the trace of the square. -/
theorem hermitian_trace_square_eq_sum_eigenvalues_sq
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  let U := hA.eigenvectorUnitary
  let D : Matrix ι ι ℝ := diagonal hA.eigenvalues
  have hspec : A = (U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply,
      RCLike.ofReal_real_eq_id] using hA.spectral_theorem
  calc
    (A * A).trace =
        (((U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ)) *
          ((U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ))).trace := by
      rw [hspec]
    _ = ((U : Matrix ι ι ℝ) * D *
          (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) * D *
          star (U : Matrix ι ι ℝ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((U : Matrix ι ι ℝ) * (D * D) *
          star (U : Matrix ι ι ℝ)).trace := by
      rw [Unitary.coe_star_mul_self]
      simp [Matrix.mul_assoc]
    _ = (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ) * (D * D)).trace :=
      Matrix.trace_mul_cycle (U : Matrix ι ι ℝ) (D * D)
        (star (U : Matrix ι ι ℝ))
    _ = (D * D).trace := by
      rw [Unitary.coe_star_mul_self, one_mul]
    _ = ∑ i, hA.eigenvalues i ^ 2 := by
      simp [D, Matrix.trace, pow_two]

/-- The squared eigenvalues and squared entries have the same finite sum for
a real symmetric matrix. -/
theorem hermitian_sum_eigenvalues_sq_eq_sum_entries_sq
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∑ i, hA.eigenvalues i ^ 2) = ∑ i, ∑ j, A i j ^ 2 := by
  rw [← hermitian_trace_square_eq_sum_eigenvalues_sq hA,
    hermitian_trace_square_eq_sum_entries_sq hA]

/-- Entrywise Hilbert--Schmidt form of the exact second-moment identity for a
centered symmetric Gaussian quadratic form. -/
theorem centeredMatrixQuadratic_secondMoment_entries
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∫ x, (centeredMatrixQuadratic A x) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ ι)) =
      2 * ∑ i, ∑ j, A i j ^ 2 := by
  rw [centeredMatrixQuadratic_secondMoment_eigenvalues hA,
    hermitian_sum_eigenvalues_sq_eq_sum_entries_sq hA]

end Hurst
