import Hurst.FiniteGaussianSpectral
import Mathlib.Probability.Distributions.Gaussian.Multivariate
noncomputable section
open Matrix
open scoped RealInnerProductSpace
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.IsHermitian) (w : ι → ℝ)
    (x : EuclideanSpace ℝ ι) :
    dotProduct (WithLp.ofLp x) ((S * diagonal w * S) *ᵥ WithLp.ofLp x) =
      ∑ i, w i * ((toEuclideanCLM (𝕜 := ℝ) S x) i)^2 := by
  rw [Matrix.mul_assoc]
  rw [← Matrix.mulVec_mulVec (WithLp.ofLp x) S (diagonal w * S)]
  rw [← Matrix.mulVec_mulVec (WithLp.ofLp x) (diagonal w) S]
  rw [Matrix.dotProduct_mulVec]
  rw [show (WithLp.ofLp x ᵥ* S) = S *ᵥ WithLp.ofLp x by
    rw [← Matrix.mulVec_transpose]
    rw [show Sᵀ = S by simpa [Matrix.IsHermitian] using hS]]
  simp only [dotProduct, Matrix.mulVec_diagonal,
    Matrix.ofLp_toEuclideanCLM]
  congr 1
  funext i
  ring
