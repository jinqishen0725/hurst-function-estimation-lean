import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
noncomputable section
open Matrix
open scoped RealInnerProductSpace Matrix.Norms.Frobenius
#synth InnerProductSpace ℝ (Matrix (Fin 2) (Fin 2) ℝ)
#check abs_real_inner_le_norm
#check Matrix.frobenius_norm_transpose
#check Matrix.frobenius_norm_conjTranspose
example {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) :
    Matrix.trace (A * B) = ⟪A, B.transpose⟫_ℝ := by
  simp [Matrix.trace, Matrix.mul_apply, real_inner_comm]
