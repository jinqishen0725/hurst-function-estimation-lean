import Hurst.FiniteGaussianSpectral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Probability.Distributions.Gaussian.Multivariate

#check Matrix.IsHermitian.eigenvectorBasis
#check Matrix.IsHermitian.eigenvalues
#check Matrix.IsHermitian.mulVec_eigenvectorBasis
#check Matrix.IsHermitian.eigenvectorUnitary
#check Matrix.IsHermitian.eigenvectorUnitary_transpose_apply
#check Matrix.IsHermitian.coe_eigenvectorUnitary_apply
#check Matrix.IsHermitian.star_mul_eigenvectorUnitary
#check Matrix.IsHermitian.eq_conjStarAlgAut_diagonal
#check OrthonormalBasis.repr
#check OrthonormalBasis.equiv
#check ProbabilityTheory.stdGaussian_map
#check MeasureTheory.MeasurePreserving.identDistrib
#check ProbabilityTheory.IdentDistrib.comp
#check MeasureTheory.MeasurePreserving.integral_comp
#check Matrix.dotProduct_mulVec
#check Matrix.trace_eq_sum_diagonal
#check Matrix.IsHermitian.trace_eq_sum_eigenvalues
#check Matrix.mulVec
#check EuclideanSpace.basisFun
#check EuclideanSpace.inner_basisFun
#check EuclideanSpace.basisFun_inner
#check LinearIsometryEquiv.measurePreserving

#print axioms Hurst.centeredMatrixQuadratic_identDistrib_eigenvalueSquares
#print axioms Hurst.centeredMatrixQuadratic_secondMoment_entries
