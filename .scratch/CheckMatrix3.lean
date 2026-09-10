import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
open scoped Matrix.Norms.Frobenius
#check LinearMap.continuous_of_finiteDimensional
#check LinearMap.continuous_of_finiteDimensional_dom
#check Matrix.traceLinearMap
#check Continuous.trace
#check continuous_pow
#check Filter.Tendsto.pow
#synth FiniteDimensional ℝ (Matrix (Fin 2) (Fin 2) ℝ)
