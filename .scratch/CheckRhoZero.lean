import Hurst.FrozenLagSummability
open Set
namespace Hurst
example (h : ℝ) (hh : 0 < h) : firstIncrementLagCorrelation h 0 = 1 := by
  unfold firstIncrementLagCorrelation
  norm_num [Real.zero_rpow (by positivity : 2 * h ≠ 0)]

example (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    secondIncrementLagCorrelation h 0 = 1 := by
  unfold secondIncrementLagCorrelation
  have hz : firstIncrementLagCorrelation h 0 = 1 := by
    unfold firstIncrementLagCorrelation
    norm_num [Real.zero_rpow (by positivity : 2 * h ≠ 0)]
  rw [hz]
  unfold firstIncrementLagCorrelation
  norm_num [Real.zero_rpow (by positivity : 2 * h ≠ 0)]
  have hden : 4 - (2 : ℝ) ^ (2 * h) ≠ 0 := by
    have hp : (2 : ℝ) ^ (2 * h) < (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    norm_num at hp
    linarith
  field_simp
  ring
end Hurst
