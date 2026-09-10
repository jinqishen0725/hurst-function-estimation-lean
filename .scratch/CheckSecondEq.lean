import Hurst.SecondGridLogVariance
import Hurst.StrideLogVariance
namespace Hurst
example (n : ℕ) : gridStrideSecondCoefficients n 1 = gridSecondCoefficients n := by
  funext i
  unfold gridStrideSecondCoefficients gridSecondCoefficients
  congr 2 <;> apply Fin.ext <;> rfl

example (n : ℕ) (H : Fin n → Set.Ioo (0 : ℝ) 1) :
    gridStrideSecondActual n 1 H = gridSecondActual n H := by
  funext i
  unfold gridStrideSecondActual gridSecondActual
  congr 2 <;> try {apply Fin.ext <;> rfl}
  · norm_num
end Hurst
