import Hurst.LinearScale
import Hurst.ActualPilot
import Hurst.AverageAlgebra

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

def q2LinearScale (r n m : ℕ) (δ : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  linearScaleCombination (Real.log n)
    (gaussianLogStatistic (averagedLocalWeights r n 4 m δ) (commonStrideCoefficients n 1 4 (by norm_num)))
    (gaussianLogStatistic (averagedLocalWeights r n 4 m δ) (commonStrideCoefficients n 2 4 (by norm_num)))

theorem q2LinearScale_eq_average (r n m : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    q2LinearScale r n m δ x =
      (∑ j : Fin m, (gaussianLogStatistic (localPolynomialWeights r n 4 δ (grid m j.val))
        (commonStrideCoefficients n 1 4 (by norm_num)) x + 2*Real.log n*q2Pilot r n δ (grid m j.val) x))/(m:ℝ) := by
  have hlocal : ∀ j : Fin m,
      gaussianLogStatistic (localPolynomialWeights r n 4 δ (grid m j.val)) (commonStrideCoefficients n 1 4 (by norm_num)) x+
        2*Real.log n*q2Pilot r n δ (grid m j.val) x =
      linearScaleCombination (Real.log n)
        (gaussianLogStatistic (localPolynomialWeights r n 4 δ (grid m j.val)) (commonStrideCoefficients n 1 4 (by norm_num)))
        (gaussianLogStatistic (localPolynomialWeights r n 4 δ (grid m j.val)) (commonStrideCoefficients n 2 4 (by norm_num))) x := by
    intro j
    exact (congrFun (linearScaleCombination_pilot_identity (Real.log n) _ _) x).symm
  simp_rw [hlocal]
  unfold q2LinearScale linearScaleCombination
  rw [← averaged_gaussianLogStatistic, ← averaged_gaussianLogStatistic,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring


def q2LogScaleEstimator (a b : ℝ) (r n m : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  q2LinearScale r n m δ x -
    (∑ j : Fin m, q2LogCorrection (clip a b (q2Pilot r n δ (grid m j.val) x)))/(m:ℝ) - gaussianLogSquareMean

theorem q2LogScaleEstimator_decomposition (a b : ℝ) (r n m : ℕ) (hm : 0 < m) (δ : ℝ)
    (f : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    q2LogScaleEstimator a b r n m δ x =
      (q2LinearScale r n m δ x - (∑ j : Fin m, (q2LogCorrection (f (grid m j.val))+gaussianLogSquareMean))/(m:ℝ)) -
      (∑ j : Fin m, (q2LogCorrection (clip a b (q2Pilot r n δ (grid m j.val) x))-q2LogCorrection (f (grid m j.val))))/(m:ℝ) := by
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold q2LogScaleEstimator
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

end Hurst
