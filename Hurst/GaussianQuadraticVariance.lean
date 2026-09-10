import Hurst.GaussianLogRank
import Hurst.GaussianPairLaw
import Hurst.JointHermite
import Hurst.GaussianPolynomialLaw

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
namespace Hurst

theorem jointStandardGaussian_centeredSquare_integral
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y : Omega → ℝ)
    (hXY : HasGaussianLaw (fun x => (X x, Y x)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) :
    (∫ x, ((X x) ^ 2 - 1) * ((Y x) ^ 2 - 1) ∂P) =
      2 * cov[X, Y; P] ^ 2 := by
  have hXlaw : HasLaw X (gaussianReal 0 1) P :=
    ⟨hX.measurable.aemeasurable, hX.map_eq⟩
  have hYlaw : HasLaw Y (gaussianReal 0 1) P :=
    ⟨hY.measurable.aemeasurable, hY.map_eq⟩
  have hX0 : (∫ x, X x ∂P) = 0 := by
    rw [hXlaw.integral_eq, integral_id_gaussianReal]
  have hY0 : (∫ x, Y x ∂P) = 0 := by
    rw [hYlaw.integral_eq, integral_id_gaussianReal]
  have hX1 : Var[X; P] = 1 := by
    rw [hXlaw.variance_eq, variance_id_gaussianReal]
    norm_num
  have hY1 : Var[Y; P] = 1 := by
    rw [hYlaw.variance_eq, variance_id_gaussianReal]
    norm_num
  have hHermite := joint_standardGaussian_hermite P X Y hXY
    hX0 hY0 hX1 hY1 2 2
  norm_num [gaussianHermite_two, Nat.factorial] at hHermite ⊢
  exact hHermite

/-- Exact `L²` identity for a finite weighted sum of centered squares of a
jointly Gaussian standard array.  This is the probabilistic form of the
Hilbert--Schmidt norm identity used for second-chaos spectral tails. -/
theorem jointStandardGaussian_weightedCenteredSquares_secondMoment
    {ι Omega : Type*} [Fintype ι] [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ι → Omega → ℝ)
    (hX : ∀ i, MeasurePreserving (X i) P (gaussianReal 0 1))
    (hpair : ∀ i j, HasGaussianLaw (fun x => (X i x, X j x)) P)
    (w : ι → ℝ) :
    (∫ x, (∑ i, w i * ((X i x) ^ 2 - 1)) ^ 2 ∂P) =
      2 * ∑ i, ∑ j, w i * w j * cov[X i, X j; P] ^ 2 := by
  have hcenter (i : ι) : MemLp (fun x => (X i x) ^ 2 - 1) 2 P := by
    have hmem := gaussianLaw_polynomial_memLp_two (hpair i i).fst
      (gaussianHermite 2)
    simpa only [gaussianHermite_two, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] using hmem
  have hterm (i j : ι) : Integrable (fun x =>
      (w i * ((X i x) ^ 2 - 1)) * (w j * ((X j x) ^ 2 - 1))) P :=
    ((hcenter i).const_mul (w i)).integrable_mul
      ((hcenter j).const_mul (w j))
  have hexpand : (fun x => (∑ i, w i * ((X i x) ^ 2 - 1)) ^ 2) =
      fun x => ∑ i, ∑ j,
        (w i * ((X i x) ^ 2 - 1)) * (w j * ((X j x) ^ 2 - 1)) := by
    funext x
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hexpand]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hterm i j))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hterm i j)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∫ x, w i * ((X i x) ^ 2 - 1) *
        (w j * ((X j x) ^ 2 - 1)) ∂P) =
        w i * w j * (∫ x, ((X i x) ^ 2 - 1) *
          ((X j x) ^ 2 - 1) ∂P) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = w i * w j * (2 * cov[X i, X j; P] ^ 2) := by
      rw [jointStandardGaussian_centeredSquare_integral P
        (X i) (X j) (hpair i j) (hX i) (hX j)]
    _ = 2 * (w i * w j * cov[X i, X j; P] ^ 2) := by ring

end Hurst
