import Hurst.GaussianHilbert
import Hurst.HermiteParity
import Hurst.GaussianLogCovariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def gaussianLogLp : GaussianL2 := centeredGaussianLog_memLp_two.toLp centeredGaussianLog

theorem gaussianLogLp_ae : gaussianLogLp =ᵐ[gaussianReal 0 1] centeredGaussianLog :=
  MemLp.coeFn_toLp _

theorem gaussianLog_hermite_coefficient (n : ℕ) :
    ⟪gaussianHermiteUnit n,gaussianLogLp⟫ = (Real.sqrt (n.factorial:ℝ))⁻¹*
      (∫ x,centeredGaussianLog x*(gaussianHermite n).eval x ∂gaussianReal 0 1) := by
  rw [gaussianHermiteUnit,inner_smul_left,conj_trivial,gaussianHermiteLp_inner_function]
  congr 1
  apply integral_congr_ae
  filter_upwards [gaussianLogLp_ae] with x hx
  rw [hx]

theorem gaussianLog_hermite_coefficient_zero : ⟪gaussianHermiteUnit 0,gaussianLogLp⟫=0 := by
  rw [gaussianLog_hermite_coefficient]
  simp only [gaussianHermite_zero,Polynomial.eval_one,mul_one,centeredGaussianLog_mean,mul_zero]

theorem gaussianLog_hermite_coefficient_odd (n : ℕ) (hn : Odd n) :
    ⟪gaussianHermiteUnit n,gaussianLogLp⟫=0 := by
  rw [gaussianLog_hermite_coefficient,
    standardGaussian_even_odd_hermite centeredGaussianLog centeredGaussianLog_even n hn,mul_zero]

theorem gaussianLog_hermite_rank_at_least_two :
    ∀ n : ℕ,n<2 → ⟪gaussianHermiteUnit n,gaussianLogLp⟫=0 := by
  intro n hn
  interval_cases n
  · exact gaussianLog_hermite_coefficient_zero
  · exact gaussianLog_hermite_coefficient_odd 1 (by decide)

theorem gaussianLog_hermite_expansion :
    HasSum (fun n => ⟪gaussianHermiteUnit n,gaussianLogLp⟫ • gaussianHermiteUnit n) gaussianLogLp :=
  gaussianHermite_expansion _

theorem gaussianLog_hermite_parseval :
    HasSum (fun n => ⟪gaussianHermiteUnit n,gaussianLogLp⟫^2) gaussianLogSquareVariance := by
  convert gaussianHermite_parseval gaussianLogLp using 1
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  unfold gaussianLogSquareVariance
  apply integral_congr_ae
  filter_upwards [gaussianLogLp_ae] with x hx
  simp only [hx,Real.inner_apply,pow_two]

end Hurst
