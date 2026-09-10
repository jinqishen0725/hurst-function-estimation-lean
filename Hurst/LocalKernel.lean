import Hurst.BumpPacking
import Hurst.BumpLoss
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Hurst

/-- A fixed smooth compact kernel, positive throughout (-1,1), suitable at both boundaries. -/
def localKernel (x : ℝ) : ℝ := correctedBump (x / 2)

theorem localKernel_smooth : ContDiff ℝ (⊤ : ℕ∞) localKernel :=
  correctedBump_smooth.comp (contDiff_id.div_const 2)

theorem localKernel_nonneg (x : ℝ) : 0 ≤ localKernel x := by
  exact expNegInvGlue.nonneg _

theorem localKernel_pos (x : ℝ) (hx : |x| < 1) : 0 < localKernel x := by
  apply correctedBump_positive
  have he := abs_lt.mp hx
  constructor <;> linarith [he.1, he.2]

theorem localKernel_zero (x : ℝ) (hx : 1 ≤ |x|) : localKernel x = 0 := by
  apply correctedBump_zero
  rcases le_total x 0 with h | h
  · left
    rw [abs_of_nonpos h] at hx
    linarith
  · right
    rw [abs_of_nonneg h] at hx
    linarith

theorem localKernel_compactSupport : HasCompactSupport localKernel := by
  apply HasCompactSupport.intro (K := Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  apply localKernel_zero
  by_contra h
  exact hx (by have he := abs_lt.mp (lt_of_not_ge h); exact ⟨he.1.le, he.2.le⟩)

def kernelMomentFunction (k : ℕ) (x : ℝ) : ℝ := localKernel x * x ^ k

theorem kernelMomentFunction_smooth (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (kernelMomentFunction k) :=
  localKernel_smooth.mul (contDiff_id.pow k)

theorem kernelMomentFunction_compactSupport (k : ℕ) : HasCompactSupport (kernelMomentFunction k) :=
  localKernel_compactSupport.mul_right

theorem kernelMomentFunction_derivative_integrable (k : ℕ) : Integrable (deriv (kernelMomentFunction k)) := by
  have hc := (kernelMomentFunction_smooth k).continuous_deriv (by simp)
  exact hc.integrable_of_hasCompactSupport (kernelMomentFunction_compactSupport k).deriv

theorem kernelMomentFunction_bounded (k : ℕ) : ∃ C ≥ 0, ∀ x : ℝ, |kernelMomentFunction k x| ≤ C := by
  obtain ⟨C, hC⟩ := (kernelMomentFunction_compactSupport k).exists_bound_of_continuousOn
    (kernelMomentFunction_smooth k).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : kernelMomentFunction k x = 0
  · simp only [hx, abs_zero]; exact le_max_right _ _
  · exact (hC x (subset_closure hx)).trans (le_max_left _ _)

def coefficientPolynomial {r : ℕ} (v : Fin (r + 1) → ℝ) : Polynomial ℝ :=
  ∑ k, Polynomial.C (v k) * Polynomial.X ^ k.val

theorem coefficientPolynomial_coeff {r : ℕ} (v : Fin (r + 1) → ℝ) (k : Fin (r + 1)) :
    (coefficientPolynomial v).coeff k.val = v k := by
  classical
  simp only [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]
  simp

theorem coefficientPolynomial_eval {r : ℕ} (v : Fin (r + 1) → ℝ) (x : ℝ) :
    (coefficientPolynomial v).eval x = ∑ k, v k * x ^ k.val := by
  simp [coefficientPolynomial, Polynomial.eval_finsetSum]

theorem coefficientPolynomial_nonzero {r : ℕ} (v : Fin (r + 1) → ℝ) (hv : v ≠ 0) :
    coefficientPolynomial v ≠ 0 := by
  intro h
  apply hv
  funext k
  have he := coefficientPolynomial_coeff v k
  rw [h, Polynomial.coeff_zero] at he
  exact he.symm

theorem polynomial_nonzero_in_interval (P : Polynomial ℝ) (hP : P ≠ 0) (a b : ℝ) (hab : a < b) :
    ∃ x ∈ Ioo a b, P.eval x ≠ 0 := by
  by_contra h
  push Not at h
  have hs : Ioo a b ⊆ {x | P.IsRoot x} := fun x hx => h x hx
  exact hP (P.eq_zero_of_infinite_isRoot ((Set.Ioo_infinite hab).mono hs))

theorem kernel_polynomial_integral_pos {r : ℕ} (v : Fin (r + 1) → ℝ) (hv : v ≠ 0)
    (a b : ℝ) (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    0 < ∫ x in a..b, localKernel x * (∑ k, v k * x ^ k.val) ^ 2 := by
  obtain ⟨x, hx, hpx⟩ := polynomial_nonzero_in_interval (coefficientPolynomial v)
    (coefficientPolynomial_nonzero v hv) a b hab
  apply intervalIntegral.integral_pos hab
  · exact (localKernel_smooth.continuous.mul (by fun_prop)).continuousOn
  · intro y hy
    exact mul_nonneg (localKernel_nonneg y) (sq_nonneg _)
  · refine ⟨x, ⟨hx.1.le, hx.2.le⟩, ?_⟩
    apply mul_pos (localKernel_pos x (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
    apply sq_pos_of_ne_zero
    rwa [coefficientPolynomial_eval] at hpx

end Hurst
