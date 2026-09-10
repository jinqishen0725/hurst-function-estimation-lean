import Hurst.ActiveWeightProfile
import Hurst.TruncatedVarianceFormula

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem activeBSPolynomial_mean_zero
    (r n q : ℕ) (δ t : ℝ) (P : Polynomial ℝ)
    (hP : (∫ z : ℝ, P.eval z ∂gaussianReal 0 1) = 0)
    (j : Fin (localWeightActiveSet n q δ t).card) :
    (∫ z : ℝ, (activeBSPolynomial r n q δ t P j).eval z
      ∂gaussianReal 0 1) = 0 := by
  unfold activeBSPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [integral_const_mul, hP, mul_zero]

theorem activeBSPolynomial_hermite_orthogonal
    (r n q m : ℕ) (δ t : ℝ) (P : Polynomial ℝ)
    (hP : ∀ k, k < m →
      (∫ z : ℝ, P.eval z * (gaussianHermite k).eval z
        ∂gaussianReal 0 1) = 0)
    (j : Fin (localWeightActiveSet n q δ t).card)
    (k : ℕ) (hk : k < m) :
    (∫ z : ℝ, (activeBSPolynomial r n q δ t P j).eval z *
      (gaussianHermite k).eval z ∂gaussianReal 0 1) = 0 := by
  unfold activeBSPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun z : ℝ =>
      (Real.sqrt (↑(localWeightActiveSet n q δ t).card / (↑n * δ)) *
          (↑n * δ * localPolynomialWeights r n q δ t
            (localWeightActiveIndex n q δ t j)) * P.eval z) *
        (gaussianHermite k).eval z) =
      fun z : ℝ =>
        (Real.sqrt (↑(localWeightActiveSet n q δ t).card / (↑n * δ)) *
          (↑n * δ * localPolynomialWeights r n q δ t
            (localWeightActiveIndex n q δ t j))) *
        (P.eval z * (gaussianHermite k).eval z) by
      funext z; ring,
    integral_const_mul, hP k hk, mul_zero]

theorem gaussianLogTruncationPolynomial_hermite_rank_two
    (M : ℕ) (k : ℕ) (hk : k < 2) :
    (∫ z : ℝ, (hermiteTruncationPolynomial gaussianLogLp M).eval z *
      (gaussianHermite k).eval z ∂gaussianReal 0 1) = 0 := by
  have hunit :
      ⟪gaussianHermiteUnit k, hermiteTruncation gaussianLogLp M⟫ = 0 := by
    rw [hermiteTruncation_coefficient]
    split_ifs
    · exact gaussianLog_hermite_rank_at_least_two k hk
    · rfl
  have hsqrt : (Real.sqrt (k.factorial : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos k))).ne'
  have hraw :
      ⟪gaussianHermiteLp k, hermiteTruncation gaussianLogLp M⟫ = 0 := by
    rw [gaussianHermiteUnit, inner_smul_left, conj_trivial] at hunit
    exact (mul_eq_zero.mp hunit).resolve_left hsqrt
  calc
    (∫ z : ℝ, (hermiteTruncationPolynomial gaussianLogLp M).eval z *
        (gaussianHermite k).eval z ∂gaussianReal 0 1) =
      ∫ z : ℝ, (hermiteTruncation gaussianLogLp M) z *
        (gaussianHermite k).eval z ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [hermiteTruncation_polynomial_ae gaussianLogLp M] with z hz
      rw [hz]
    _ = ⟪gaussianHermiteLp k, hermiteTruncation gaussianLogLp M⟫ :=
      (gaussianHermiteLp_inner_function k (hermiteTruncation gaussianLogLp M)).symm
    _ = 0 := hraw

theorem activeGaussianLogBSPolynomial_mean_zero
    (r n q M : ℕ) (δ t : ℝ)
    (j : Fin (localWeightActiveSet n q δ t).card) :
    (∫ z : ℝ,
      (activeBSPolynomial r n q δ t
        (hermiteTruncationPolynomial gaussianLogLp M) j).eval z
      ∂gaussianReal 0 1) = 0 :=
  activeBSPolynomial_mean_zero r n q δ t _
    (gaussianLogTruncationPolynomial_mean M) j

theorem activeGaussianLogBSPolynomial_hermite_rank_two
    (r n q M : ℕ) (δ t : ℝ)
    (j : Fin (localWeightActiveSet n q δ t).card)
    (k : ℕ) (hk : k < 2) :
    (∫ z : ℝ,
      (activeBSPolynomial r n q δ t
        (hermiteTruncationPolynomial gaussianLogLp M) j).eval z *
      (gaussianHermite k).eval z ∂gaussianReal 0 1) = 0 :=
  activeBSPolynomial_hermite_orthogonal r n q 2 δ t _
    (gaussianLogTruncationPolynomial_hermite_rank_two M) j k hk

/-- The active B&S normalization is exactly the original local-statistic
normalization, before centering/variance arguments. -/
theorem activeBSPolynomial_normalized_sum
    (r n q : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (P : Polynomial ℝ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (X : Fin (localWeightActiveSet n q δ t).card → ℝ) :
    (Real.sqrt ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
        ∑ j, (activeBSPolynomial r n q δ t P j).eval (X j) =
      Real.sqrt ((n : ℝ) * δ) *
        ∑ j, localPolynomialWeights r n q δ t
          (localWeightActiveIndex n q δ t j) * P.eval (X j) := by
  let m : ℝ := ((localWeightActiveSet n q δ t).card : ℝ)
  let S : ℝ := (n : ℝ) * δ
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast hcard
  have hS : 0 < S := by dsimp only [S]; positivity
  have hfactor : (Real.sqrt m)⁻¹ * (Real.sqrt (m / S) * S) = Real.sqrt S := by
    rw [Real.sqrt_div hm.le]
    have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
    have hsS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
    field_simp [hsm.ne', hsS.ne']
    nlinarith [Real.sq_sqrt hS.le]
  change (Real.sqrt m)⁻¹ * ∑ j,
      (activeBSPolynomial r n q δ t P j).eval (X j) =
    Real.sqrt S * ∑ j,
      localPolynomialWeights r n q δ t
        (localWeightActiveIndex n q δ t j) * P.eval (X j)
  simp only [activeBSPolynomial, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (Real.sqrt m)⁻¹ *
      ((Real.sqrt (m / S) * (S *
        localPolynomialWeights r n q δ t
          (localWeightActiveIndex n q δ t j))) * P.eval (X j)) =
    Real.sqrt S *
      (localPolynomialWeights r n q δ t
        (localWeightActiveIndex n q δ t j) * P.eval (X j))
  calc
    (Real.sqrt m)⁻¹ *
        ((Real.sqrt (m / S) * (S *
          localPolynomialWeights r n q δ t
            (localWeightActiveIndex n q δ t j))) * P.eval (X j)) =
      ((Real.sqrt m)⁻¹ * (Real.sqrt (m / S) * S)) *
        localPolynomialWeights r n q δ t
          (localWeightActiveIndex n q δ t j) * P.eval (X j) := by ring
    _ = Real.sqrt S *
        localPolynomialWeights r n q δ t
          (localWeightActiveIndex n q δ t j) * P.eval (X j) := by rw [hfactor]
    _ = Real.sqrt S *
        (localPolynomialWeights r n q δ t
          (localWeightActiveIndex n q δ t j) * P.eval (X j)) := by ring

end Hurst
