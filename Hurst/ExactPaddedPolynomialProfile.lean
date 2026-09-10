import Hurst.ExactPaddedHitLaw
import Hurst.ActiveWeightProfile
import Hurst.ActiveBSPolynomialConditions

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace Hurst

def exactPaddedPolynomialRow
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (s : ℕ → ℕ) (P : Polynomial ℝ) (N : ℕ) (i : Fin N) :
    Polynomial ℝ := Polynomial.C (exactPaddedCoefficientRow m c g s N i) * P

def scalarPolynomialProfile (g : ℝ → ℝ) (P : Polynomial ℝ)
    (τ z : ℝ) : ℝ := g τ * P.eval z

theorem exactPaddedPolynomialRow_mean_zero
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (s : ℕ → ℕ) (P : Polynomial ℝ)
    (hP : ∫ z : ℝ, P.eval z ∂gaussianReal 0 1 = 0)
    (N : ℕ) (i : Fin N) :
    ∫ z : ℝ, (exactPaddedPolynomialRow m c g s P N i).eval z
      ∂gaussianReal 0 1 = 0 := by
  simp only [exactPaddedPolynomialRow, Polynomial.eval_mul, Polynomial.eval_C]
  rw [integral_const_mul, hP, mul_zero]

theorem exactPaddedPolynomialRow_hermite_orthogonal
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (s : ℕ → ℕ) (P : Polynomial ℝ) (rank : ℕ)
    (hP : ∀ k, k < rank →
      ∫ z : ℝ, P.eval z * (gaussianHermite k).eval z
        ∂gaussianReal 0 1 = 0)
    (N : ℕ) (i : Fin N) (k : ℕ) (hk : k < rank) :
    ∫ z : ℝ, (exactPaddedPolynomialRow m c g s P N i).eval z *
      (gaussianHermite k).eval z ∂gaussianReal 0 1 = 0 := by
  simp only [exactPaddedPolynomialRow, Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun z : ℝ =>
      exactPaddedCoefficientRow m c g s N i * P.eval z *
        (gaussianHermite k).eval z) =
      fun z : ℝ => exactPaddedCoefficientRow m c g s N i *
        (P.eval z * (gaussianHermite k).eval z) by funext z; ring,
    integral_const_mul, hP k hk, mul_zero]

theorem scalarPolynomialProfile_memLp
    (g : ℝ → ℝ) (P : Polynomial ℝ) (τ : ℝ) :
    MemLp (scalarPolynomialProfile g P τ) 2 (gaussianReal 0 1) := by
  exact (standardGaussian_polynomial_memLp_two P).const_mul (g τ)

theorem scalarPolynomialProfile_centered
    (g : ℝ → ℝ) (P : Polynomial ℝ)
    (hP : ∫ z : ℝ, P.eval z ∂gaussianReal 0 1 = 0) (τ : ℝ) :
    ∫ z : ℝ, scalarPolynomialProfile g P τ z ∂gaussianReal 0 1 = 0 := by
  rw [show scalarPolynomialProfile g P τ = fun z => g τ * P.eval z by rfl,
    integral_const_mul, hP, mul_zero]

/-- A scalar coefficient profile uniformly continuous on the line induces
the Gaussian-L2 continuous polynomial profile required by B&S. -/
theorem scalarPolynomialProfile_L2_uniformContinuous
    (g : ℝ → ℝ) (P : Polynomial ℝ) (hg : UniformContinuous g) :
    ∀ ε > 0, ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1, |s - t| < η →
        ∫ z : ℝ, (scalarPolynomialProfile g P s z -
          scalarPolynomialProfile g P t z) ^ 2
          ∂gaussianReal 0 1 ≤ ε := by
  let J : ℝ := ∫ z : ℝ, (P.eval z) ^ 2 ∂gaussianReal 0 1
  have hJ : 0 ≤ J := integral_nonneg fun _ => sq_nonneg _
  have hJp : 0 < J + 1 := by linarith
  intro ε hε
  let κ := Real.sqrt (ε / (J + 1))
  have hκ : 0 < κ := Real.sqrt_pos.mpr (div_pos hε hJp)
  obtain ⟨η, hη, hclose⟩ := Metric.uniformContinuous_iff.mp hg κ hκ
  refine ⟨η, hη, ?_⟩
  intro s _ t _ hst
  have hd : |g s - g t| < κ := by
    simpa only [Real.dist_eq] using hclose (by simpa only [Real.dist_eq] using hst)
  have hsq : (g s - g t) ^ 2 ≤ ε / (J + 1) := by
    calc
      (g s - g t) ^ 2 = |g s - g t| ^ 2 := by rw [sq_abs]
      _ ≤ κ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd.le 2
      _ = ε / (J + 1) := Real.sq_sqrt (div_nonneg hε.le hJp.le)
  have hint : (∫ z : ℝ, (scalarPolynomialProfile g P s z -
      scalarPolynomialProfile g P t z) ^ 2 ∂gaussianReal 0 1) =
      (g s - g t) ^ 2 * J := by
    rw [show (fun z : ℝ => (scalarPolynomialProfile g P s z -
        scalarPolynomialProfile g P t z) ^ 2) =
      fun z : ℝ => (g s - g t) ^ 2 * (P.eval z) ^ 2 by
        funext z; simp only [scalarPolynomialProfile]; ring,
      integral_const_mul]
  rw [hint]
  calc
    (g s - g t) ^ 2 * J ≤ (ε / (J + 1)) * J :=
      mul_le_mul_of_nonneg_right hsq hJ
    _ ≤ ε := by
      apply le_of_lt
      rw [div_mul_eq_mul_div, div_lt_iff₀ hJp]
      nlinarith

/-- Scalar uniform profile convergence upgrades to the Gaussian-L2 profile
condition for a fixed polynomial. -/
theorem exactPaddedPolynomialRow_L2_uniform_tendsto
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (s : ℕ → ℕ) (P : Polynomial ℝ)
    (hc : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : Fin N,
      |exactPaddedCoefficientRow m c g s N i -
        g (((i.val : ℝ) + 1) / N)| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : Fin N,
      ∫ z : ℝ, ((exactPaddedPolynomialRow m c g s P N i).eval z -
        scalarPolynomialProfile g P (((i.val : ℝ) + 1) / N) z) ^ 2
        ∂gaussianReal 0 1 ≤ ε := by
  let J : ℝ := ∫ z : ℝ, (P.eval z) ^ 2 ∂gaussianReal 0 1
  have hJ : 0 ≤ J := integral_nonneg fun _ => sq_nonneg _
  have hJp : 0 < J + 1 := by linarith
  intro ε hε
  let η := Real.sqrt (ε / (J + 1))
  have hη : 0 < η := Real.sqrt_pos.mpr (div_pos hε hJp)
  filter_upwards [hc η hη] with N hN
  intro i
  let A := exactPaddedCoefficientRow m c g s N i
  let B := g (((i.val : ℝ) + 1) / N)
  have hd : |A - B| ≤ η := by simpa only [A, B] using hN i
  have hsq : (A - B) ^ 2 ≤ ε / (J + 1) := by
    calc
      (A - B) ^ 2 = |A - B| ^ 2 := by rw [sq_abs]
      _ ≤ η ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
      _ = ε / (J + 1) := Real.sq_sqrt (div_nonneg hε.le hJp.le)
  have hint : (∫ z : ℝ,
      ((exactPaddedPolynomialRow m c g s P N i).eval z -
        scalarPolynomialProfile g P (((i.val : ℝ) + 1) / N) z) ^ 2
        ∂gaussianReal 0 1) = (A - B) ^ 2 * J := by
    rw [show (fun z : ℝ =>
        ((exactPaddedPolynomialRow m c g s P N i).eval z -
          scalarPolynomialProfile g P (((i.val : ℝ) + 1) / N) z) ^ 2) =
      fun z : ℝ => (A - B) ^ 2 * (P.eval z) ^ 2 by
        funext z
        simp only [exactPaddedPolynomialRow, Polynomial.eval_mul,
          Polynomial.eval_C, scalarPolynomialProfile, A, B]
        ring,
      integral_const_mul]
  rw [hint]
  calc
    (A - B) ^ 2 * J ≤ (ε / (J + 1)) * J :=
      mul_le_mul_of_nonneg_right hsq hJ
    _ ≤ ε := by
      apply le_of_lt
      rw [div_mul_eq_mul_div, div_lt_iff₀ hJp]
      nlinarith

theorem exactPaddedPolynomialRow_sum_eq_truncationStatistic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1)
    (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ) (s : ℕ → ℕ)
    (N K : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    (∑ i : Fin N, (exactPaddedPolynomialRow m c g s
      (hermiteTruncationPolynomial gaussianLogLp K) N i).eval
        (standardizedFeatureObservation (exactPaddedFeatureRow m u s N)
          (EuclideanSpace.basisFun (Fin N) ℝ i) x)) =
      gaussianLogTruncationStatistic (exactPaddedFeatureRow m u s N)
        (exactPaddedCoefficientRow m c g s N)
        (fun i => EuclideanSpace.basisFun (Fin N) ℝ i) K x := by
  rw [gaussianLogTruncationStatistic_basis_normalized
    (exactPaddedFeatureRow m u s N)
    (exactPaddedFeatureRow_norm m u hu s N)]
  apply Finset.sum_congr rfl
  intro i _
  rw [standardizedFeatureObservation_basis_normalized
    (exactPaddedFeatureRow m u s N)
    (exactPaddedFeatureRow_norm m u hu s N)]
  simp [exactPaddedPolynomialRow]

end Hurst
