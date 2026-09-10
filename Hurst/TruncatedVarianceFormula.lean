import Hurst.FeatureHermiteApproximation
import Hurst.FeatureHermiteTests
import Hurst.GaussianHermiteCovariance
import Hurst.GaussianLogSeries

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

def gaussianLogTruncationCovariance (M : ℕ) (ρ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range M, gaussianLogHermiteCoefficient n ^ 2 * ρ ^ n

theorem gaussianLogTruncationPolynomial_mean (M : ℕ) :
    (∫ x, (hermiteTruncationPolynomial gaussianLogLp M).eval x
      ∂gaussianReal 0 1) = 0 := by
  simp only [hermiteTruncationPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul]
  rw [integral_finsetSum (Finset.range M) (fun n _ =>
    (standardGaussian_polynomial_memLp_two (gaussianHermite n)).integrable
      (by norm_num) |>.const_mul _)]
  apply Finset.sum_eq_zero
  intro n hn
  rw [integral_const_mul]
  by_cases hn0 : n = 0
  · subst n
    rw [gaussianLog_hermite_rank_at_least_two 0 (by omega)]
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [standardGaussian_hermite_mean_succ]
    ring

theorem gaussianLogTruncation_pair_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) (M : ℕ) :
    (∫ ω, (hermiteTruncationPolynomial gaussianLogLp M).eval (X ω) *
      (hermiteTruncationPolynomial gaussianLogLp M).eval (Y ω) ∂P) =
      gaussianLogTruncationCovariance M cov[X, Y; P] := by
  have he : (∫ ω, (hermiteTruncationPolynomial gaussianLogLp M).eval (X ω) *
      (hermiteTruncationPolynomial gaussianLogLp M).eval (Y ω) ∂P) =
      ⟪gaussianPullback P X hX (hermiteTruncation gaussianLogLp M),
        gaussianPullback P Y hY (hermiteTruncation gaussianLogLp M)⟫ := by
    rw [gaussianPullback_inner]
    apply integral_congr_ae
    filter_upwards [hX.quasiMeasurePreserving.ae
        (hermiteTruncation_polynomial_ae gaussianLogLp M),
      hY.quasiMeasurePreserving.ae
        (hermiteTruncation_polynomial_ae gaussianLogLp M)] with ω hx hy
    rw [hx, hy]
  rw [he]
  simp only [hermiteTruncation, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, conj_trivial,
    jointGaussian_hermite_unit_inner P X Y hXY hX hY,
    gaussianLogTruncationCovariance, gaussianLogHermiteCoefficient]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single n]
  · simp
    ring
  · intro m hm hmn
    simp [hmn]
  · simp [hn]

theorem featureGaussian_logTruncation_pair_integral
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a b : EuclideanSpace ℝ ι)
    (ha : ∑ i, a i • v i ≠ 0) (hb : ∑ i, b i • v i ≠ 0) (M : ℕ) :
    (∫ x, (hermiteTruncationPolynomial gaussianLogLp M).eval
        (standardizedFeatureObservation v a x) *
      (hermiteTruncationPolynomial gaussianLogLp M).eval
        (standardizedFeatureObservation v b x) ∂featureGaussian v) =
      gaussianLogTruncationCovariance M (featureCorrelation v a b) := by
  rw [← standardizedFeatureObservation_covariance]
  exact gaussianLogTruncation_pair_integral (featureGaussian v)
    (standardizedFeatureObservation v a) (standardizedFeatureObservation v b)
    (standardizedFeatureObservation_pair v a b)
    (standardizedFeatureObservation_law v a ha)
    (standardizedFeatureObservation_law v b hb) M

theorem featureGaussian_logTruncation_mean
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : EuclideanSpace ℝ ι)
    (ha : ∑ i, a i • v i ≠ 0) (M : ℕ) :
    (∫ x, (hermiteTruncationPolynomial gaussianLogLp M).eval
      (standardizedFeatureObservation v a x) ∂featureGaussian v) = 0 := by
  have hpres := standardizedFeatureObservation_law v a ha
  have hlaw : HasLaw (standardizedFeatureObservation v a) (gaussianReal 0 1)
      (featureGaussian v) := ⟨hpres.measurable.aemeasurable, hpres.map_eq⟩
  change (∫ x, ((fun z => (hermiteTruncationPolynomial gaussianLogLp M).eval z) ∘
    standardizedFeatureObservation v a) x ∂featureGaussian v) = 0
  rw [hlaw.integral_comp
    (standardGaussian_polynomial_memLp_two
      (hermiteTruncationPolynomial gaussianLogLp M)).1,
    gaussianLogTruncationPolynomial_mean]

theorem featureGaussian_logTruncation_second_moment
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) (M : ℕ) :
    (∫ x, gaussianLogTruncationStatistic v w a M x ^ 2 ∂featureGaussian v) =
      ∑ i, ∑ j, w i * w j *
        gaussianLogTruncationCovariance M (featureCorrelation v (a i) (a j)) := by
  let P := hermiteTruncationPolynomial gaussianLogLp M
  have hint (i j : κ) : Integrable (fun x =>
      (w i * P.eval (standardizedFeatureObservation v (a i) x)) *
        (w j * P.eval (standardizedFeatureObservation v (a j) x)))
      (featureGaussian v) := by
    exact ((gaussianLaw_polynomial_memLp_two
      (standardizedFeatureObservation_pair v (a i) (a j)).fst P).const_mul (w i)).integrable_mul
      ((gaussianLaw_polynomial_memLp_two
        (standardizedFeatureObservation_pair v (a i) (a j)).snd P).const_mul (w j))
  simp only [gaussianLogTruncationStatistic, P, pow_two, Finset.sum_mul,
    Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hint i j))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hint j i)]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∫ x,
        w j * (hermiteTruncationPolynomial gaussianLogLp M).eval
          (standardizedFeatureObservation v (a j) x) *
        (w i * (hermiteTruncationPolynomial gaussianLogLp M).eval
          (standardizedFeatureObservation v (a i) x)) ∂featureGaussian v) =
        w j * w i * (∫ x,
          (hermiteTruncationPolynomial gaussianLogLp M).eval
            (standardizedFeatureObservation v (a j) x) *
          (hermiteTruncationPolynomial gaussianLogLp M).eval
            (standardizedFeatureObservation v (a i) x) ∂featureGaussian v) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => by ring)
    _ = _ := by rw [featureGaussian_logTruncation_pair_integral v
      (a j) (a i) (ha j) (ha i) M]

theorem featureGaussian_logTruncationStatistic_mean
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) (M : ℕ) :
    (∫ x, gaussianLogTruncationStatistic v w a M x ∂featureGaussian v) = 0 := by
  simp only [gaussianLogTruncationStatistic]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    ((gaussianLaw_polynomial_memLp_two
      (standardizedFeatureObservation_pair v (a i) (a i)).fst
      (hermiteTruncationPolynomial gaussianLogLp M)).const_mul (w i)).integrable
        (by norm_num))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_const_mul, featureGaussian_logTruncation_mean v (a i) (ha i) M,
    mul_zero]

theorem featureGaussian_logTruncation_variance
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) (M : ℕ) :
    Var[gaussianLogTruncationStatistic v w a M; featureGaussian v] =
      ∑ i, ∑ j, w i * w j *
        gaussianLogTruncationCovariance M (featureCorrelation v (a i) (a j)) := by
  rw [variance_eq_integral
      (gaussianLogTruncationStatistic_memLp_two v w a M).1.aemeasurable,
    featureGaussian_logTruncationStatistic_mean v w a ha M]
  simp only [sub_zero]
  exact featureGaussian_logTruncation_second_moment v w a ha M

end Hurst
