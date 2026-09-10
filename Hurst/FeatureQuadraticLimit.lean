import Hurst.FeatureHermiteTests
import Hurst.GaussianResidualCovariance
import Hurst.TriangularApproximation

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

def gaussianLogQuadraticStatistic {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i,w i*((standardizedFeatureObservation v (a i) x)^2-1)

theorem gaussianLogQuadraticStatistic_memLp_two {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι) :
    MemLp (gaussianLogQuadraticStatistic v w a) 2 (featureGaussian v) := by
  apply memLp_finsetSum
  intro i _
  have hh := (gaussianLaw_polynomial_memLp_two
    (standardizedFeatureObservation_pair v (a i) (a i)).fst (gaussianHermite 2)).const_mul (w i)
  simpa only [gaussianHermite_two,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one] using hh

theorem featureGaussian_log_quadratic_error {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j,∑ i,a j i • v i≠0) (R : ℝ)
    (hrow : ∀ i,∑ j,|featureCorrelation v (a i) (a j)|^4≤R) :
    (∫ x,(gaussianLogStatistic w a x-(∫ y,gaussianLogStatistic w a y ∂featureGaussian v)-
      gaussianLogQuadraticStatistic v w a x)^2 ∂featureGaussian v) ≤
      (gaussianLogSquareVariance-2)*R*∑ i,w i^2 := by
  have he := gaussian_array_rank_second_moment (featureGaussian v)
    (fun i => standardizedFeatureObservation v (a i))
    (fun i => standardizedFeatureObservation_law v (a i) (ha i))
    (fun i j => standardizedFeatureObservation_pair v (a i) (a j)) w gaussianLogResidualLp 4 R
    gaussianLogResidual_rank_four (by simpa only [standardizedFeatureObservation_covariance] using hrow)
  rw [gaussianLogResidual_norm_sq] at he
  apply le_trans (le_of_eq ?_) he
  apply integral_congr_ae
  filter_upwards [gaussianLogStatistic_centered_standardized v w a ha,
    ae_all_iff.mpr (fun i => (standardizedFeatureObservation_law v (a i) (ha i)).quasiMeasurePreserving.ae
      gaussianLogResidualLp_ae)] with x hx hres
  rw [hx,gaussianLogQuadraticStatistic,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hres i]
  unfold gaussianLogResidual
  ring

theorem featureGaussian_log_limit_of_quadratic_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (m : ℕ → ℕ) (v : ∀ n,Fin n → E)
    (w : ∀ n,Fin (m n) → ℝ) (a : ∀ n,Fin (m n) → EuclideanSpace ℝ (Fin n))
    (c R : ℕ → ℝ) (Z : Ω' → ℝ)
    (ha : ∀ᶠ n in atTop,∀ j,∑ i,a n j i • v n i≠0)
    (hr : ∀ᶠ n in atTop,∀ i,∑ j,|featureCorrelation (v n) (a n i) (a n j)|^4≤R n)
    (hW : Tendsto (fun n => (c n)^2*R n*(∑ i,w n i^2)) atTop (𝓝 0))
    (hquad : TendstoInDistribution
      (fun n x => c n*gaussianLogQuadraticStatistic (v n) (w n) (a n) x) atTop Z
      (fun n => featureGaussian (v n)) P') :
    TendstoInDistribution (fun n x => c n*(gaussianLogStatistic (w n) (a n) x-
      (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))) atTop Z
      (fun n => featureGaussian (v n)) P' := by
  let X := fun n x => c n*(gaussianLogStatistic (w n) (a n) x-
      (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))
  let Y := fun n x => c n*gaussianLogQuadraticStatistic (v n) (w n) (a n) x
  have he : ∀ᶠ n in atTop,MemLp (fun x => X n x-Y n x) 2 (featureGaussian (v n)) ∧
      (∫ x,(X n x-Y n x)^2 ∂featureGaussian (v n))≤
      (gaussianLogSquareVariance-2)*((c n)^2*R n*∑ i,w n i^2) := by
    filter_upwards [ha,hr] with n hn hrow
    have hX := ((gaussianLogStatistic_memLp_two (v n) (w n) (a n) hn).sub (memLp_const (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))).const_mul (c n)
    have hY := (gaussianLogQuadraticStatistic_memLp_two (v n) (w n) (a n)).const_mul (c n)
    refine ⟨hX.sub hY,?_⟩
    have hid : (∫ x,(X n x-Y n x)^2 ∂featureGaussian (v n))=
        (c n)^2*(∫ x,(gaussianLogStatistic (w n) (a n) x-(∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n))-
          gaussianLogQuadraticStatistic (v n) (w n) (a n) x)^2 ∂featureGaussian (v n)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall (fun x => by dsimp [X,Y]; ring))
    rw [hid]
    convert mul_le_mul_of_nonneg_left (featureGaussian_log_quadratic_error (v n) (w n) (a n) hn (R n) hrow) (sq_nonneg (c n)) using 1 <;> first | rfl | ring
  apply triangular_L1_distribution_transfer (fun n => featureGaussian (v n)) P' Y X Z hquad
    (fun n => by dsimp [X]; unfold gaussianLogStatistic; fun_prop) (he.mono (fun _ hn => hn.1.integrable (by norm_num)))
  have hz : Tendsto (fun n => (gaussianLogSquareVariance-2)*((c n)^2*R n*∑ i,w n i^2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hW.const_mul (gaussianLogSquareVariance-2)
  have hs : Tendsto (fun n => Real.sqrt ((gaussianLogSquareVariance-2)*((c n)^2*R n*∑ i,w n i^2))) atTop (𝓝 0) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hz using 1 <;> first | rfl | simp only [Real.sqrt_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) _ hs
  filter_upwards [he] with n hn
  exact (integral_abs_le_sqrt_second_moment (featureGaussian (v n)) _ hn.1).trans (Real.sqrt_le_sqrt hn.2)

end Hurst
