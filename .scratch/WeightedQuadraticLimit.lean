import Hurst.FeatureQuadraticLimit
import Hurst.WeightedHermiteMoment

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem featureGaussian_log_quadratic_weighted_error {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j,∑ i,a j i • v i≠0) :
    (∫ x,(gaussianLogStatistic w a x-(∫ y,gaussianLogStatistic w a y ∂featureGaussian v)-
      gaussianLogQuadraticStatistic v w a x)^2 ∂featureGaussian v) ≤
      (gaussianLogSquareVariance-2)*(∑ i,∑ j,|w i| *|w j| *|featureCorrelation v (a i) (a j)|^4) := by
  have he := gaussian_array_rank_double_moment (featureGaussian v)
    (fun i => standardizedFeatureObservation v (a i))
    (fun i => standardizedFeatureObservation_law v (a i) (ha i))
    (fun i j => standardizedFeatureObservation_pair v (a i) (a j)) w gaussianLogResidualLp 4 gaussianLogResidual_rank_four
  simp only [gaussianLogResidual_norm_sq,standardizedFeatureObservation_covariance] at he
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

theorem featureGaussian_log_limit_of_quadratic_weighted_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (κ : ℕ → Type*) [∀ n,Fintype (κ n)] (v : ∀ n,Fin n → E)
    (w : ∀ n,κ n → ℝ) (a : ∀ n,κ n → EuclideanSpace ℝ (Fin n))
    (c : ℕ → ℝ) (Z : Ω' → ℝ)
    (ha : ∀ᶠ n in atTop,∀ j,∑ i,a n j i • v n i≠0)
    (hW : Tendsto (fun n => (c n)^2*(∑ i,∑ j,|w n i| *|w n j| *|featureCorrelation (v n) (a n i) (a n j)|^4)) atTop (𝓝 0))
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
      (gaussianLogSquareVariance-2)*((c n)^2*(∑ i,∑ j,|w n i| *|w n j| *|featureCorrelation (v n) (a n i) (a n j)|^4)) := by
    filter_upwards [ha] with n hn
    have hX := ((gaussianLogStatistic_memLp_two (v n) (w n) (a n) hn).sub (memLp_const (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))).const_mul (c n)
    have hY := (gaussianLogQuadraticStatistic_memLp_two (v n) (w n) (a n)).const_mul (c n)
    refine ⟨hX.sub hY,?_⟩
    have hid : (∫ x,(X n x-Y n x)^2 ∂featureGaussian (v n))=
        (c n)^2*(∫ x,(gaussianLogStatistic (w n) (a n) x-(∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n))-
          gaussianLogQuadraticStatistic (v n) (w n) (a n) x)^2 ∂featureGaussian (v n)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall (fun x => by dsimp [X,Y]; ring))
    rw [hid]
    convert mul_le_mul_of_nonneg_left (featureGaussian_log_quadratic_weighted_error (v n) (w n) (a n) hn) (sq_nonneg (c n)) using 1 <;> first | rfl | ring
  apply triangular_L1_distribution_transfer (fun n => featureGaussian (v n)) P' Y X Z hquad
    (fun n => by dsimp [X]; unfold gaussianLogStatistic; fun_prop) (he.mono (fun _ hn => hn.1.integrable (by norm_num)))
  have hz : Tendsto (fun n => (gaussianLogSquareVariance-2)*((c n)^2*(∑ i,∑ j,|w n i| *|w n j| *|featureCorrelation (v n) (a n i) (a n j)|^4))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hW.const_mul (gaussianLogSquareVariance-2)
  have hs : Tendsto (fun n => Real.sqrt ((gaussianLogSquareVariance-2)*((c n)^2*(∑ i,∑ j,|w n i| *|w n j| *|featureCorrelation (v n) (a n i) (a n j)|^4)))) atTop (𝓝 0) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hz using 1 <;> first | rfl | simp only [Real.sqrt_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) _ hs
  filter_upwards [he] with n hn
  exact (integral_abs_le_sqrt_second_moment (featureGaussian (v n)) _ hn.1).trans (Real.sqrt_le_sqrt hn.2)

end Hurst
