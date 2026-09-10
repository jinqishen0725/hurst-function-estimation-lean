import Hurst.FeatureConditionalCLT

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem featureGaussian_log_CLT_general_indices
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℕ → Type*) [∀ n,Fintype (κ n)] (v : ∀ n,Fin n → E)
    (w : ∀ n,κ n → ℝ) (a : ∀ n,κ n → EuclideanSpace ℝ (Fin n))
    (c R : ℕ → ℝ) (C : ℝ)
    (ha : ∀ᶠ n in atTop,∀ j,∑ i,a n j i • v n i≠0)
    (hr : ∀ᶠ n in atTop,∀ i,∑ j,featureCorrelation (v n) (a n i) (a n j)^2≤R n)
    (hW : ∀ᶠ n in atTop,(c n)^2*R n*(∑ i,w n i^2)≤C)
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hpoly : ∀ k,TendstoInDistribution
      (fun n x => c n*gaussianLogTruncationStatistic (v n) (w n) (a n) k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z) (fun n => featureGaussian (v n)) (gaussianReal 0 1)) :
    TendstoInDistribution (fun n x => c n*(gaussianLogStatistic (w n) (a n) x-
      (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))) atTop
      (fun z : ℝ => Real.sqrt V*z) (fun n => featureGaussian (v n)) (gaussianReal 0 1) := by
  apply triangular_L2_approximation (fun n => featureGaussian (v n)) (gaussianReal 0 1)
    _ _ _ _ (fun n => by unfold gaussianLogStatistic; fun_prop) hpoly
    (gaussian_variance_distribution_tendsto Vk V hV) (fun k => C*‖hermiteTail gaussianLogLp k‖^2)
    (by simpa only [mul_zero] using (hermiteTail_norm_sq_tendsto gaussianLogLp).const_mul C)
  intro k
  filter_upwards [ha,hr,hW] with n hn hrow hweight
  have hX := ((gaussianLogStatistic_memLp_two (v n) (w n) (a n) hn).sub (memLp_const
    (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))).const_mul (c n)
  have hY := (gaussianLogTruncationStatistic_memLp_two (v n) (w n) (a n) k).const_mul (c n)
  refine ⟨hX.sub hY,?_⟩
  have hid : (∫ x,(c n*(gaussianLogStatistic (w n) (a n) x-
      (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n)))-
      c n*gaussianLogTruncationStatistic (v n) (w n) (a n) k x)^2 ∂featureGaussian (v n)) =
    (c n)^2*(∫ x,(gaussianLogStatistic (w n) (a n) x-
      (∫ y,gaussianLogStatistic (w n) (a n) y ∂featureGaussian (v n))-
      gaussianLogTruncationStatistic (v n) (w n) (a n) k x)^2 ∂featureGaussian (v n)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun _ => by ring))
  rw [hid]
  calc
    _ ≤ (c n)^2*(‖hermiteTail gaussianLogLp k‖^2*R n*∑ i,w n i^2) :=
      mul_le_mul_of_nonneg_left (featureGaussian_log_truncation_error (v n) (w n) (a n) hn (R n) hrow k) (sq_nonneg _)
    _ = ‖hermiteTail gaussianLogLp k‖^2*((c n)^2*R n*∑ i,w n i^2) := by ring
    _ ≤ ‖hermiteTail gaussianLogLp k‖^2*C := mul_le_mul_of_nonneg_left hweight (sq_nonneg _)
    _ = _ := by ring

end Hurst
