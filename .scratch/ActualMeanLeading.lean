import Hurst.ActualMeanResidual
import Hurst.MeanLimitTransfer
import Hurst.GridBiasRemainderLimit

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_second_log_mean_leading (p a b M : ℝ) (r : ℕ)
    (hp : 2≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop)
    (hNk : Tendsto (fun n : ℕ => (n:ℝ)*(δ n)^(r+1)) atTop atTop) :
    Tendsto (fun n : ℕ => (secondGridLogExpectation r n (δ n) t (midpointSampleHurst f hf.1 n)-
      (-2*Real.log n*f t+q2LogCorrection (f t)+gaussianLogSquareMean))/(Real.log n*(δ n)^(r+1)))
      atTop (𝓝 (-2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))) := by
  have hcomp : ContDiffOn ℝ (r+1) (q2LogCorrection ∘ f) (Ioo (0:ℝ) 1) :=
    (q2LogCorrection_smooth.of_le (by exact_mod_cast le_top)).comp hfc hf.1
  have hbias := localCalibrationBias_leading_tendsto r 2 f q2LogCorrection gaussianLogSquareMean
    hfc hcomp t ht δ hδpos hδ hN
  have herror : Tendsto (fun n : ℕ => gridCovarianceError (1/2) 1 n/(Real.log n*(δ n)^(r+1))) atTop (𝓝 0) := by
    apply gridCovarianceError_scaled_tendsto (1/2) 1 (r+1) δ hδpos hNk
    convert hNk using 1 <;> norm_num
  obtain ⟨N₀,hN₀,C,hC,hres⟩ := hurstHolder_second_log_expectation_residual p a b M r hp ha hb hab hM
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine scalar_scaled_approximation_tendsto _ _ _ _ _ C ?_ hbias herror ?_
  · filter_upwards [hδpos,hlog.eventually_gt_atTop 0] with n hn hln
    positivity
  · filter_upwards [hres,hδpos,hδ.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      hN.eventually (eventually_ge_atTop N₀)] with n hn hnδ hnδ2 hnN
    have he := hn f hf hF (δ n) t hnδ hnδ2.le ⟨ht.1.le,ht.2.le⟩ hnN
    convert he using 1
    congr 1
    unfold localCalibrationBias
    ring

theorem hurstHolder_stride_first_log_mean_leading (p a b M : ℝ) (r d : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) (hd : 0<d)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop)
    (hN₁ : Tendsto (fun n : ℕ => (n:ℝ)*(δ n)^(r+1)) atTop atTop)
    (hN₂ : Tendsto (fun n : ℕ => (n:ℝ)^(2-2*b)*(δ n)^(r+1)) atTop atTop) :
    Tendsto (fun n : ℕ => (strideFirstGridLogExpectation r n d (δ n) t (midpointSampleHurst f hf.1 n)-
      (-2*Real.log n*f t+2*f t*Real.log d+gaussianLogSquareMean))/(Real.log n*(δ n)^(r+1)))
      atTop (𝓝 (-2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))) := by
  let φ : ℝ → ℝ := fun x => 2*x*Real.log d
  have hφ : ContDiff ℝ (r+1) φ := by unfold φ; fun_prop
  have hcomp : ContDiffOn ℝ (r+1) (φ ∘ f) (Ioo (0:ℝ) 1) := hφ.comp_contDiffOn hfc
  have hbias := localCalibrationBias_leading_tendsto r d f φ gaussianLogSquareMean hfc hcomp t ht δ hδpos hδ hN
  have herror := gridCovarianceError_scaled_tendsto b 1 (r+1) δ hδpos hN₁ hN₂
  obtain ⟨N₀,hN₀,C,hC,hres⟩ := hurstHolder_stride_first_log_expectation_residual p a b M r d hp ha hb hab hM hd
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine scalar_scaled_approximation_tendsto _ _ _ _ _ C ?_ hbias herror ?_
  · filter_upwards [hδpos,hlog.eventually_gt_atTop 0] with n hn hln
    positivity
  · filter_upwards [hres,hδpos,hδ.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      hN.eventually (eventually_ge_atTop N₀)] with n hn hnδ hnδ2 hnN
    have he := hn f hf hF (δ n) t hnδ hnδ2.le ⟨ht.1.le,ht.2.le⟩ hnN
    convert he using 1
    congr 1
    unfold localCalibrationBias φ
    ring

end Hurst
