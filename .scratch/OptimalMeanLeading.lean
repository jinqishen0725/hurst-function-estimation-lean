import Hurst.ActualMeanLeading
import Hurst.OptimalBiasBandwidth

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem optimalLocalBandwidth_bias_conditions (r : ℕ) (b : ℝ) (hb : b<3/4) :
    (∀ᶠ n in atTop,0<optimalLocalBandwidth ((r:ℝ)+1) n) ∧
    Tendsto (optimalLocalBandwidth ((r:ℝ)+1)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n) atTop atTop ∧
    Tendsto (fun n : ℕ => (n:ℝ)*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop atTop ∧
    Tendsto (fun n : ℕ => (n:ℝ)^(2-2*b)*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop atTop := by
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have hd : 0<2*((r:ℝ)+1)+1 := by positivity
  have hratio : ((r+1:ℕ):ℝ)/(2*((r:ℝ)+1)+1)<1/2 := by
    apply (div_lt_iff₀ hd).mpr
    push_cast
    linarith
  refine ⟨?_,optimalLocalBandwidth_tendsto_zero _ hp,?_,?_,?_⟩
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact optimalLocalBandwidth_pos _ n (by omega)
  · have hrat : (1:ℝ)/(2*((r:ℝ)+1)+1)<1 := by
      apply (div_lt_iff₀ hd).mpr
      linarith
    have hg := optimalLocalBandwidth_power_growth ((r:ℝ)+1) 1 1 (by convert hrat using 1 <;> norm_num)
    simpa using hg
  · have hg := optimalLocalBandwidth_power_growth ((r:ℝ)+1) 1 (r+1) (by linarith)
    simpa using hg
  · exact optimalLocalBandwidth_power_growth ((r:ℝ)+1) (2-2*b) (r+1) (by linarith)

theorem hurstHolder_second_log_mean_leading_optimal (a b M : ℝ) (r : ℕ) (hr : 1≤r)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n : ℕ => (secondGridLogExpectation r n (optimalLocalBandwidth ((r:ℝ)+1) n) t
      (midpointSampleHurst f hf.1 n)-(-2*Real.log n*f t+q2LogCorrection (f t)+gaussianLogSquareMean))/
      (Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))) atTop
      (𝓝 (-2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))) := by
  obtain ⟨hpos,hzero,hN,hNk,hN₂⟩ := optimalLocalBandwidth_bias_conditions r 0 (by norm_num)
  exact hurstHolder_second_log_mean_leading ((r:ℝ)+1) a b M r (by exact_mod_cast (show 2≤r+1 by omega))
    ha hb hab hM f hf hF hfc t ht _ hpos hzero hN hNk

theorem hurstHolder_stride_first_log_mean_leading_optimal (a b M : ℝ) (r d : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M) (hd : 0<d)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n : ℕ => (strideFirstGridLogExpectation r n d (optimalLocalBandwidth ((r:ℝ)+1) n) t
      (midpointSampleHurst f hf.1 n)-(-2*Real.log n*f t+2*f t*Real.log d+gaussianLogSquareMean))/
      (Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))) atTop
      (𝓝 (-2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))) := by
  obtain ⟨hpos,hzero,hN,hNk,hN₂⟩ := optimalLocalBandwidth_bias_conditions r b hb
  exact hurstHolder_stride_first_log_mean_leading ((r:ℝ)+1) a b M r d (by linarith [Nat.cast_nonneg (α := ℝ) r])
    ha (by linarith) hab hM hd f hf hF hfc t ht _ hpos hzero hN hNk hN₂

end Hurst
