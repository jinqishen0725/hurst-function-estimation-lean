import Hurst.BiasVarianceScale
import Hurst.SecondGridLogMean
import Hurst.CommonFirstVariance
import Hurst.FirstStrideMean

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_second_optimal_log_variance (a b M : ℝ) (r : ℕ) (hr : 1≤r)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    ∃ V≥0,∀ᶠ n : ℕ in atTop,
      MemLp (gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridSecondCoefficients n)) 2 (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      Var[gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridSecondCoefficients n);featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤
        V*(Real.log n)^2*((optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))^2 := by
  have hp : (2:ℝ)≤(r:ℝ)+1 := by exact_mod_cast (show 2≤r+1 by omega)
  obtain ⟨N₀,hN₀,V,hV,hvar⟩ := hurstHolder_grid_second_log_variance ((r:ℝ)+1) a b M r hp ha hb hab hM
  obtain ⟨E,hE,hmean⟩ := hurstHolder_grid_second_log_mean ((r:ℝ)+1) a b M hp ha hb hab hM
  refine ⟨V,hV,?_⟩
  filter_upwards [hvar,hmean,optimalLocalBandwidth_eventual_design ((r:ℝ)+1) N₀ (by linarith)] with n hv hm hdesign
  obtain ⟨hn,hδ,hδ2,hnd,hrate,hlog⟩ := hdesign
  have hz := fun i => (hm f hf hF i).1
  refine ⟨gaussianLogStatistic_memLp_two _ _ _ hz,?_⟩
  have he := hv f hf hF _ t hδ hδ2 ht hnd
  exact he.trans_eq (by
    calc
      _ = V*(1/((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)) := by ring
      _ = _ := by rw [optimalLocalBandwidth_raw_variance_balance r n hn]; ring)

theorem hurstHolder_stride_first_optimal_log_variance (a b M : ℝ) (r d : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M) (hd : 0<d)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    ∃ V≥0,∀ᶠ n : ℕ in atTop,
      MemLp (gaussianLogStatistic (localPolynomialWeights r n d (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridStrideFirstCoefficients n d)) 2 (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      Var[gaussianLogStatistic (localPolynomialWeights r n d (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridStrideFirstCoefficients n d);featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤
        V*(Real.log n)^2*((optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))^2 := by
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  obtain ⟨N₀,hN₀,V,hV,hvar⟩ := hurstHolder_common_first_stride_log_variance ((r:ℝ)+1) a b M r d d hp ha hb hab hM hd le_rfl
  obtain ⟨E,hE,hmean⟩ := hurstHolder_stride_first_log_mean ((r:ℝ)+1) a b M hp ha (by linarith) hab hM d hd
  refine ⟨V,hV,?_⟩
  filter_upwards [hvar,hmean,optimalLocalBandwidth_eventual_design ((r:ℝ)+1) N₀ hp] with n hv hm hdesign
  obtain ⟨hn,hδ,hδ2,hnd,hrate,hlog⟩ := hdesign
  have hz := fun i => (hm f hf hF i).1
  refine ⟨gaussianLogStatistic_memLp_two _ _ _ hz,?_⟩
  have he : Var[gaussianLogStatistic (localPolynomialWeights r n d (optimalLocalBandwidth ((r:ℝ)+1) n) t)
      (gridStrideFirstCoefficients n d);featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤
        V/((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n) := by
    convert hv f hf hF _ t hδ hδ2 ht hnd using 1 <;> rfl
  exact he.trans_eq (by
    calc
      _ = V*(1/((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)) := by ring
      _ = _ := by rw [optimalLocalBandwidth_raw_variance_balance r n hn]; ring)

end Hurst
