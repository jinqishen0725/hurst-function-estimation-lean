from pathlib import Path
s='''import Hurst.FeatureConditionalCLT
import Hurst.GridHermiteApproximation

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst
'''
for q in [1,2]:
 d=str(q)
 name='stride_first' if q==1 else 'grid_second'
 coeff='(gridStrideFirstCoefficients n 1)' if q==1 else '(gridSecondCoefficients n)'
 rows='hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM 1 (by norm_num)' if q==1 else 'hurstHolder_grid_second_correlation_rows p a b M hp ha hb hab hM'
 ident='gridStrideFirst_feature_identity n 1 hn0 (by norm_num) H i' if q==1 else 'gridSecond_feature_identity n hn0 H i'
 corr='gridStrideFirst_correlation_identity n 1 hn0 (by norm_num) H' if q==1 else 'gridSecond_correlation_identity n hn0 H'
 s+=f'''
theorem hurstHolder_{name}_CLT_of_polynomial_limits (p a b M : ℝ) (r : ℕ)
    (hp : {q}≤p) (ha : 0<a) (hb : b<{'3/4' if q==1 else '1'}) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop,0<δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n => (n:ℝ)*δ n) atTop atTop)
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hpoly : ∀ k,TendstoInDistribution
      (fun n x => Real.sqrt ((n:ℝ)*δ n)*gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n {d} (δ n) t) {coeff} k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1)) :
    TendstoInDistribution (fun n x => Real.sqrt ((n:ℝ)*δ n)*
      (gaussianLogStatistic (localPolynomialWeights r n {d} (δ n) t) {coeff} x-
        (∫ y,gaussianLogStatistic (localPolynomialWeights r n {d} (δ n) t) {coeff} y
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop
      (fun z : ℝ => Real.sqrt V*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) := by
  obtain ⟨R,hR,hrows⟩ := {rows}
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := localPolynomialWeights_energy r {d}
  have hevent := hrows.and ((eventually_ge_atTop {d}).and
    (hδ.and ((hδ0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).and (hN.eventually_ge_atTop N₀))))
  have hdata : ∀ᶠ n in atTop,
      (∀ i,∑ j,{coeff} i j • gridObservationFeatures n (midpointSampleHurst f hf.1 n) j≠0) ∧
      (∀ i,∑ j,featureCorrelation (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        ({coeff} i) ({coeff} j)^2≤R) ∧
      (Real.sqrt ((n:ℝ)*δ n))^2*R*(∑ i,localPolynomialWeights r n {d} (δ n) t i^2)≤R*D := by
    filter_upwards [hevent] with n hn
    obtain ⟨hrows,hn,hδ,hδhalf,hN⟩ := hn
    obtain ⟨hzero,hrow⟩ := hrows f hf hF
    have hn0 : 0<n := by omega
    let H := midpointSampleHurst f hf.1 n
    refine ⟨?_,?_,?_⟩
    · intro i
      rw [{ident}]
      exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
    · intro i
      simpa only [{corr}] using hrow i
    · rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hδ.le)]
      have he := mul_le_mul_of_nonneg_left (hw n hn0 hn (δ n) t hδ hδhalf.le ht hN) hR
      convert he using 1 <;> ring
  exact featureGaussian_log_CLT_of_polynomial_limits (fun n => n-{d})
    (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => localPolynomialWeights r n {d} (δ n) t) (fun n => {coeff})
    (fun n => Real.sqrt ((n:ℝ)*δ n)) (fun _ => R) (R*D)
    (hdata.mono (fun _ hn => hn.1)) (hdata.mono (fun _ hn => hn.2.1))
    (hdata.mono (fun _ hn => hn.2.2)) V Vk hV hpoly
'''
s+='\nend Hurst\n'
Path('.scratch/ActualConditionalCLT.lean').write_text(s)
