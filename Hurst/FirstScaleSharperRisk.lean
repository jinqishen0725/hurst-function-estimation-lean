import Hurst.FirstScaleVariance
import Hurst.FirstScaleBias
import Hurst.ScaleBandwidth

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_scale_risk_log_squared_over_n (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ n : ℕ, N ≤ n →
      MemLp (q1LogScaleEstimator (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n)) 2
        (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      (∫ x, (q1LogScaleEstimator (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x)^2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/(Real.log n)^2 ≤ C/(n:ℝ) := by
  obtain ⟨Nv,hNv,V,hV,Nv₀,hNv₀,hvar⟩ := hurstHolder_q1_linearScale_variance p a b M (Nat.ceil p-1) hp ha hb hab hM
  obtain ⟨Nb,hNb,E,hE,Nb₀,hNb₀,hbias⟩ := hurstHolder_q1_linearScale_bias p a b M (Nat.ceil p-1) hp ha hb hab hM
  have herr := (gridCovarianceError_square_row_tendsto b E hb).eventually_le_const zero_lt_one
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((optimalLocalBandwidth_eventual_design p (max Nv Nb) hp).and herr)
  let N := max (max Nv₀ Nb₀) K
  refine ⟨V+1,by positivity,N,hNv₀.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro f hf hF n hn
  have hnv : Nv₀ ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnb : Nb₀ ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  obtain ⟨⟨hn1,hδ,hδhalf,hnd,hrate,hL⟩,he⟩ := hK n ((le_max_right _ _).trans hn)
  obtain ⟨hm,hmd⟩ := scaleAverageResolution_design p n hδ
  obtain ⟨hmem,hv⟩ := hvar n hnv hL f hf hF _ hm _ hδ hδhalf ((le_max_left _ _).trans hnd) hmd
  have hbias' := hbias n hnb hL f hf hF _ hm _ hδ hδhalf ((le_max_right _ _).trans hnd) hmd
  refine ⟨hmem.sub (memLp_const _),?_⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL0 : 0 < Real.log (n:ℝ) := by linarith
  have he' : (gridCovarianceError b E n)^2 ≤ 1/(n:ℝ) := (le_div_iff₀ hnR).mpr (by simpa only [mul_comm] using he)
  have hmse := mse_decomposition (q1LinearScale (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n)) gaussianLogSquareMean hmem
  have hb2 := pow_le_pow_left₀ (abs_nonneg _) hbias' 2
  rw [sq_abs,mul_pow] at hb2
  unfold q1LogScaleEstimator
  rw [hmse]
  apply (div_le_div_of_nonneg_right (add_le_add hv hb2) (sq_nonneg _)).trans
  have hid : (V*(Real.log n)^2/(n:ℝ)+(Real.log n)^2*(gridCovarianceError b E n)^2)/(Real.log n)^2 =
      V/(n:ℝ)+(gridCovarianceError b E n)^2 := by field_simp
  rw [hid]
  calc
    _ ≤ V/(n:ℝ)+1/(n:ℝ) := add_le_add le_rfl he'
    _ = _ := by ring

end Hurst
