import Hurst.GaussianMeanApproximation
import Hurst.CalibratedBiasLimit
import Hurst.SecondGridLogMean
import Hurst.FirstStrideMean

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

def secondGridLogExpectation (r n : ℕ) (δ t : ℝ) (H : Fin n → Ioo (0:ℝ) 1) : ℝ :=
  ∫ x,gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x
    ∂featureGaussian (gridObservationFeatures n H)

def strideFirstGridLogExpectation (r n d : ℕ) (δ t : ℝ) (H : Fin n → Ioo (0:ℝ) 1) : ℝ :=
  ∫ x,gaussianLogStatistic (localPolynomialWeights r n d δ t) (gridStrideFirstCoefficients n d) x
    ∂featureGaussian (gridObservationFeatures n H)

theorem hurstHolder_second_log_expectation_residual (p a b M : ℝ) (r : ℕ)
    (hp : 2≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) :
    ∃ N₀>0,∃ C≥0,∀ᶠ n : ℕ in atTop,∀ f : ℝ → ℝ,∀ hf : f∈hurstHolderClass p M,
      MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ,0<δ → δ≤1/2 → t∈Icc (0:ℝ) 1 → N₀≤(n:ℝ)*δ →
      |secondGridLogExpectation r n δ t (midpointSampleHurst f hf.1 n)-
        smooth (localPolynomialWeights r n 2 δ t)
          (fun i => -2*Real.log n*f (grid n i.val)+q2LogCorrection (f (grid n i.val))+gaussianLogSquareMean)| ≤
        C*gridCovarianceError (1/2) 1 n := by
  obtain ⟨E,hE,hmean⟩ := hurstHolder_grid_second_log_mean p a b M hp ha hb hab hM
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := localPolynomialWeights_uniform_stability r 2
  refine ⟨N₀,hN₀,D*E,by positivity,?_⟩
  filter_upwards [hmean,eventually_ge_atTop 2] with n hn hn2
  intro f hf hF δ t hδ hδ2 ht hN
  have hn0 : 0<n := by omega
  have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  have ha' : ∀ i,∑ j,gridSecondCoefficients n i j • v j≠0 := fun i => (hn f hf hF i).1
  have hm : ∀ i,|Real.log (‖∑ j,gridSecondCoefficients n i j • v j‖^2)+gaussianLogSquareMean-
      (-2*Real.log n*f (grid n i.val)+q2LogCorrection (f (grid n i.val))+gaussianLogSquareMean)| ≤
        gridCovarianceError (1/2) E n := by
    intro i
    have he := (hn f hf hF i).2
    rw [featureGaussian_expected_log_square _ _ (ha' i)] at he
    convert he using 1 <;> congr 1 <;> ring
  have he := gaussianLogStatistic_mean_approximation v (localPolynomialWeights r n 2 δ t)
    (gridSecondCoefficients n) ha' _ _ hm
  obtain ⟨hdet,hmax,hsum,hmom⟩ := hw n hn0 hn2 δ t hδ hδ2 ht hN
  have herr : 0≤gridCovarianceError (1/2) E n := by
    unfold gridCovarianceError
    have hl := Real.log_nonneg (show (1:ℝ)≤2*n by linarith)
    positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hsum herr).trans_eq (by unfold gridCovarianceError; ring))

theorem hurstHolder_stride_first_log_expectation_residual (p a b M : ℝ) (r d : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) (hd : 0<d) :
    ∃ N₀>0,∃ C≥0,∀ᶠ n : ℕ in atTop,∀ f : ℝ → ℝ,∀ hf : f∈hurstHolderClass p M,
      MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ,0<δ → δ≤1/2 → t∈Icc (0:ℝ) 1 → N₀≤(n:ℝ)*δ →
      |strideFirstGridLogExpectation r n d δ t (midpointSampleHurst f hf.1 n)-
        smooth (localPolynomialWeights r n d δ t)
          (fun i => -2*Real.log n*f (grid n i.val)+(2*f (grid n i.val)*Real.log d)+gaussianLogSquareMean)| ≤
        C*gridCovarianceError b 1 n := by
  obtain ⟨E,hE,hmean⟩ := hurstHolder_stride_first_log_mean p a b M hp ha hb hab hM d hd
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := localPolynomialWeights_uniform_stability r d
  refine ⟨N₀,hN₀,D*E,by positivity,?_⟩
  filter_upwards [hmean,eventually_ge_atTop d] with n hn hnd
  intro f hf hF δ t hδ hδ2 ht hN
  have hn0 : 0<n := by omega
  have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  have ha' : ∀ i,∑ j,gridStrideFirstCoefficients n d i j • v j≠0 := fun i => (hn f hf hF i).1
  have hm : ∀ i,|Real.log (‖∑ j,gridStrideFirstCoefficients n d i j • v j‖^2)+gaussianLogSquareMean-
      (-2*Real.log n*f (grid n i.val)+2*f (grid n i.val)*Real.log d+gaussianLogSquareMean)| ≤
        gridCovarianceError b E n := by
    intro i
    convert (hn f hf hF i).2 using 1 <;> congr 1 <;> ring
  have he := gaussianLogStatistic_mean_approximation v (localPolynomialWeights r n d δ t)
    (gridStrideFirstCoefficients n d) ha' _ _ hm
  obtain ⟨hdet,hmax,hsum,hmom⟩ := hw n hn0 hnd δ t hδ hδ2 ht hN
  have herr : 0≤gridCovarianceError b E n := by
    unfold gridCovarianceError
    have hl := Real.log_nonneg (show (1:ℝ)≤2*n by linarith)
    positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hsum herr).trans_eq (by unfold gridCovarianceError; ring))

end Hurst
