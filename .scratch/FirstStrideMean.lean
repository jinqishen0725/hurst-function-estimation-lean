import Hurst.FirstStrideGrid
import Hurst.GridLogMeanSharp

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_stride_first_log_mean (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0:ℝ) 1) (Icc a b) → ∀ i : Fin (n-d),
      (∑ j, gridStrideFirstCoefficients n d i j • gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0) ∧
      |(Real.log (‖∑ j, gridStrideFirstCoefficients n d i j • gridObservationFeatures n (midpointSampleHurst f hf.1 n) j‖^2)+gaussianLogSquareMean)-
        (-2*f (grid n i.val)*Real.log n+2*f (grid n i.val)*Real.log d+gaussianLogSquareMean)| ≤ gridCovarianceError b C n := by
  obtain ⟨C,hC,hcov⟩ := hurstHolder_stride_first_covariance p a b M hp ha hb hab hM d hd
  refine ⟨2*C,by positivity,?_⟩
  have he := (gridCovarianceError_tendsto b C hb).eventually_le_const (by norm_num : (0:ℝ) < 1/2)
  filter_upwards [eventually_ge_atTop 1,he] with n hn hsmall
  intro f hf hF i
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  let H := midpointSampleHurst f hf.1 n
  let W := gridStrideFirstActual n d H i
  have hc := hcov n hn0 f hf hF i i
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hc
  have hfloor : (1/2:ℝ) ≤ ‖W‖^2 := by have := (abs_le.mp hc).1; dsimp only [W]; linarith
  have hW : W ≠ 0 := by intro hz; rw [hz,norm_zero] at hfloor; norm_num at hfloor
  have hfeat : ∑ j, gridStrideFirstCoefficients n d i j • gridObservationFeatures n H j ≠ 0 := by
    rw [gridStrideFirst_feature_identity n d hn0 hd H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' hW
  refine ⟨hfeat,?_⟩
  have hl := log_lipschitz_from_below (‖W‖^2) 1 (1/2) (by norm_num) hfloor (by norm_num)
  simp only [Real.log_one,sub_zero] at hl
  have herr : |Real.log (‖W‖^2)| ≤ 2*gridCovarianceError b C n := by
    change |‖W‖^2-1| ≤ gridCovarianceError b C n at hc
    linarith
  rw [gridStrideFirst_feature_identity n d hn0 hd H i, norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    Real.log_mul (pow_ne_zero 2 (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < (d:ℝ)/n) _).ne')
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hW)),Real.log_pow,Real.log_rpow (by positivity : (0:ℝ) < (d:ℝ)/n),Real.log_div hdR.ne' hnR.ne']
  have hid : 2*gridCovarianceError b C n = gridCovarianceError b (2*C) n := by unfold gridCovarianceError; ring
  rw [hid] at herr
  convert herr using 1
  congr 1
  dsimp only [W,H,midpointSampleHurst,strideFirstLeft]
  ring

end Hurst
