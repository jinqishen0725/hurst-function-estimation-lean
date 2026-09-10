import Hurst.ScaleAverage
import Hurst.CommonLogBias

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst
set_option maxHeartbeats 800000

theorem hurstHolder_q2_linearScale_bias (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ B ≥ 0, ∃ E ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n → ∀ m : ℕ, 0 < m →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → N₀ ≤ (n:ℝ)*δ →
      |(∫ x, q2LinearScale (Nat.ceil p-1) n m δ x ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) -
        (∑ j : Fin m, (q2LogCorrection (f (grid m j.val))+gaussianLogSquareMean))/(m:ℝ)| ≤
        B*Real.log n*δ^p+Real.log n*gridCovarianceError (1/2) E n := by
  obtain ⟨Np, hNp, Bp, hBp, Ep, hEp, Vp, hVp, Np₀, hNp₀, hpm⟩ := hurstHolder_q2_pilot_moments p a b M hp ha hb hab hM
  obtain ⟨Ng, hNg, Bg, hBg, Eg, hEg, Ng₀, hNg₀, hgm⟩ := hurstHolder_common_log_bias p a b M hp ha hb hab hM
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hm₁
  refine ⟨max Np Ng, lt_of_lt_of_le hNp (le_max_left _ _), Bg+2*Bp, by positivity, Eg+2*Ep, by positivity,
    max (max Np₀ Ng₀) K, hNp₀.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro f hf hF n hn hL m hm δ hδ hδhalf hnd
  obtain ⟨g, hg, heq, hgb, hpilot⟩ := hpm f hf hF
  have hnp : Np₀ ≤ n := ((le_max_left Np₀ Ng₀).trans (le_max_left _ _)).trans hn
  have hng : Ng₀ ≤ n := ((le_max_right Np₀ Ng₀).trans (le_max_left _ _)).trans hn
  have hn0 : 0 < n := by omega
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hge := hgm f hf hF g hg heq n hng hL
  have hmean := hK n ((le_max_right _ _).trans hn) f hf hF
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let X := fun j : Fin m => gaussianLogStatistic (localPolynomialWeights (Nat.ceil p-1) n 4 δ (grid m j.val))
    (commonStrideCoefficients n 1 4 (by norm_num))
  let Y := fun j : Fin m => q2Pilot (Nat.ceil p-1) n δ (grid m j.val)
  have hj : ∀ j : Fin m, grid m j.val ∈ Ioo (0:ℝ) 1 := fun j => grid_mem m j.val hm j.isLt
  have hj' : ∀ j : Fin m, grid m j.val ∈ Icc (0:ℝ) 1 := fun j => ⟨(hj j).1.le, (hj j).2.le⟩
  have hmemX : ∀ j, MemLp (X j) 2 (featureGaussian v) := fun j =>
    gaussianLogStatistic_memLp_two v _ _ (fun i => (hmean i).1)
  have hmemY : ∀ j, MemLp (Y j) 2 (featureGaussian v) := fun j =>
    (hpilot n hnp δ _ hδ hδhalf (hj' j) ((le_max_left _ _).trans hnd)).1
  have hlin : ∀ j, Integrable (fun x => X j x+2*Real.log n*Y j x) (featureGaussian v) :=
    fun j => ((hmemX j).add ((hmemY j).const_mul _)).integrable one_le_two
  have hbias : ∀ j, |(∫ x, X j x+2*Real.log n*Y j x ∂featureGaussian v)-
      (q2LogCorrection (f (grid m j.val))+gaussianLogSquareMean)| ≤
      (Bg+2*Bp)*Real.log n*δ^p+Real.log n*gridCovarianceError (1/2) (Eg+2*Ep) n := by
    intro j
    have hpb := (hpilot n hnp δ _ hδ hδhalf (hj' j) ((le_max_left _ _).trans hnd)).2.1
    have hgb := hge δ _ hδ hδhalf (hj' j) ((le_max_right _ _).trans hnd)
    have hgval : g (grid m j.val) = f (grid m j.val) := (heq (hj j)).symm
    rw [hgval] at hpb hgb
    rw [integral_add ((hmemX j).integrable one_le_two) (((hmemY j).integrable one_le_two).const_mul _), integral_const_mul]
    have hid : (∫ x, X j x ∂featureGaussian v)+2*Real.log n*(∫ x, Y j x ∂featureGaussian v)-
        (q2LogCorrection (f (grid m j.val))+gaussianLogSquareMean) =
        ((∫ x, X j x ∂featureGaussian v)-(gaussianLogSquareMean-2*Real.log n*f (grid m j.val)+q2LogCorrection (f (grid m j.val))))+
        2*Real.log n*((∫ x, Y j x ∂featureGaussian v)-f (grid m j.val)) := by ring
    rw [hid]
    have he := abs_add_le ((∫ x, X j x ∂featureGaussian v)-(gaussianLogSquareMean-2*Real.log n*f (grid m j.val)+q2LogCorrection (f (grid m j.val))))
      (2*Real.log n*((∫ x, Y j x ∂featureGaussian v)-f (grid m j.val)))
    rw [abs_mul, abs_of_nonneg (show 0 ≤ 2*Real.log n by linarith)] at he
    have h := he.trans (add_le_add hgb (mul_le_mul_of_nonneg_left hpb (by linarith : 0 ≤ 2*Real.log n)))
    apply h.trans
    have heg : 0 ≤ gridCovarianceError (1/2) Eg n := by
      unfold gridCovarianceError
      have hl := Real.log_nonneg (show (1:ℝ) ≤ 2*n by linarith)
      positivity
    have hgain := mul_le_mul_of_nonneg_right hL heg
    have hid' : gridCovarianceError (1/2) (Eg+2*Ep) n =
      gridCovarianceError (1/2) Eg n+2*gridCovarianceError (1/2) Ep n := by unfold gridCovarianceError; ring
    rw [hid']
    nlinarith
  simp_rw [q2LinearScale_eq_average]
  exact finite_average_expectation_bias (featureGaussian v) m hm (fun j x => X j x+2*Real.log n*Y j x)
    (fun j => q2LogCorrection (f (grid m j.val))+gaussianLogSquareMean) _ hlin hbias

end Hurst
