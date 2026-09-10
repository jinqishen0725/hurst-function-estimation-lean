import Hurst.ActualPilotRawEvenMoment
import Hurst.NonlinearScaleRisk
import Hurst.ScaleMeasurability

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

/-- The averaged clipped correction in the second estimator inherits the full
`2k` pilot moment bound.  The constant is uniform in the sample size, grid
size, bandwidth, and Hurst function. -/
theorem hurstHolder_q2_nonlinearScale_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ Cp > 0, ∃ B ≥ 0, ∃ E ≥ 0, ∃ C ≥ 1,
      ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ n : ℕ, N ≤ n → ∀ m : ℕ, 0 < m → ∀ δ : ℝ,
      0 < δ → δ ≤ 1 / 2 → N₀ ≤ (n : ℝ) * δ →
      Integrable (fun x => |q2NonlinearScaleError a b (Nat.ceil p - 1) n m δ f x| ^
        (2 * k))
        (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      (∫ x, |q2NonlinearScaleError a b (Nat.ceil p - 1) n m δ f x| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C ^ (2 * k) * 2 ^ (2 * k - 1) *
          (Cp / ((n : ℝ) * δ) ^ k +
            (B * δ ^ p + gridCovarianceError (1 / 2) E n) ^ (2 * k)) := by
  obtain ⟨N₀, hN₀, Cp, hCp, B, hB, E, hE, Nr, hNr, hraw⟩ :=
    hurstHolder_q2Pilot_evenMoment_about_extension hBS k hk p a b M hp ha hb hab hM
  obtain ⟨C, hC, herr⟩ :=
    smooth_clipped_error q2LogCorrection q2LogCorrection_smooth a b ha hb
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_stride_log_mean
    p a b M 1 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_stride_log_mean
    p a b M 2 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hz₁.and hz₂)
  let N := max Nr K
  refine ⟨N₀, hN₀, Cp, hCp, B, hB, E, hE, C, hC, N,
    hNr.trans (le_max_left _ _), ?_⟩
  intro f hf hF n hn m hm δ hδ hδhalf hnδ
  obtain ⟨g, hg, heq, hgmap, hpilot⟩ := hraw f hf hF
  obtain ⟨hnz1, hnz2⟩ := hK n ((le_max_right _ _).trans hn)
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := fun j : Fin m =>
    localPolynomialWeights (Nat.ceil p - 1) n 4 δ (grid m j.val)
  let a₁ := commonStrideCoefficients n 1 4 (by omega)
  let a₂ := commonStrideCoefficients n 2 4 (by omega)
  let X := fun j : Fin m => q2Pilot (Nat.ceil p - 1) n δ (grid m j.val)
  let Y := fun j : Fin m => fun x =>
    q2LogCorrection (clip a b (X j x)) - q2LogCorrection (f (grid m j.val))
  let R := C ^ (2 * k) * 2 ^ (2 * k - 1) *
    (Cp / ((n : ℝ) * δ) ^ k +
      (B * δ ^ p + gridCovarianceError (1 / 2) E n) ^ (2 * k))
  have hj : ∀ j : Fin m, grid m j.val ∈ Ioo (0 : ℝ) 1 :=
    fun j => grid_mem m j.val hm j.isLt
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hG₁ : ∀ j, MemLp (gaussianLogStatistic (w j) a₁) 2 P :=
    fun j => gaussianLogStatistic_memLp_two v (w j) a₁ hfeat₁
  have hG₂ : ∀ j, MemLp (gaussianLogStatistic (w j) a₂) 2 P :=
    fun j => gaussianLogStatistic_memLp_two v (w j) a₂ hfeat₂
  have hXi : ∀ j, Integrable (X j) P := by
    intro j
    change Integrable (twoScalePilot (gaussianLogStatistic (w j) a₁)
      (gaussianLogStatistic (w j) a₂)) P
    exact (twoScalePilot_memLp P _ _ (hG₁ j) (hG₂ j)).integrable one_le_two
  have hXcenter : ∀ j, Integrable
      (fun x => |X j x - ∫ y, X j y ∂P| ^ (2 * k)) P := by
    intro j
    change Integrable (fun x => |twoScalePilot (gaussianLogStatistic (w j) a₁)
      (gaussianLogStatistic (w j) a₂) x -
      (∫ y, twoScalePilot (gaussianLogStatistic (w j) a₁)
        (gaussianLogStatistic (w j) a₂) y ∂P)| ^ (2 * k)) P
    exact twoScalePilot_centered_evenPower_integrable v (w j) a₁ a₂ hfeat₁ hfeat₂ k
  have hYm : ∀ j, AEStronglyMeasurable (Y j) P := by
    intro j
    have hphi : Measurable q2LogCorrection := by unfold q2LogCorrection; fun_prop
    exact ((hphi.comp ((clip_continuous a b).measurable.comp
      (q2Pilot_measurable _ _ _ _))).sub measurable_const).aestronglyMeasurable
  have hY : ∀ j, Integrable (fun x => |Y j x| ^ (2 * k)) P ∧
      (∫ x, |Y j x| ^ (2 * k) ∂P) ≤ R := by
    intro j
    have hgj : g (grid m j.val) = f (grid m j.val) := (heq (hj j)).symm
    have hpj := hpilot n ((le_max_left _ _).trans hn) δ (grid m j.val)
      hδ hδhalf ⟨(hj j).1.le, (hj j).2.le⟩ hnδ
    rw [hgj] at hpj
    have hrawInt := evenPower_about_integrable P (X j) (f (grid m j.val)) k hk
      (hXi j) (hXcenter j)
    have hdom : ∀ x, |Y j x| ^ (2 * k) ≤
        C ^ (2 * k) * |X j x - f (grid m j.val)| ^ (2 * k) := by
      intro x
      have hlip := herr (X j x) (f (grid m j.val)) (hF (hj j))
      have hp := pow_le_pow_left₀ (abs_nonneg _) hlip (2 * k)
      simpa only [Y, mul_pow] using hp
    have hYint : Integrable (fun x => |Y j x| ^ (2 * k)) P :=
      (hrawInt.const_mul (C ^ (2 * k))).mono' ((hYm j).norm.pow (2 * k))
        (Filter.Eventually.of_forall (fun x => by
          simpa only [Real.norm_eq_abs, abs_pow, abs_abs, abs_mul,
            abs_of_nonneg hC0] using hdom x))
    refine ⟨hYint, ?_⟩
    calc
      (∫ x, |Y j x| ^ (2 * k) ∂P) ≤
          ∫ x, C ^ (2 * k) * |X j x - f (grid m j.val)| ^ (2 * k) ∂P :=
        integral_mono hYint (hrawInt.const_mul _) hdom
      _ = C ^ (2 * k) *
          (∫ x, |X j x - f (grid m j.val)| ^ (2 * k) ∂P) := by
        rw [integral_const_mul]
      _ ≤ R := by
        dsimp only [R]
        simpa only [P, X, mul_assoc] using
          (mul_le_mul_of_nonneg_left hpj (pow_nonneg hC0 (2 * k)))
  have havg := finite_average_evenMoment_bound P m hm Y k hk R hYm
    (fun j => (hY j).1) (fun j => (hY j).2)
  have havgInt := finite_average_evenPower_integrable P m hm Y k hk hYm
    (fun j => (hY j).1)
  exact ⟨by simpa only [q2NonlinearScaleError, Y, X] using havgInt,
    by simpa only [q2NonlinearScaleError, Y, X, R] using havg⟩

end Hurst
