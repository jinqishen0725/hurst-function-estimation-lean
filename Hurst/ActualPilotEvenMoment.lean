import Hurst.ActualCommonLocalEvenMoment
import Hurst.EvenMomentAlgebra
import Hurst.ActualPilot

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem twoScalePilot_centered_evenPower_integrable
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a₁ a₂ : κ → EuclideanSpace ℝ ι)
    (h₁ : ∀ j, ∑ i, a₁ j i • v i ≠ 0)
    (h₂ : ∀ j, ∑ i, a₂ j i • v i ≠ 0) (k : ℕ) :
    Integrable (fun x => |twoScalePilot (gaussianLogStatistic w a₁)
      (gaussianLogStatistic w a₂) x -
      (∫ y, twoScalePilot (gaussianLogStatistic w a₁)
        (gaussianLogStatistic w a₂) y ∂featureGaussian v)| ^ (2 * k))
      (featureGaussian v) := by
  let X := twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂)
  have hG₁ := gaussianLogStatistic_memLp_finite v w a₁ h₁ (2 * k : ℝ)
  have hG₂ := gaussianLogStatistic_memLp_finite v w a₂ h₂ (2 * k : ℝ)
  have hX : MemLp X (ENNReal.ofReal (2 * k : ℝ)) (featureGaussian v) := by
    dsimp only [X, twoScalePilot]
    exact (hG₂.sub hG₁).mul_const _
  have hc := hX.sub (memLp_const (c := ∫ y, X y ∂featureGaussian v))
  have hi := hc.integrable_norm_rpow'
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
    show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
  simpa only [X, Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi

theorem hurstHolder_q2Pilot_centered_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (r : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 →
      N₀ ≤ (n : ℝ) * δ →
      (∫ x, |q2Pilot r n δ t x -
          (∫ y, q2Pilot r n δ t y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C / ((n : ℝ) * δ) ^ k := by
  obtain ⟨N₁, hN₁, C₁, hC₁, hm₁⟩ := hurstHolder_local_commonStride_centered_evenMoment
    hBS k hk p a b M hp ha hb hab hM r 1 4 (by omega) (by omega)
  obtain ⟨N₂, hN₂, C₂, hC₂, hm₂⟩ := hurstHolder_local_commonStride_centered_evenMoment
    hBS k hk p a b M hp ha hb hab hM r 2 4 (by omega) (by omega)
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_stride_log_mean
    p a b M 1 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_stride_log_mean
    p a b M 2 4 hp ha hb hab hM (by omega) (by omega)
  let c : ℝ := 1 / (2 * Real.log 2)
  have hc : 0 < c := by dsimp only [c]; positivity
  let C : ℝ := 2 ^ (2 * k - 1) * c ^ (2 * k) * (C₁ + C₂)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁ (le_max_left _ _), C, hC, ?_⟩
  filter_upwards [hm₁, hm₂, hz₁, hz₂] with n hm1 hm2 hnz1 hnz2
  intro f hf hF δ t hδ hδhalf ht hnδ
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := localPolynomialWeights r n 4 δ t
  let a₁ := commonStrideCoefficients n 1 4 (by omega)
  let a₂ := commonStrideCoefficients n 2 4 (by omega)
  let X := gaussianLogStatistic w a₁
  let Y := gaussianLogStatistic w a₂
  have hM₁ := hm1 f hf hF δ t hδ hδhalf ht ((le_max_left _ _).trans hnδ)
  have hM₂ := hm2 f hf hF δ t hδ hδhalf ht ((le_max_right _ _).trans hnδ)
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hXtwo := gaussianLogStatistic_memLp_two v w a₁ hfeat₁
  have hYtwo := gaussianLogStatistic_memLp_two v w a₂ hfeat₂
  have hX : Integrable X P := hXtwo.integrable one_le_two
  have hY : Integrable Y P := hYtwo.integrable one_le_two
  have hXp : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P := by
    have hfinite := (gaussianLogStatistic_memLp_finite v w a₁ hfeat₁ (2 * k : ℝ)).sub
      (memLp_const (c := ∫ y, X y ∂P))
    have hi := hfinite.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [X, P, Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hYp : Integrable (fun x => |Y x - ∫ y, Y y ∂P| ^ (2 * k)) P := by
    have hfinite := (gaussianLogStatistic_memLp_finite v w a₂ hfeat₂ (2 * k : ℝ)).sub
      (memLp_const (c := ∫ y, Y y ∂P))
    have hi := hfinite.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Y, P, Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hcomb := centered_linear_combination_evenMoment_le P X Y (-c) c k hk hX hY hXp hYp
  have hpilot : q2Pilot r n δ t = fun x => (-c) * X x + c * Y x := by
    funext x
    unfold q2Pilot twoScalePilot
    dsimp only [c, X, Y, w, a₁, a₂]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    ring
  rw [hpilot]
  apply hcomb.trans
  rw [abs_neg, abs_of_pos hc]
  calc
    2 ^ (2 * k - 1) *
        (c ^ (2 * k) * (∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
         c ^ (2 * k) * (∫ x, |Y x - ∫ y, Y y ∂P| ^ (2 * k) ∂P)) ≤
      2 ^ (2 * k - 1) *
        (c ^ (2 * k) * (C₁ / ((n : ℝ) * δ) ^ k) +
         c ^ (2 * k) * (C₂ / ((n : ℝ) * δ) ^ k)) := by
      gcongr
    _ = C / ((n : ℝ) * δ) ^ k := by
      dsimp only [C]
      ring

end Hurst
