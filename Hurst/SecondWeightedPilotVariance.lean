import Hurst.WeightedMergedWeights
import Hurst.StrideCorrelationRows
import Hurst.CommonStrideMean
import Hurst.GaussianLogRisk
import Hurst.PilotTransfer
import Hurst.ActualPilot

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst
set_option maxHeartbeats 1000000

theorem coefficientAveraged_gaussianLogStatistic (n q m r : ℕ) (δ : ℝ)
    (c : Fin m → ℝ) (a : Fin (n-q) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑ j : Fin m,c j*gaussianLogStatistic (localPolynomialWeights r n q δ (grid m j.val)) a x)/(m:ℝ)=
      gaussianLogStatistic (coefficientAveragedLocalWeights r n q m δ c) a x := by
  unfold gaussianLogStatistic coefficientAveragedLocalWeights
  simp only [Finset.mul_sum]
  rw [div_eq_mul_inv]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

theorem coefficientAveraged_q2Pilot (r n m : ℕ) (δ : ℝ) (c : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑ j : Fin m,c j*q2Pilot r n δ (grid m j.val) x)/(m:ℝ)=
      twoScalePilot
        (gaussianLogStatistic (coefficientAveragedLocalWeights r n 4 m δ c)
          (commonStrideCoefficients n 1 4 (by norm_num)))
        (gaussianLogStatistic (coefficientAveragedLocalWeights r n 4 m δ c)
          (commonStrideCoefficients n 2 4 (by norm_num))) x := by
  unfold q2Pilot twoScalePilot
  calc
    _ = ((∑ j : Fin m,c j*gaussianLogStatistic (localPolynomialWeights r n 4 δ (grid m j.val))
          (commonStrideCoefficients n 2 4 (by norm_num)) x)/(m:ℝ)-
        (∑ j : Fin m,c j*gaussianLogStatistic (localPolynomialWeights r n 4 δ (grid m j.val))
          (commonStrideCoefficients n 1 4 (by norm_num)) x)/(m:ℝ))/(2*Real.log 2) := by
      simp only [div_eq_mul_inv]
      ring_nf
      rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      ring
    _ = _ := by
      rw [coefficientAveraged_gaussianLogStatistic,coefficientAveraged_gaussianLogStatistic]

/-- The first-order Taylor part of the nonlinear q=2 correction gains the
spatial-average rate `1/n`, even though each pilot separately has variance
of order `1/(n*δ)`. -/
theorem hurstHolder_q2_coefficientAveraged_pilot_variance
    (p a b M : ℝ) (r : ℕ) (hp : 2≤p) (ha : 0<a) (hb : b<1)
    (hab : a≤b) (hM : 0≤M) :
    ∃ N₀>0,∃ C≥0,∀ᶠ n : ℕ in atTop,∀ f : ℝ → ℝ,
      ∀ hf : f∈hurstHolderClass p M,MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ m : ℕ,0<m → ∀ δ : ℝ,0<δ → δ≤1/2 → N₀≤(n:ℝ)*δ →
      1≤(m:ℝ)*δ → ∀ c : Fin m → ℝ,∀ K : ℝ,0≤K → (∀ j,|c j|≤K) →
      MemLp (fun x => (∑ j : Fin m,c j*q2Pilot r n δ (grid m j.val) x)/(m:ℝ)) 2
        (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      Var[fun x => (∑ j : Fin m,c j*q2Pilot r n δ (grid m j.val) x)/(m:ℝ);
        featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))]≤C*K^2/(n:ℝ) := by
  obtain ⟨R₁,hR₁,hrows₁⟩ := hurstHolder_grid_stride_second_correlation_rows p a b M hp ha hb hab hM 1 (by norm_num)
  obtain ⟨R₂,hR₂,hrows₂⟩ := hurstHolder_grid_stride_second_correlation_rows p a b M hp ha hb hab hM 2 (by norm_num)
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := coefficientAveragedLocalWeights_uniform_bounds r 4
  obtain ⟨E₁,_,hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂,_,hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hrows₁.and (hrows₂.and (hm₁.and hm₂)))
  have hg := gaussianLogSquareVariance_nonneg
  have hC : 0≤12*gaussianLogSquareVariance*(D*D*(R₁+R₂))/(2*(Real.log 2)^2) := by positivity
  refine ⟨N₀,hN₀,12*gaussianLogSquareVariance*(D*D*(R₁+R₂))/(2*(Real.log 2)^2),hC,?_⟩
  filter_upwards [eventually_ge_atTop (max N 4)] with n hn
  intro f hf hF m hm δ hδ hδhalf hnd hmd c K hK hc
  have hn4 : 4≤n := (le_max_right N 4).trans hn
  have hn0 : 0<n := by omega
  obtain ⟨hrow1,hrow2,hm1,hm2⟩ := hN n ((le_max_left N 4).trans hn)
  let H := midpointSampleHurst f hf.1 n
  let v := gridObservationFeatures n H
  let w := coefficientAveragedLocalWeights r n 4 m δ c
  let a₁ := commonStrideCoefficients n 1 4 (by norm_num)
  let a₂ := commonStrideCoefficients n 2 4 (by norm_num)
  have hz₁ : ∀ i,∑ j,a₁ i j • v j≠0 := fun i => (hm1 f hf hF i).1
  have hz₂ : ∀ i,∑ j,a₂ i j • v j≠0 := fun i => (hm2 f hf hF i).1
  obtain ⟨hl1,hmax⟩ := hw n m hn0 hn4 hm δ hδ hδhalf hnd hmd c K hK hc
  have hr₁ : ∀ i,∑ j,(featureCorrelation v (a₁ i) (a₁ j))^2≤R₁ := by
    intro i
    dsimp [a₁,v,H]
    simp only [commonStrideCoefficients,gridStrideSecond_correlation_identity n 1 hn0 (by norm_num)]
    exact finite_subfamily_square_rows _ (commonStrideIndex_injective n 1 4 (by norm_num)) _ R₁
      (hrow1 f hf hF).2 i
  have hr₂ : ∀ i,∑ j,(featureCorrelation v (a₂ i) (a₂ j))^2≤R₂ := by
    intro i
    dsimp [a₂,v,H]
    simp only [commonStrideCoefficients,gridStrideSecond_correlation_identity n 2 hn0 (by norm_num)]
    exact finite_subfamily_square_rows _ (commonStrideIndex_injective n 2 4 (by norm_num)) _ R₂
      (hrow2 f hf hF).2 i
  have hG₁ := gaussianLogStatistic_memLp_two v w a₁ hz₁
  have hG₂ := gaussianLogStatistic_memLp_two v w a₂ hz₂
  have hv₁ := gaussianLogStatistic_variance_row_bound v w a₁ hz₁
    (3*(K*D)/(n:ℝ)) (K*D) R₁ (by positivity) hR₁ hmax hl1 hr₁
  have hv₂ := gaussianLogStatistic_variance_row_bound v w a₂ hz₂
    (3*(K*D)/(n:ℝ)) (K*D) R₂ (by positivity) hR₂ hmax hl1 hr₂
  have hpMem := twoScalePilot_memLp (featureGaussian v) _ _ hG₁ hG₂
  have hpVar := twoScalePilot_variance (featureGaussian v) _ _ hG₁ hG₂
  change MemLp (fun x => (∑ j : Fin m,c j*q2Pilot r n δ (grid m j.val) x)/(m:ℝ)) 2
      (featureGaussian v) ∧ Var[fun x => (∑ j : Fin m,c j*q2Pilot r n δ (grid m j.val) x)/(m:ℝ);
      featureGaussian v]≤_
  have hid : (fun x => (∑ j : Fin m,c j*q2Pilot r n δ (grid m j.val) x)/(m:ℝ))=
      twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) := by
    funext x
    exact coefficientAveraged_q2Pilot r n m δ c x
  rw [hid]
  refine ⟨hpMem,hpVar.trans ?_⟩
  have hh := div_le_div_of_nonneg_right (add_le_add hv₁ hv₂)
    (show 0≤2*(Real.log 2)^2 by positivity)
  exact hh.trans_eq (by ring)

end Hurst
