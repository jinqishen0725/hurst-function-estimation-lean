import Hurst.RawScaleTransfer
import Hurst.ConditionalMomentMinimax

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_rawMomentBound
    (hBS : BardetSurgailisLemmaOneScalar)
    (p a b M s : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (hs : 2 ≤ s) :
    Q1RawMomentBound p a b M s := by
  let k := Nat.ceil s
  have hk : 1 ≤ k := by
    have : 0 < k := (Nat.ceil_pos.mpr (by linarith : 0 < s))
    omega
  have hsk : s ≤ ((2 * k : ℕ) : ℝ) := by
    have hc : s ≤ (k : ℝ) := by simpa only [k] using Nat.le_ceil s
    have hkR : 0 ≤ (k : ℝ) := by positivity
    norm_num at hc ⊢
    linarith
  obtain ⟨C, hC, N₀, hN₀, heven⟩ :=
    hurstHolder_q1_optimal_raw_evenMoment hBS k hk p a b M hp ha hb hab hM
  obtain ⟨N₁, hN₁, D₁, hD₁, hw₁⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨N₂, hN₂, D₂, hD₂, hw₂⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 2
  obtain ⟨E₀, _, hm₀⟩ := hurstHolder_stride_first_log_mean p a b M hp ha (by linarith) hab hM 1 (by norm_num)
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha (by linarith) hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha (by linarith) hab hM (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hm₀.and (hm₁.and (hm₂.and (optimalLocalBandwidth_eventual_design p (max N₁ N₂) hp))))
  let N := max N₀ (max K 4)
  refine ⟨C, hC, N, (le_max_right K 4).trans (le_max_right _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgmap, hunitEven⟩ := heven f hf hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro σ hσ n hn t ht
  obtain ⟨h₀, h₁, h₂, hd⟩ := hK n
    ((le_max_left K 4).trans ((le_max_right N₀ _).trans hn))
  obtain ⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩ := hd
  obtain ⟨hm, hmd⟩ := scaleAverageResolution_design p n hδ
  have hws : ∑ i, localPolynomialWeights (Nat.ceil p - 1) n 1
      (optimalLocalBandwidth p n) t i = 1 := by
    have he := (hw₁ n (by omega) (by omega) _ t hδ hδhalf
      ⟨ht.1.le, ht.2.le⟩ ((le_max_left _ _).trans hnd)).2.2.2 0
    simpa using he
  have hwm : ∑ i, averagedLocalWeights (Nat.ceil p - 1) n 2
      (scaleAverageResolution p n) (optimalLocalBandwidth p n) i = 1 := by
    apply averagedLocalWeights_sum _ _ _ _ hm
    intro j
    have hj := grid_mem (scaleAverageResolution p n) j.val hm j.isLt
    have he := (hw₂ n (by omega) (by omega) _ _ hδ hδhalf
      ⟨hj.1.le, hj.2.le⟩ ((le_max_right _ _).trans hnd)).2.2.2 0
    simpa using he
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let R := q1RawLogDifference (Nat.ceil p - 1) n (scaleAverageResolution p n)
    (optimalLocalBandwidth p n) t
  have hRmem : MemLp R (ENNReal.ofReal s) (featureGaussian v) :=
    q1RawLogDifference_memLp_finite _ _ _ _ _ v
      (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1)
      (fun i => (h₂ f hf hF i).1) s
  have hcenterMem : MemLp (fun x => R x -
      calibrationOne (Real.log n) gaussianLogSquareMean (g t))
      (ENNReal.ofReal (2 * k : ℝ)) (featureGaussian v) :=
    (q1RawLogDifference_memLp_finite _ _ _ _ _ v
      (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1)
      (fun i => (h₂ f hf hF i).1) (2 * k : ℝ)).sub (memLp_const _)
  have hEven := hunitEven n ((le_max_left N₀ _).trans hn) t ⟨ht.1.le, ht.2.le⟩
  have hlow := lower_real_moment_of_even (featureGaussian v)
    (fun x => R x - calibrationOne (Real.log n) gaussianLogSquareMean (g t))
    s k (by linarith) hk hsk hcenterMem
    (C * Real.log n * lowerBoundRate p n)
    (mul_nonneg (mul_nonneg hC.le (by linarith)) (by unfold lowerBoundRate; positivity))
    (by simpa only [R, v, q1RawLogDifference] using hEven)
  have hscaledMem := q1RawLogDifference_scale_memLp _ _ _ _ _ v hws hwm
    (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1)
    (fun i => (h₂ f hf hF i).1) σ hσ (ENNReal.ofReal s) hRmem
  refine ⟨?_, ?_⟩
  · change MemLp (q1RawLogDifference (Nat.ceil p - 1) n
      (scaleAverageResolution p n) (optimalLocalBandwidth p n) t)
      (ENNReal.ofReal s) (featureGaussian (fun i => σ • v i))
    exact hscaledMem
  · rw [show scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n)
        (fun i => grid n i.val) = featureGaussian (fun i => σ • v i) by
      rfl]
    change (∫ x, |q1RawLogDifference (Nat.ceil p - 1) n
      (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x -
      calibrationOne (Real.log n) gaussianLogSquareMean (g t)| ^ s
      ∂featureGaussian (fun i => σ • v i)) ≤ _
    rw [q1RawLogDifference_scale_integral _ _ _ _ _ v hws hwm
      (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1)
      (fun i => (h₂ f hf hF i).1) σ hσ
      (fun y => |y - calibrationOne (Real.log n) gaussianLogSquareMean (g t)| ^ s)]
    apply hlow.2.trans
    apply Real.rpow_le_rpow
    · exact mul_nonneg (mul_nonneg hC.le (by linarith))
        (by unfold lowerBoundRate; positivity)
    · nlinarith [mul_nonneg hC.le
        (by unfold lowerBoundRate; positivity : 0 ≤ lowerBoundRate p n)]
    · linarith

theorem hurstHolder_q2_rawMomentBound
    (hBS : BardetSurgailisLemmaOneScalar)
    (p a b M s : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (hs : 2 ≤ s) :
    Q2RawMomentBound p a b M s := by
  let k := Nat.ceil s
  have hk : 1 ≤ k := by
    have : 0 < k := Nat.ceil_pos.mpr (by linarith : 0 < s)
    omega
  have hsk : s ≤ ((2 * k : ℕ) : ℝ) := by
    have hc : s ≤ (k : ℝ) := by simpa only [k] using Nat.le_ceil s
    have hkR : 0 ≤ (k : ℝ) := by positivity
    norm_num at hc ⊢
    linarith
  obtain ⟨C, hC, N₀, hN₀, heven⟩ :=
    hurstHolder_q2_optimal_raw_evenMoment hBS k hk p a b M hp ha hb hab hM
  obtain ⟨N₁, hN₁, D₁, hD₁, hw₁⟩ :=
    localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 2
  obtain ⟨N₂, hN₂, D₂, hD₂, hw₂⟩ :=
    localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 4
  obtain ⟨E₀, _, hm₀⟩ := hurstHolder_grid_second_log_mean
    p a b M hp ha hb hab hM
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_stride_log_mean
    p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ := hurstHolder_common_stride_log_mean
    p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hm₀.and (hm₁.and (hm₂.and
      (optimalLocalBandwidth_eventual_design p (max N₁ N₂) (by linarith)))))
  let N := max N₀ (max K 4)
  refine ⟨C, hC, N, (le_max_right K 4).trans (le_max_right _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgmap, hunitEven⟩ := heven f hf hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro σ hσ n hn t ht
  obtain ⟨h₀, h₁, h₂, hd⟩ := hK n
    ((le_max_left K 4).trans ((le_max_right N₀ _).trans hn))
  obtain ⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩ := hd
  obtain ⟨hm, hmd⟩ := scaleAverageResolution_design p n hδ
  have hws : ∑ i, localPolynomialWeights (Nat.ceil p - 1) n 2
      (optimalLocalBandwidth p n) t i = 1 := by
    have he := (hw₁ n (by omega) (by omega) _ t hδ hδhalf
      ⟨ht.1.le, ht.2.le⟩ ((le_max_left _ _).trans hnd)).2.2.2 0
    simpa using he
  have hwm : ∑ i, averagedLocalWeights (Nat.ceil p - 1) n 4
      (scaleAverageResolution p n) (optimalLocalBandwidth p n) i = 1 := by
    apply averagedLocalWeights_sum _ _ _ _ hm
    intro j
    have hj := grid_mem (scaleAverageResolution p n) j.val hm j.isLt
    have he := (hw₂ n (by omega) (by omega) _ _ hδ hδhalf
      ⟨hj.1.le, hj.2.le⟩ ((le_max_right _ _).trans hnd)).2.2.2 0
    simpa using he
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let R := q2RawLogDifference a b (Nat.ceil p - 1) n
    (scaleAverageResolution p n) (optimalLocalBandwidth p n) t
  have hRmem : MemLp R (ENNReal.ofReal s) (featureGaussian v) :=
    q2RawLogDifference_memLp_finite a b ha hb hab _ _ _ _ _ v
      (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1)
      (fun i => (h₂ f hf hF i).1) s
  have hcenterMem : MemLp (fun x => R x -
      calibrationTwo (Real.log n) gaussianLogSquareMean (g t))
      (ENNReal.ofReal (2 * k : ℝ)) (featureGaussian v) :=
    (q2RawLogDifference_memLp_finite a b ha hb hab _ _ _ _ _ v
      (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1)
      (fun i => (h₂ f hf hF i).1) (2 * k : ℝ)).sub (memLp_const _)
  have hEven := hunitEven n ((le_max_left N₀ _).trans hn) t ⟨ht.1.le, ht.2.le⟩
  have hlow := lower_real_moment_of_even (featureGaussian v)
    (fun x => R x - calibrationTwo (Real.log n) gaussianLogSquareMean (g t))
    s k (by linarith) hk hsk hcenterMem
    (C * Real.log n * lowerBoundRate p n)
    (mul_nonneg (mul_nonneg hC.le (by linarith))
      (by unfold lowerBoundRate; positivity))
    (by simpa only [R, v, q2RawLogDifference] using hEven)
  have hscaledMem := q2RawLogDifference_scale_memLp a b _ _ _ _ _ v hws hwm
    (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1)
    (fun i => (h₂ f hf hF i).1) σ hσ (ENNReal.ofReal s) hRmem
  refine ⟨?_, ?_⟩
  · change MemLp (q2RawLogDifference a b (Nat.ceil p - 1) n
      (scaleAverageResolution p n) (optimalLocalBandwidth p n) t)
      (ENNReal.ofReal s) (featureGaussian (fun i => σ • v i))
    exact hscaledMem
  · rw [show scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n)
        (fun i => grid n i.val) = featureGaussian (fun i => σ • v i) by rfl]
    change (∫ x, |q2RawLogDifference a b (Nat.ceil p - 1) n
      (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x -
      calibrationTwo (Real.log n) gaussianLogSquareMean (g t)| ^ s
      ∂featureGaussian (fun i => σ • v i)) ≤ _
    rw [q2RawLogDifference_scale_integral a b _ _ _ _ _ v hws hwm
      (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1)
      (fun i => (h₂ f hf hF i).1) σ hσ
      (fun y => |y - calibrationTwo (Real.log n) gaussianLogSquareMean (g t)| ^ s)]
    apply hlow.2.trans
    apply Real.rpow_le_rpow
    · exact mul_nonneg (mul_nonneg hC.le (by linarith))
        (by unfold lowerBoundRate; positivity)
    · nlinarith [mul_nonneg hC.le
        (by unfold lowerBoundRate; positivity : 0 ≤ lowerBoundRate p n)]
    · linarith

end Hurst
