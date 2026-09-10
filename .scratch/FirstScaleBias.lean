import Hurst.FirstScale
import Hurst.FirstScaleAlgebra

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_linearScale_bias (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ E ≥ 0, ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n →
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → N₀ ≤ (n:ℝ)*δ → 1 ≤ (m:ℝ)*δ →
      |(∫ x, q1LinearScale r n m δ x ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-gaussianLogSquareMean| ≤
        Real.log n*gridCovarianceError b E n := by
  obtain ⟨Nw,hNw,D,hD,hw⟩ := averagedLocalWeights_uniform_bounds r 2
  obtain ⟨Ns,hNs,Ds,hDs,hws⟩ := localPolynomialWeights_uniform_stability r 2
  obtain ⟨E₁,hE₁,hm₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha (by linarith) hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂,hE₂,hm₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha (by linarith) hab hM (by norm_num) (by norm_num)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hm₁.and hm₂)
  refine ⟨max Nw Ns,lt_of_lt_of_le hNw (le_max_left _ _),(1+1/Real.log 2)*D*(E₁+E₂),by positivity,
    max K 2,le_max_right _ _,?_⟩
  intro n hn hL f hf hF m hm δ hδ hδhalf hnd hmd
  have hn2 : 2 ≤ n := (le_max_right K 2).trans hn
  have hn0 : 0 < n := by omega
  obtain ⟨hm1,hm2⟩ := hK n ((le_max_left K 2).trans hn)
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := averagedLocalWeights r n 2 m δ
  let a₁ := commonFirstStrideCoefficients n 1 2 (by norm_num)
  let a₂ := commonFirstStrideCoefficients n 2 2 (by norm_num)
  let m₁ := fun i => Real.log (‖∑ j,a₁ i j • v j‖^2)+gaussianLogSquareMean
  let m₂ := fun i => Real.log (‖∑ j,a₂ i j • v j‖^2)+gaussianLogSquareMean
  have hz₁ : ∀ i,∑ j,a₁ i j • v j ≠ 0 := fun i => (hm1 f hf hF i).1
  have hz₂ : ∀ i,∑ j,a₂ i j • v j ≠ 0 := fun i => (hm2 f hf hF i).1
  have hG₁ := gaussianLogStatistic_memLp_two v w a₁ hz₁
  have hG₂ := gaussianLogStatistic_memLp_two v w a₂ hz₂
  have hw1 : ∑ i,w i = 1 := by
    apply averagedLocalWeights_sum _ _ _ _ hm
    intro j
    have hj := grid_mem m j.val hm j.isLt
    have he := (hws n hn0 hn2 δ _ hδ hδhalf ⟨hj.1.le,hj.2.le⟩ ((le_max_right _ _).trans hnd)).2.2.2 0
    simpa using he
  have hb₁ : ∀ i,|m₁ i-(gaussianLogSquareMean-2*Real.log n*f (grid n i.val))| ≤ gridCovarianceError b E₁ n := by
    intro i
    have he := (hm1 f hf hF i).2
    simp only [Nat.cast_one,Real.log_one,mul_zero,add_zero] at he
    convert he using 1
    congr 1
    dsimp [m₁,a₁,v]
    ring
  have hb₂ : ∀ i,|m₂ i-(gaussianLogSquareMean-2*Real.log n*f (grid n i.val)+2*Real.log 2*f (grid n i.val))| ≤ gridCovarianceError b E₂ n := by
    intro i
    have he := (hm2 f hf hF i).2
    convert he using 1
    congr 1
    dsimp [m₂,a₂,v]
    norm_num only [Nat.cast_ofNat]
    ring
  have he := firstScale_weighted_bias w (fun i => f (grid n i.val)) m₁ m₂ (Real.log n) gaussianLogSquareMean
    (gridCovarianceError b E₁ n) (gridCovarianceError b E₂ n) hL hw1 hb₁ hb₂
  unfold q1LinearScale linearScaleCombination
  rw [integral_add ((hG₁.integrable one_le_two).const_mul _) ((hG₂.integrable one_le_two).const_mul _),
    integral_const_mul,integral_const_mul,gaussianLogStatistic_expectation v w a₁ hz₁,gaussianLogStatistic_expectation v w a₂ hz₂]
  apply he.trans
  have hwb := (hw n m hn0 hn2 hm δ hδ hδhalf ((le_max_left _ _).trans hnd) hmd).1
  have herr : 0 ≤ gridCovarianceError b E₁ n+gridCovarianceError b E₂ n := by
    unfold gridCovarianceError
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have := Real.log_nonneg (show (1:ℝ) ≤ 2*n by linarith)
    positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwb (show 0 ≤ (1+1/Real.log 2)*Real.log n by positivity)) herr
  exact hh.trans_eq (by unfold gridCovarianceError; ring)

end Hurst
