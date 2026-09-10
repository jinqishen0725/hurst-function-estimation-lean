import Hurst.CommonStrideMean
import Hurst.CompositeLocalBias
import Hurst.SecondMSE

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst
set_option maxHeartbeats 800000

theorem hurstHolder_common_log_bias (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ B ≥ 0, ∃ E ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ g : ℝ → ℝ, Continuous g → EqOn f g (Ioo (0:ℝ) 1) →
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n → ∀ δ t : ℝ, 0 < δ → δ ≤ 1/2 → t ∈ Icc (0:ℝ) 1 → N₀ ≤ (n:ℝ)*δ →
      |(∫ x, gaussianLogStatistic (localPolynomialWeights (Nat.ceil p-1) n 4 δ t) (commonStrideCoefficients n 1 4 (by norm_num)) x
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) -
        (gaussianLogSquareMean-2*Real.log n*g t+q2LogCorrection (g t))| ≤
        B*Real.log n*δ^p+gridCovarianceError (1/2) E n := by
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p-1) 4
  obtain ⟨Nb, hNb, Bh, hBh, hhb⟩ := hurstHolder_localPolynomial_bias_closed p (by linarith) 4
  obtain ⟨Nc, hNc, Bc, hBc, hcb⟩ := hurstHolder_smooth_composite_local_bias p a b M q2LogCorrection 4 hp ha hb hM q2LogCorrection_smooth
  obtain ⟨E, hE, hmean⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmean
  let N₀ := max (max Nw Nb) Nc
  refine ⟨N₀, lt_of_lt_of_le hNw ((le_max_left Nw Nb).trans (le_max_left _ _)),
    2*(Bh*(1+M)+Bc), by positivity, D*E, by positivity, max N 4, le_max_right _ _, ?_⟩
  intro f hf hF g hg heq n hn hL δ t hδ hδhalf ht hnd
  have hn4 : 4 ≤ n := (le_max_right N 4).trans hn
  have hn0 : 0 < n := by omega
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := localPolynomialWeights (Nat.ceil p-1) n 4 δ t
  let a₁ := commonStrideCoefficients n 1 4 (by norm_num)
  let m := fun i => Real.log (‖∑ j, a₁ i j • v j‖^2)+gaussianLogSquareMean
  have hmn := hN n ((le_max_left N 4).trans hn) f hf hF
  have hz : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hmn i).1
  have hwN : Nw ≤ (n:ℝ)*δ := ((le_max_left Nw Nb).trans (le_max_left _ _)).trans hnd
  have hbN : Nb ≤ (n:ℝ)*δ := ((le_max_right Nw Nb).trans (le_max_left _ _)).trans hnd
  have hcN : Nc ≤ (n:ℝ)*δ := (le_max_right _ _).trans hnd
  obtain ⟨hdet, hmax, hsum, hmom⟩ := hw n hn0 hn4 δ t hδ hδhalf ht hwN
  have hw1 : ∑ i, w i = 1 := by simpa using hmom 0
  have hh := hhb M hM f hf g hg heq n hn0 hn4 δ hδ hδhalf hbN t ht
  have hc := hcb f hf hF g hg heq n hn0 hn4 δ hδ hδhalf hcN t ht
  have hm : ∀ i, |m i-(-2*Real.log n*f (grid n i.val)+q2LogCorrection (f (grid n i.val))+gaussianLogSquareMean)| ≤ gridCovarianceError (1/2) E n := by
    intro i
    have he := (hmn i).2
    simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero] at he
    convert he using 1
    congr 1
    dsimp [m, a₁, v]
    ring
  have he0 : 0 ≤ gridCovarianceError (1/2) E n := by
    unfold gridCovarianceError
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hl := Real.log_nonneg (show (1:ℝ) ≤ 2*n by linarith)
    positivity
  have he := weighted_nonlinear_bias_bound w (fun i => f (grid n i.val)) m q2LogCorrection
    (Real.log n) gaussianLogSquareMean (g t)
    (Bh*(1+M)*δ^p) (Bc*δ^p) D (gridCovarianceError (1/2) E n) hL (by positivity) he0 hw1 hsum hh hc hm
  rw [gaussianLogStatistic_expectation v w a₁ hz]
  apply he.trans_eq
  unfold gridCovarianceError
  ring

end Hurst
