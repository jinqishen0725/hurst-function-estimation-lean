import Hurst.CommonStrideMean
import Hurst.PilotTransfer
import Hurst.LocalBias

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst
set_option maxHeartbeats 800000

def q2Pilot (r n : ℕ) (δ t : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  twoScalePilot
    (gaussianLogStatistic (localPolynomialWeights r n 4 δ t) (commonStrideCoefficients n 1 4 (by norm_num)))
    (gaussianLogStatistic (localPolynomialWeights r n 4 δ t) (commonStrideCoefficients n 2 4 (by norm_num)))

/-- Both actual scales share all valid base points and one local design. -/
theorem hurstHolder_q2_pilot_moments (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ B ≥ 0, ∃ E ≥ 0, ∃ V ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧ MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ n : ℕ, N ≤ n → ∀ δ t : ℝ, 0 < δ → δ ≤ 1/2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n:ℝ)*δ →
      MemLp (q2Pilot (Nat.ceil p-1) n δ t) 2 (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      |(∫ x, q2Pilot (Nat.ceil p-1) n δ t x ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-g t| ≤
        B*δ^p + gridCovarianceError (1/2) E n ∧
      Var[q2Pilot (Nat.ceil p-1) n δ t; featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤ V/((n:ℝ)*δ) := by
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p-1) 4
  obtain ⟨Nb, hNb, B, hB, hbias⟩ := hurstHolder_localPolynomial_bias p (by linarith) 4
  obtain ⟨E₁, hE₁, hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, hE₂, hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨Nv₁, hNv₁, V₁, hV₁, hv₁⟩ := hurstHolder_common_stride_log_variance p a b M (Nat.ceil p-1) 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨Nv₂, hNv₂, V₂, hV₂, hv₂⟩ := hurstHolder_common_stride_log_variance p a b M (Nat.ceil p-1) 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hm₁.and (hm₂.and (hv₁.and hv₂)))
  let N₀ := max (max Nw Nb) (max Nv₁ Nv₂)
  have hL : 0 < 2*Real.log 2 := by positivity
  refine ⟨N₀, lt_of_lt_of_le hNw ((le_max_left Nw Nb).trans (le_max_left _ _)), B*(1+M), by positivity,
    D*(E₁+E₂)/(2*Real.log 2), by positivity, (V₁+V₂)/(2*(Real.log 2)^2), by positivity,
    max N 4, le_max_right _ _, ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgb, hbg⟩ := hbias M hM f hf
  refine ⟨g, hg, heq, hgb, ?_⟩
  intro n hn δ t hδ hδhalf ht hnd
  have hn4 : 4 ≤ n := (le_max_right N 4).trans hn
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  obtain ⟨hm1, hm2, hv1, hv2⟩ := hN n ((le_max_left N 4).trans hn)
  let H := midpointSampleHurst f hf.1 n
  let v := gridObservationFeatures n H
  let w := localPolynomialWeights (Nat.ceil p-1) n 4 δ t
  let a₁ := commonStrideCoefficients n 1 4 (by norm_num)
  let a₂ := commonStrideCoefficients n 2 4 (by norm_num)
  have hz₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hm1 f hf hF i).1
  have hz₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hm2 f hf hF i).1
  have hG₁ := gaussianLogStatistic_memLp_two v w a₁ hz₁
  have hG₂ := gaussianLogStatistic_memLp_two v w a₂ hz₂
  refine ⟨twoScalePilot_memLp _ _ _ hG₁ hG₂, ?_, ?_⟩
  · let m₁ := fun i => Real.log (‖∑ j, a₁ i j • v j‖^2)+gaussianLogSquareMean
    let m₂ := fun i => Real.log (‖∑ j, a₂ i j • v j‖^2)+gaussianLogSquareMean
    let base := fun i : Fin (n-4) => -2*f (grid n i.val)*Real.log n + q2LogCorrection (f (grid n i.val))+gaussianLogSquareMean
    have he1 : ∀ i, |m₁ i-base i| ≤ gridCovarianceError (1/2) E₁ n := by
      intro i
      simpa only [Nat.cast_one, Real.log_one, mul_zero, add_zero, m₁, base, a₁, v, H] using (hm1 f hf hF i).2
    have he2 : ∀ i, |m₂ i-(base i+2*Real.log 2*f (grid n i.val))| ≤ gridCovarianceError (1/2) E₂ n := by
      intro i
      convert (hm2 f hf hF i).2 using 1
      congr 1
      dsimp [base, m₂, a₂, v, H]
      ring
    have hwN : Nw ≤ (n:ℝ)*δ := ((le_max_left Nw Nb).trans (le_max_left _ _)).trans hnd
    have hbN : Nb ≤ (n:ℝ)*δ := ((le_max_right Nw Nb).trans (le_max_left _ _)).trans hnd
    have hbi := hbg n hn0 hn4 δ hδ hδhalf hbN t ht
    have hpilot := twoScalePilot_weighted_bias w (fun i => f (grid n i.val)) base m₁ m₂ (g t)
      (gridCovarianceError (1/2) E₁ n) (gridCovarianceError (1/2) E₂ n) (B*(1+M)*δ^p) he1 he2 hbi
    change |(∫ x, twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) x ∂featureGaussian v)-g t| ≤ _
    rw [twoScalePilot_expectation _ _ _ (hG₁.integrable one_le_two) (hG₂.integrable one_le_two),
      gaussianLogStatistic_expectation v w a₂ hz₂, gaussianLogStatistic_expectation v w a₁ hz₁]
    apply hpilot.trans
    have hws := (hw n hn0 hn4 δ t hδ hδhalf ht hwN).2.2.1
    have he0 : 0 ≤ gridCovarianceError (1/2) E₁ n + gridCovarianceError (1/2) E₂ n := by
      unfold gridCovarianceError
      have hh := Real.log_nonneg (show (1:ℝ) ≤ 2*n by linarith)
      positivity
    have hm := (div_le_div_iff_of_pos_right hL).mpr (mul_le_mul_of_nonneg_right hws he0)
    have heq : D*(gridCovarianceError (1/2) E₁ n+gridCovarianceError (1/2) E₂ n)/(2*Real.log 2) =
        gridCovarianceError (1/2) (D*(E₁+E₂)/(2*Real.log 2)) n := by unfold gridCovarianceError; ring
    exact add_le_add le_rfl (hm.trans_eq heq)
  · have hv1N : Nv₁ ≤ (n:ℝ)*δ := ((le_max_left Nv₁ Nv₂).trans (le_max_right _ _)).trans hnd
    have hv2N : Nv₂ ≤ (n:ℝ)*δ := ((le_max_right Nv₁ Nv₂).trans (le_max_right _ _)).trans hnd
    have he1 := hv1 f hf hF δ t hδ hδhalf ht hv1N
    have he2 := hv2 f hf hF δ t hδ hδhalf ht hv2N
    have he := twoScalePilot_variance (featureGaussian v) (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) hG₁ hG₂
    apply he.trans
    have hh := div_le_div_of_nonneg_right (add_le_add he1 he2) (show 0 ≤ 2*(Real.log 2)^2 by positivity)
    exact hh.trans_eq (by ring)

end Hurst
