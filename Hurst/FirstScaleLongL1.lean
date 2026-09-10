import Hurst.FirstScaleLongVariance
import Hurst.FirstScaleLongBias
import Hurst.SecondScaleFineL1

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_logScale_L1_lt_one
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0,
    ∃ A₁ ≥ 1, ∃ C₁ ≥ 0, ∃ D₁ ≥ 0,
    ∃ A₂ ≥ 1, ∃ C₂ ≥ 0, ∃ D₂ ≥ 0,
    ∃ E ≥ 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n →
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      MemLp (q1LogScaleEstimator r n m δ) 2
        (featureGaussian
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      (∫ x, |q1LogScaleEstimator r n m δ x|
        ∂featureGaussian
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        Real.sqrt
          ((4 + 4 / (Real.log 2) ^ 2) * (Real.log n) ^ 2 *
            (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
             D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)) +
        Real.log n * gridCovarianceError b E n := by
  obtain ⟨Nv, hNv, A₁, hA₁, C₁, hC₁, D₁, hD₁,
      A₂, hA₂, C₂, hC₂, D₂, hD₂, Nvn, hNvn, hvar⟩ :=
    hurstHolder_q1_linearScale_variance_lt_one
      p a b M r hp ha hb hab hM
  obtain ⟨Nb, hNb, E, hE, Nbn, hNbn, hbias⟩ :=
    hurstHolder_q1_linearScale_bias_lt_one
      p a b M r hp ha hb hab hM
  let N₀ := max Nv Nb
  let N := max Nvn Nbn
  refine ⟨N₀, lt_of_lt_of_le hNv (le_max_left _ _),
    A₁, hA₁, C₁, hC₁, D₁, hD₁,
    A₂, hA₂, C₂, hC₂, D₂, hD₂,
    E, hE, N, hNvn.trans (le_max_left _ _), ?_⟩
  intro n hn hlog f hf hF m hm δ hδ hδhalf hnd hmd
  have hnv : Nvn ≤ n := (le_max_left Nvn Nbn).trans hn
  have hnb : Nbn ≤ n := (le_max_right Nvn Nbn).trans hn
  have hndv : Nv ≤ (n : ℝ) * δ := (le_max_left Nv Nb).trans hnd
  have hndb : Nb ≤ (n : ℝ) * δ := (le_max_right Nv Nb).trans hnd
  obtain ⟨hXmem, hXvar⟩ :=
    hvar n hnv hlog f hf hF m hm δ hδ hδhalf hndv hmd
  have hXbias := hbias n hnb hlog f hf hF m hm δ hδ hδhalf hndb hmd
  refine ⟨hXmem.sub (memLp_const gaussianLogSquareMean), ?_⟩
  unfold q1LogScaleEstimator
  exact (integral_abs_sub_le_sqrt_variance_add_bias
    (featureGaussian
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
    (q1LinearScale r n m δ) gaussianLogSquareMean hXmem).trans
      (add_le_add (Real.sqrt_le_sqrt hXvar) hXbias)

end Hurst
