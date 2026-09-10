import Hurst.ActualStrideEvenMoment
import Hurst.MergedWeights

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_stride_first_averaged_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (r d : ℕ) (hd : 0 < d) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |gaussianLogStatistic (averagedLocalWeights r n d m δ)
          (gridStrideFirstCoefficients n d) x -
          (∫ y, gaussianLogStatistic (averagedLocalWeights r n d m δ)
            (gridStrideFirstCoefficients n d) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C / (n : ℝ) ^ k := by
  obtain ⟨N₀, hN₀, Dw, hDw, hw⟩ := averagedLocalWeights_uniform_bounds r d
  obtain ⟨Dm, hDm, hmom⟩ := hurstHolder_stride_first_weighted_evenMoment
    hBS k hk p a b M hp ha hb hab hM d hd
  let C := Dm * (3 * Dw) ^ (2 * k)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨N₀, hN₀, C, hC, ?_⟩
  filter_upwards [hmom, eventually_ge_atTop d] with n hn hdle
  intro f hf hF m hm δ hδ hδhalf hnd hmd
  have hn0 : 0 < n := lt_of_lt_of_le hd hdle
  obtain ⟨_, hmax⟩ := hw n m hn0 hdle hm δ hδ hδhalf hnd hmd
  have hbnd := hn f hf hF (averagedLocalWeights r n d m δ)
    (3 * Dw / (n : ℝ)) (by positivity) hmax
  calc
    _ ≤ Dm * (3 * Dw / (n : ℝ)) ^ (2 * k) * (n - d : ℕ) ^ k := hbnd
    _ ≤ Dm * (3 * Dw / (n : ℝ)) ^ (2 * k) * (n : ℝ) ^ k := by
      gcongr
      exact_mod_cast Nat.sub_le n d
    _ = C / (n : ℝ) ^ k := by
      dsimp only [C]
      have hnR : (n : ℝ) ≠ 0 := by positivity
      rw [div_pow]
      field_simp
      ring

theorem hurstHolder_stride_second_averaged_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (r d : ℕ) (hd : 0 < d) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |gaussianLogStatistic (averagedLocalWeights r n (2 * d) m δ)
          (gridStrideSecondCoefficients n d) x -
          (∫ y, gaussianLogStatistic (averagedLocalWeights r n (2 * d) m δ)
            (gridStrideSecondCoefficients n d) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C / (n : ℝ) ^ k := by
  obtain ⟨N₀, hN₀, Dw, hDw, hw⟩ := averagedLocalWeights_uniform_bounds r (2 * d)
  obtain ⟨Dm, hDm, hmom⟩ := hurstHolder_stride_second_weighted_evenMoment
    hBS k hk p a b M hp ha hb hab hM d hd
  let C := Dm * (3 * Dw) ^ (2 * k)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨N₀, hN₀, C, hC, ?_⟩
  filter_upwards [hmom, eventually_ge_atTop (2 * d)] with n hn hdle
  intro f hf hF m hm δ hδ hδhalf hnd hmd
  have hn0 : 0 < n := lt_of_lt_of_le (by omega : 0 < 2 * d) hdle
  obtain ⟨_, hmax⟩ := hw n m hn0 hdle hm δ hδ hδhalf hnd hmd
  have hbnd := hn f hf hF (averagedLocalWeights r n (2 * d) m δ)
    (3 * Dw / (n : ℝ)) (by positivity) hmax
  calc
    _ ≤ Dm * (3 * Dw / (n : ℝ)) ^ (2 * k) * (n - 2 * d : ℕ) ^ k := hbnd
    _ ≤ Dm * (3 * Dw / (n : ℝ)) ^ (2 * k) * (n : ℝ) ^ k := by
      gcongr
      exact_mod_cast Nat.sub_le n (2 * d)
    _ = C / (n : ℝ) ^ k := by
      dsimp only [C]
      have hnR : (n : ℝ) ≠ 0 := by positivity
      rw [div_pow]
      field_simp
      ring

end Hurst
