import Hurst.ActualCommonCutoffEvenMoment
import Hurst.MergedWeights

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_commonFirstStride_averaged_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (r d q : ℕ) (hd : 0 < d) (hdq : d ≤ q) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |gaussianLogStatistic (averagedLocalWeights r n q m δ)
          (commonFirstStrideCoefficients n d q hdq) x -
          (∫ y, gaussianLogStatistic (averagedLocalWeights r n q m δ)
            (commonFirstStrideCoefficients n d q hdq) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C / (n : ℝ) ^ k := by
  obtain ⟨N₀, hN₀, Dw, hDw, hw⟩ := averagedLocalWeights_uniform_bounds r q
  obtain ⟨Dm, hDm, hmom⟩ := hurstHolder_commonFirstStride_weighted_evenMoment
    hBS k hk p a b M hp ha hb hab hM d q hd hdq
  let C := Dm * (3 * Dw) ^ (2 * k)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨N₀, hN₀, C, hC, ?_⟩
  filter_upwards [hmom, eventually_ge_atTop q] with n hn hqn
  intro f hf hF m hm δ hδ hδhalf hnd hmd
  have hn0 : 0 < n := lt_of_lt_of_le (by omega : 0 < d) (hdq.trans hqn)
  obtain ⟨_, hmax⟩ := hw n m hn0 hqn hm δ hδ hδhalf hnd hmd
  have hbnd := hn f hf hF (averagedLocalWeights r n q m δ)
    (3 * Dw / (n : ℝ)) (by positivity) hmax
  calc
    _ ≤ Dm * (3 * Dw / (n : ℝ)) ^ (2 * k) * (n - q : ℕ) ^ k := hbnd
    _ ≤ Dm * (3 * Dw / (n : ℝ)) ^ (2 * k) * (n : ℝ) ^ k := by
      gcongr
      exact_mod_cast Nat.sub_le n q
    _ = C / (n : ℝ) ^ k := by
      dsimp only [C]
      have hnR : (n : ℝ) ≠ 0 := by positivity
      rw [div_pow]
      field_simp
      ring

theorem hurstHolder_commonStride_averaged_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (r d q : ℕ) (hd : 0 < d) (hdq : 2 * d ≤ q) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      (∫ x, |gaussianLogStatistic (averagedLocalWeights r n q m δ)
          (commonStrideCoefficients n d q hdq) x -
          (∫ y, gaussianLogStatistic (averagedLocalWeights r n q m δ)
            (commonStrideCoefficients n d q hdq) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C / (n : ℝ) ^ k := by
  obtain ⟨N₀, hN₀, Dw, hDw, hw⟩ := averagedLocalWeights_uniform_bounds r q
  obtain ⟨Dm, hDm, hmom⟩ := hurstHolder_commonStride_weighted_evenMoment
    hBS k hk p a b M hp ha hb hab hM d q hd hdq
  let C := Dm * (3 * Dw) ^ (2 * k)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨N₀, hN₀, C, hC, ?_⟩
  filter_upwards [hmom, eventually_ge_atTop q] with n hn hqn
  intro f hf hF m hm δ hδ hδhalf hnd hmd
  have hn0 : 0 < n := lt_of_lt_of_le (by omega : 0 < 2 * d) (hdq.trans hqn)
  obtain ⟨_, hmax⟩ := hw n m hn0 hqn hm δ hδ hδhalf hnd hmd
  have hbnd := hn f hf hF (averagedLocalWeights r n q m δ)
    (3 * Dw / (n : ℝ)) (by positivity) hmax
  calc
    _ ≤ Dm * (3 * Dw / (n : ℝ)) ^ (2 * k) * (n - q : ℕ) ^ k := hbnd
    _ ≤ Dm * (3 * Dw / (n : ℝ)) ^ (2 * k) * (n : ℝ) ^ k := by
      gcongr
      exact_mod_cast Nat.sub_le n q
    _ = C / (n : ℝ) ^ k := by
      dsimp only [C]
      have hnR : (n : ℝ) ≠ 0 := by positivity
      rw [div_pow]
      field_simp
      ring

end Hurst
