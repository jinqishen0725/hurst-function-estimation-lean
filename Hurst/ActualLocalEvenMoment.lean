import Hurst.SupportRestrictedEvenMoment
import Hurst.ActualPointwiseDecay
import Hurst.StrideLogVariance
import Hurst.SecondGridLogVariance
import Hurst.LocalWeightSupport

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_local_first_averaged_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (r : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 →
      N₀ ≤ (n : ℝ) * δ →
      (∫ x, |gaussianLogStatistic (localPolynomialWeights r n 1 δ t)
          (gridDifferenceCoefficients n) x -
          (∫ y, gaussianLogStatistic (localPolynomialWeights r n 1 δ t)
            (gridDifferenceCoefficients n) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C / ((n : ℝ) * δ) ^ k := by
  obtain ⟨A, hA, Cerr, hCerr, hdecay⟩ :=
    hurstHolder_stride_first_correlation_decay p a b M hp ha hb hab hM 1 (by omega)
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM 1 (by omega)
  obtain ⟨N₀, hN₀, W₀, hW₀, hweights⟩ := localPolynomialWeights_uniform_stability r 1
  let ε : ℝ := 1 / (4 * k)
  have hε0 : 0 < ε := by dsimp only [ε]; positivity
  have hε : ε < 1 / (2 * k : ℝ) := by
    dsimp only [ε]
    have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  obtain ⟨Dm, hDm, hmom⟩ := gaussianLogStatistic_uniform_evenMoment_on_support
    hBS k hk (strideFirstDecay b 1) (strideFirstDecay_tendsto_zero b hb 1 (by omega))
    (4 * A) (by positivity) ε hε0 hε (ε / 2) le_rfl R hR
  let C := Dm * W₀ ^ (2 * k) * 3 ^ k
  have hC : 0 < C := by dsimp only [C]; positivity
  let N := max N₀ 1
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ (le_max_left _ _)
  refine ⟨N, hNpos, C, hC, ?_⟩
  have herr := (gridCovarianceError_tendsto b Cerr (by linarith)).eventually_le_const
    (show (0 : ℝ) < ε / 8 by positivity)
  filter_upwards [hdecay, hrows, herr, eventually_ge_atTop 2] with
    n hdec hrow herr hn
  intro f hf hF δ t hδ hδhalf ht hN
  let H := midpointSampleHurst f hf.1 n
  let S := localWeightActiveSet n 1 δ t
  have hn0 : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hz, hpnt⟩ := hdec f hf hF
  obtain ⟨_, hrw⟩ := hrow f hf hF
  obtain ⟨_, hmax, _, _⟩ := hweights n hn0 hn1 δ t hδ hδhalf ht
    ((le_max_left N₀ 1).trans hN)
  have hfeat : ∀ i, ∑ j, gridStrideFirstCoefficients n 1 i j •
      gridObservationFeatures n H j ≠ 0 := by
    intro i
    rw [gridStrideFirst_feature_identity n 1 hn0 (by omega) H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hz i)
  have hpnt' : ∀ i j : Fin (n - 1),
      |featureCorrelation (gridObservationFeatures n H)
        (gridStrideFirstCoefficients n 1 i) (gridStrideFirstCoefficients n 1 j)| ≤
        4 * A * strideFirstDecay b 1 (Nat.dist j.val i.val) + ε / 2 := by
    intro i j
    rw [gridStrideFirst_correlation_identity n 1 hn0 (by omega) H]
    exact (hpnt i j).trans (by linarith)
  have hrw' : ∀ i : Fin (n - 1),
      ∑ j, |featureCorrelation (gridObservationFeatures n H)
        (gridStrideFirstCoefficients n 1 i) (gridStrideFirstCoefficients n 1 j)| ^ 2 ≤ R := by
    intro i
    simpa only [gridStrideFirst_correlation_identity n 1 hn0 (by omega) H, sq_abs] using hrw i
  have hbnd := hmom (n - 1) S (gridObservationFeatures n H)
    (localPolynomialWeights r n 1 δ t) (gridStrideFirstCoefficients n 1)
    hfeat hpnt' hrw' (localPolynomialWeights_zero_outside_activeSet r n 1 δ t)
    (W₀ / ((n : ℝ) * δ)) (by positivity) hmax
  have hcard := localWeightActiveSet_card n 1 hn0 δ t hδ
    ((le_max_right N₀ 1).trans hN)
  have hbase : 0 < (n : ℝ) * δ := by positivity
  simpa only [show gridStrideFirstCoefficients n 1 = gridDifferenceCoefficients n from rfl] using
    hbnd.trans (by
      calc
        Dm * (W₀ / ((n : ℝ) * δ)) ^ (2 * k) * (S.card : ℝ) ^ k ≤
            Dm * (W₀ / ((n : ℝ) * δ)) ^ (2 * k) * (3 * ((n : ℝ) * δ)) ^ k := by
          gcongr
        _ = C / ((n : ℝ) * δ) ^ k := by
          let x : ℝ := (n : ℝ) * δ
          change Dm * (W₀ / x) ^ (2 * k) * (3 * x) ^ k = C / x ^ k
          dsimp only [C]
          rw [show 2 * k = k + k by omega, pow_add, div_pow, mul_pow]
          field_simp [hbase.ne']
          ring)

theorem hurstHolder_local_second_averaged_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (r : ℕ) :
    ∃ N₀ > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 →
      N₀ ≤ (n : ℝ) * δ →
      (∫ x, |gaussianLogStatistic (localPolynomialWeights r n 2 δ t)
          (gridSecondCoefficients n) x -
          (∫ y, gaussianLogStatistic (localPolynomialWeights r n 2 δ t)
            (gridSecondCoefficients n) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        C / ((n : ℝ) * δ) ^ k := by
  obtain ⟨A, hA, Cerr, hCerr, hdecay⟩ :=
    hurstHolder_stride_second_correlation_decay p a b M hp ha hb hab hM 1 (by omega)
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_grid_stride_second_correlation_rows p a b M hp ha hb hab hM 1 (by omega)
  obtain ⟨N₀, hN₀, W₀, hW₀, hweights⟩ := localPolynomialWeights_uniform_stability r 2
  let ε : ℝ := 1 / (4 * k)
  have hε0 : 0 < ε := by dsimp only [ε]; positivity
  have hε : ε < 1 / (2 * k : ℝ) := by
    dsimp only [ε]
    have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  obtain ⟨Dm, hDm, hmom⟩ := gaussianLogStatistic_uniform_evenMoment_on_support
    hBS k hk (strideSecondDecay b 1) (strideSecondDecay_tendsto_zero b hb 1 (by omega))
    A hA ε hε0 hε (ε / 2) le_rfl R hR
  let C := Dm * W₀ ^ (2 * k) * 3 ^ k
  have hC : 0 < C := by dsimp only [C]; positivity
  let N := max N₀ 1
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ (le_max_left _ _)
  refine ⟨N, hNpos, C, hC, ?_⟩
  have htiny : 0 < ε / (2 * (A + 1)) := by positivity
  have herr := (gridCovarianceError_tendsto (1 / 2) Cerr (by norm_num)).eventually_le_const htiny
  filter_upwards [hdecay, hrows, herr, eventually_ge_atTop 3] with
    n hdec hrow herr hn
  intro f hf hF δ t hδ hδhalf ht hN
  let H := midpointSampleHurst f hf.1 n
  let S := localWeightActiveSet n 2 δ t
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hz, hpnt⟩ := hdec f hf hF
  obtain ⟨_, hrw⟩ := hrow f hf hF
  obtain ⟨_, hmax, _, _⟩ := hweights n hn0 hn2 δ t hδ hδhalf ht
    ((le_max_left N₀ 1).trans hN)
  have hfeat : ∀ i, ∑ j, gridStrideSecondCoefficients n 1 i j •
      gridObservationFeatures n H j ≠ 0 := by
    intro i
    rw [gridStrideSecond_feature_identity n 1 hn0 (by omega) H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hz i)
  have heA : A * gridCovarianceError (1 / 2) Cerr n ≤ ε / 2 := by
    calc
      A * gridCovarianceError (1 / 2) Cerr n ≤
          A * (ε / (2 * (A + 1))) := mul_le_mul_of_nonneg_left herr hA
      _ ≤ ε / 2 := by
        have hA1 : 0 < A + 1 := by linarith
        have hfrac : A / (A + 1) ≤ 1 := (div_le_one hA1).2 (by linarith)
        rw [show A * (ε / (2 * (A + 1))) = (ε / 2) * (A / (A + 1)) by
          field_simp]
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hfrac (show 0 ≤ ε / 2 by positivity))
  have hpnt' : ∀ i j : Fin (n - 2),
      |featureCorrelation (gridObservationFeatures n H)
        (gridStrideSecondCoefficients n 1 i) (gridStrideSecondCoefficients n 1 j)| ≤
        A * strideSecondDecay b 1 (Nat.dist j.val i.val) + ε / 2 := by
    intro i j
    rw [gridStrideSecond_correlation_identity n 1 hn0 (by omega) H]
    exact (hpnt i j).trans (by linarith)
  have hrw' : ∀ i : Fin (n - 2),
      ∑ j, |featureCorrelation (gridObservationFeatures n H)
        (gridStrideSecondCoefficients n 1 i) (gridStrideSecondCoefficients n 1 j)| ^ 2 ≤ R := by
    intro i
    simpa only [gridStrideSecond_correlation_identity n 1 hn0 (by omega) H, sq_abs] using hrw i
  have hbnd := hmom (n - 2) S (gridObservationFeatures n H)
    (localPolynomialWeights r n 2 δ t) (gridStrideSecondCoefficients n 1)
    hfeat hpnt' hrw' (localPolynomialWeights_zero_outside_activeSet r n 2 δ t)
    (W₀ / ((n : ℝ) * δ)) (by positivity) hmax
  have hcard := localWeightActiveSet_card n 2 hn0 δ t hδ
    ((le_max_right N₀ 1).trans hN)
  have hbase : 0 < (n : ℝ) * δ := by positivity
  simpa only [show gridStrideSecondCoefficients n 1 = gridSecondCoefficients n from rfl] using
    hbnd.trans (by
      calc
        Dm * (W₀ / ((n : ℝ) * δ)) ^ (2 * k) * (S.card : ℝ) ^ k ≤
            Dm * (W₀ / ((n : ℝ) * δ)) ^ (2 * k) * (3 * ((n : ℝ) * δ)) ^ k := by
          gcongr
        _ = C / ((n : ℝ) * δ) ^ k := by
          let x : ℝ := (n : ℝ) * δ
          change Dm * (W₀ / x) ^ (2 * k) * (3 * x) ^ k = C / x ^ k
          dsimp only [C]
          rw [show 2 * k = k + k by omega, pow_add, div_pow, mul_pow]
          field_simp [hbase.ne']
          ring)

end Hurst
