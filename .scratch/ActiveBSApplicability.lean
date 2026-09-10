import Hurst.ActiveBSPolynomialConditions
import Hurst.ActiveCorrelationTail
import Hurst.FeatureObservationMap

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Restricting a nonnegative correlation row along an injection cannot
increase its sum. -/
theorem featureCorrelation_row_sum_restrict
    {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : ρ → EuclideanSpace ℝ ι)
    (e : κ ↪ ρ) (i : κ) :
    ∑ j : κ, |featureCorrelation v (a (e i)) (a (e j))| ^ 2 ≤
      ∑ j : ρ, |featureCorrelation v (a (e i)) (a j)| ^ 2 := by
  classical
  let T : Finset ρ := Finset.univ.map e
  calc
    ∑ j : κ, |featureCorrelation v (a (e i)) (a (e j))| ^ 2 =
        ∑ j ∈ T, |featureCorrelation v (a (e i)) (a j)| ^ 2 := by
      dsimp only [T]
      rw [Finset.sum_map]
    _ ≤ ∑ j : ρ, |featureCorrelation v (a (e i)) (a j)| ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)

/-- The full finite-Hermite statistic and the active standardized-feature row
are identically distributed.  This removes the ambient source-dimension
issue before invoking a triangular-array CLT. -/
theorem gaussianLogTruncationStatistic_local_active_identDistrib
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ k, ∑ i, a k i • v i ≠ 0) (M : ℕ) :
    IdentDistrib
      (gaussianLogTruncationStatistic v w a M)
      (gaussianLogTruncationStatistic
        (fun k => standardizedFeatureVector v (a k)) w
        (fun k => EuclideanSpace.basisFun κ ℝ k) M)
      (featureGaussian v)
      (featureGaussian (fun k => standardizedFeatureVector v (a k))) :=
  gaussianLogTruncationStatistic_identDistrib_normalizedFeatures v w a ha M

/-- q=1 active rows have nonzero features and a uniform covariance-square
row bound. -/
theorem hurstHolder_stride_first_active_correlation_rows
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (δ : ℕ → ℝ) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop,
      (∀ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ k, gridStrideFirstCoefficients n 1
          (localWeightActiveIndex n 1 (δ n) t j) k •
            gridObservationFeatures n (midpointSampleHurst f hf.1 n) k ≠ 0) ∧
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j, |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridStrideFirstCoefficients n 1
            (localWeightActiveIndex n 1 (δ n) t i))
          (gridStrideFirstCoefficients n 1
            (localWeightActiveIndex n 1 (δ n) t j))| ^ 2 ≤ R := by
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM 1 (by norm_num)
  refine ⟨R, hR, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop 2] with n hn hn2
  obtain ⟨hnonzero, hrow⟩ := hn f hf hF
  have hn0 : 0 < n := by omega
  constructor
  · intro j
    rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
      (midpointSampleHurst f hf.1 n)]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne'
      (hnonzero (localWeightActiveIndex n 1 (δ n) t j))
  · intro i
    let e : Fin (localWeightActiveSet n 1 (δ n) t).card ↪ Fin (n - 1) :=
      ⟨localWeightActiveIndex n 1 (δ n) t,
        localWeightActiveIndex_injective n 1 (δ n) t⟩
    have hsub := featureCorrelation_row_sum_restrict
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1) e i
    change (∑ j,
      |featureCorrelation
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridStrideFirstCoefficients n 1 (e i))
        (gridStrideFirstCoefficients n 1 (e j))| ^ 2) ≤ R
    calc
      _ ≤ ∑ j : Fin (n - 1),
          |featureCorrelation
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
            (gridStrideFirstCoefficients n 1 (e i))
            (gridStrideFirstCoefficients n 1 j)| ^ 2 := hsub
      _ = ∑ j : Fin (n - 1),
          vectorCorrelation
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) (e i))
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [gridStrideFirst_correlation_identity n 1 hn0 (by norm_num)
          (midpointSampleHurst f hf.1 n), sq_abs]
      _ ≤ R := hrow (e i)

/-- q=2 active rows have nonzero features and a uniform covariance-square
row bound. -/
theorem hurstHolder_grid_second_active_correlation_rows
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (δ : ℕ → ℝ) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop,
      (∀ j : Fin (localWeightActiveSet n 2 (δ n) t).card,
        ∑ k, gridSecondCoefficients n
          (localWeightActiveIndex n 2 (δ n) t j) k •
            gridObservationFeatures n (midpointSampleHurst f hf.1 n) k ≠ 0) ∧
      ∀ i : Fin (localWeightActiveSet n 2 (δ n) t).card,
        ∑ j, |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridSecondCoefficients n
            (localWeightActiveIndex n 2 (δ n) t i))
          (gridSecondCoefficients n
            (localWeightActiveIndex n 2 (δ n) t j))| ^ 2 ≤ R := by
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_grid_second_correlation_rows p a b M hp ha hb hab hM
  refine ⟨R, hR, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop 3] with n hn hn3
  obtain ⟨hnonzero, hrow⟩ := hn f hf hF
  have hn0 : 0 < n := by omega
  constructor
  · intro j
    rw [gridSecond_feature_identity n hn0 (midpointSampleHurst f hf.1 n)]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne'
      (hnonzero (localWeightActiveIndex n 2 (δ n) t j))
  · intro i
    let e : Fin (localWeightActiveSet n 2 (δ n) t).card ↪ Fin (n - 2) :=
      ⟨localWeightActiveIndex n 2 (δ n) t,
        localWeightActiveIndex_injective n 2 (δ n) t⟩
    have hsub := featureCorrelation_row_sum_restrict
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n) e i
    change (∑ j,
      |featureCorrelation
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridSecondCoefficients n (e i))
        (gridSecondCoefficients n (e j))| ^ 2) ≤ R
    calc
      _ ≤ ∑ j : Fin (n - 2),
          |featureCorrelation
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
            (gridSecondCoefficients n (e i))
            (gridSecondCoefficients n j)| ^ 2 := hsub
      _ = ∑ j : Fin (n - 2),
          vectorCorrelation
            (gridSecondActual n (midpointSampleHurst f hf.1 n) (e i))
            (gridSecondActual n (midpointSampleHurst f hf.1 n) j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [gridSecond_correlation_identity n hn0
          (midpointSampleHurst f hf.1 n), sq_abs]
      _ ≤ R := hrow (e i)

end Hurst
