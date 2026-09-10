import Hurst.StrideLogVariance
import Hurst.FiniteRows

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst

def commonStrideIndex (n d q : ℕ) (hq : 2*d ≤ q) (i : Fin (n-q)) : Fin (n-2*d) :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le_sub_left hq n)⟩

theorem commonStrideIndex_injective (n d q : ℕ) (hq : 2*d ≤ q) :
    Function.Injective (commonStrideIndex n d q hq) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (n-2*d) => x.val) h)

def commonStrideCoefficients (n d q : ℕ) (hq : 2*d ≤ q) (i : Fin (n-q)) : EuclideanSpace ℝ (Fin n) :=
  gridStrideSecondCoefficients n d (commonStrideIndex n d q hq i)

theorem hurstHolder_common_stride_log_variance (p a b M : ℝ) (r d q : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (hd : 0 < d) (hq : 2*d ≤ q) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1/2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n:ℝ)*δ →
      Var[gaussianLogStatistic (localPolynomialWeights r n q δ t) (commonStrideCoefficients n d q hq);
        featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤ C/((n:ℝ)*δ) := by
  obtain ⟨R, hR, hrows⟩ := hurstHolder_grid_stride_second_correlation_rows p a b M hp ha hb hab hM d hd
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_uniform_stability r q
  refine ⟨N₀, hN₀, 4*gaussianLogSquareVariance*(D*D*R), by have := gaussianLogSquareVariance_nonneg; positivity, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop q] with n hrows hn
  intro f hf hF δ t hδ hδhalf ht hN
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  let H := midpointSampleHurst f hf.1 n
  obtain ⟨hzero, hrow⟩ := hrows f hf hF
  have hfeat : ∀ i, ∑ j, commonStrideCoefficients n d q hq i j • gridObservationFeatures n H j ≠ 0 := by
    intro i
    rw [commonStrideCoefficients, gridStrideSecond_feature_identity n d hn0 hd H]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero _)
  obtain ⟨hdet, hmax, hl1, hmom⟩ := hw n hn0 hn δ t hδ hδhalf ht hN
  have hr : ∀ i, (∑ j, featureCorrelation (gridObservationFeatures n H) (commonStrideCoefficients n d q hq i)
      (commonStrideCoefficients n d q hq j)^2) ≤ R := by
    intro i
    simp only [commonStrideCoefficients, gridStrideSecond_correlation_identity n d hn0 hd H]
    exact finite_subfamily_square_rows _ (commonStrideIndex_injective n d q hq) _ R hrow i
  have he := gaussianLogStatistic_variance_row_bound (gridObservationFeatures n H)
    (localPolynomialWeights r n q δ t) (commonStrideCoefficients n d q hq) hfeat
    (D/((n:ℝ)*δ)) D R (by positivity) hR hmax hl1 hr
  exact he.trans_eq (by ring)

end Hurst
