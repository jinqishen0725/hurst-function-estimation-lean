import Hurst.UniformFeatureDecayEvenMoment
import Hurst.ActualPointwiseDecay
import Hurst.StrideLogVariance
import Hurst.CommonCutoffCorrelation

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_commonFirstStride_weighted_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (d q : ℕ) (hd : 0 < d) (hdq : d ≤ q) :
    ∃ D > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ (w : Fin (n - q) → ℝ) (W : ℝ), 0 ≤ W → (∀ i, |w i| ≤ W) →
      (∫ x, |gaussianLogStatistic w (commonFirstStrideCoefficients n d q hdq) x -
          (∫ y, gaussianLogStatistic w (commonFirstStrideCoefficients n d q hdq) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        D * W ^ (2 * k) * (n - q : ℕ) ^ k := by
  obtain ⟨A, hA, C, hC, hdecay⟩ :=
    hurstHolder_stride_first_correlation_decay p a b M hp ha hb hab hM d hd
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM d hd
  let ε : ℝ := 1 / (4 * k)
  have hε0 : 0 < ε := by dsimp only [ε]; positivity
  have hε : ε < 1 / (2 * k : ℝ) := by
    dsimp only [ε]
    have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  obtain ⟨D, hD, hmom⟩ := gaussianLogStatistic_uniform_evenMoment_of_decay
    hBS k hk (strideFirstDecay b d) (strideFirstDecay_tendsto_zero b hb d hd)
    (4 * A) (by positivity) ε hε0 hε (ε / 2) le_rfl R hR
  refine ⟨D, hD, ?_⟩
  have herr := (gridCovarianceError_tendsto b C (by linarith)).eventually_le_const
    (show (0 : ℝ) < ε / 8 by positivity)
  filter_upwards [hdecay, hrows, herr, eventually_ge_atTop (q + 1)] with
    n hdec hrow herr hn
  intro f hf hF w W hW0 hw
  let H := midpointSampleHurst f hf.1 n
  have hn0 : 0 < n := by omega
  have hnq : 0 < n - q := by omega
  obtain ⟨hz, hpnt⟩ := hdec f hf hF
  obtain ⟨_, hrw⟩ := hrow f hf hF
  have hfeat := commonFirstStride_feature_nonzero hn0 hd hdq H hz
  have hpnt' : ∀ i j : Fin (n - q),
      |featureCorrelation (gridObservationFeatures n H)
        (commonFirstStrideCoefficients n d q hdq i)
        (commonFirstStrideCoefficients n d q hdq j)| ≤
          4 * A * strideFirstDecay b d (Nat.dist j.val i.val) + ε / 2 := by
    apply commonFirstStride_pointwise hn0 hd hdq H (4 * A) (ε / 2)
      (strideFirstDecay b d)
    intro i j
    exact (hpnt i j).trans (by linarith)
  have hrw' := commonFirstStride_square_rows hn0 hd hdq H R hrw
  exact hmom (n - q) hnq (gridObservationFeatures n H) w
    (commonFirstStrideCoefficients n d q hdq) hfeat hpnt' hrw' W hW0 hw

theorem hurstHolder_commonStride_weighted_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (d q : ℕ) (hd : 0 < d) (hdq : 2 * d ≤ q) :
    ∃ D > 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ (w : Fin (n - q) → ℝ) (W : ℝ), 0 ≤ W → (∀ i, |w i| ≤ W) →
      (∫ x, |gaussianLogStatistic w (commonStrideCoefficients n d q hdq) x -
          (∫ y, gaussianLogStatistic w (commonStrideCoefficients n d q hdq) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))| ^
            (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        D * W ^ (2 * k) * (n - q : ℕ) ^ k := by
  obtain ⟨A, hA, C, hC, hdecay⟩ :=
    hurstHolder_stride_second_correlation_decay p a b M hp ha hb hab hM d hd
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_grid_stride_second_correlation_rows p a b M hp ha hb hab hM d hd
  let ε : ℝ := 1 / (4 * k)
  have hε0 : 0 < ε := by dsimp only [ε]; positivity
  have hε : ε < 1 / (2 * k : ℝ) := by
    dsimp only [ε]
    have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  obtain ⟨D, hD, hmom⟩ := gaussianLogStatistic_uniform_evenMoment_of_decay
    hBS k hk (strideSecondDecay b d) (strideSecondDecay_tendsto_zero b hb d hd)
    A hA ε hε0 hε (ε / 2) le_rfl R hR
  refine ⟨D, hD, ?_⟩
  have ht : 0 < ε / (2 * (A + 1)) := by positivity
  have herr := (gridCovarianceError_tendsto (1 / 2) C (by norm_num)).eventually_le_const ht
  filter_upwards [hdecay, hrows, herr, eventually_ge_atTop (q + 1)] with
    n hdec hrow herr hn
  intro f hf hF w W hW0 hw
  let H := midpointSampleHurst f hf.1 n
  have hn0 : 0 < n := by omega
  have hnq : 0 < n - q := by omega
  obtain ⟨hz, hpnt⟩ := hdec f hf hF
  obtain ⟨_, hrw⟩ := hrow f hf hF
  have hfeat := commonStride_feature_nonzero hn0 hd hdq H hz
  have heA : A * gridCovarianceError (1 / 2) C n ≤ ε / 2 := by
    calc
      A * gridCovarianceError (1 / 2) C n ≤
          A * (ε / (2 * (A + 1))) := mul_le_mul_of_nonneg_left herr hA
      _ ≤ ε / 2 := by
        have hA1 : 0 < A + 1 := by linarith
        have hfrac : A / (A + 1) ≤ 1 := (div_le_one hA1).2 (by linarith)
        rw [show A * (ε / (2 * (A + 1))) = (ε / 2) * (A / (A + 1)) by
          field_simp]
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hfrac (show 0 ≤ ε / 2 by positivity))
  have hpnt' : ∀ i j : Fin (n - q),
      |featureCorrelation (gridObservationFeatures n H)
        (commonStrideCoefficients n d q hdq i)
        (commonStrideCoefficients n d q hdq j)| ≤
          A * strideSecondDecay b d (Nat.dist j.val i.val) + ε / 2 := by
    apply commonStride_pointwise hn0 hd hdq H A (ε / 2) (strideSecondDecay b d)
    intro i j
    exact (hpnt i j).trans (by linarith)
  have hrw' := commonStride_square_rows hn0 hd hdq H R hrw
  exact hmom (n - q) hnq (gridObservationFeatures n H) w
    (commonStrideCoefficients n d q hdq) hfeat hpnt' hrw' W hW0 hw

end Hurst
