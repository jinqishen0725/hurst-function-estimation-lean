import Hurst.ActualConditionalCLT
import Hurst.OptimalMeanLeading

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Bardet--Surgailis, *J. Multivariate Analysis* 114 (2013), Theorem 1(ii),
arXiv:1104.4732v2, specialized to scalar polynomial functions.

The hypotheses are the paper's conditions (3.1), (3.2), (3.5), and (3.6):
uniform covariance-power rows, vanishing average covariance-power tails,
uniform Gaussian-L2 convergence to a continuous function profile, and a
strictly positive variance limit.  Standardization and joint Gaussianity are
supplied here by `featureGaussian` and `standardizedFeatureObservation`.

This definition records the exact external theorem boundary.  It is deliberately
separate from `WeightedFiniteHermiteTriangularCLT`: applying Theorem 1(ii) to a
shrinking local window still requires a Lean reindexing argument and convergence
of the local weight profile to the equivalent kernel. -/
def BardetSurgailisTheoremOnePartTwoScalarPolynomial : Prop :=
  ∀ (m : ℕ) (_hm : 0 < m)
    (v : ∀ n, Fin n → Lp ℂ 2 (volume : Measure ℝ))
    (a : ∀ n, Fin n → EuclideanSpace ℝ (Fin n))
    (P : ∀ n, Fin n → Polynomial ℝ) (V : ℝ),
    (∀ n i, ∑ j, a n i j • v n j ≠ 0) →
    (∀ n i, (∫ z, (P n i).eval z ∂gaussianReal 0 1) = 0) →
    (∀ n i k, k < m →
      (∫ z, (P n i).eval z * (gaussianHermite k).eval z ∂gaussianReal 0 1) = 0) →
    (∃ C ≥ 0, ∀ n i,
      ∑ j, |featureCorrelation (v n) (a n i) (a n j)| ^ m ≤ C) →
    (∀ ε > 0, ∃ K : ℕ, ∀ n : ℕ,
      (n : ℝ)⁻¹ * ∑ i, ∑ j,
        (if K < Nat.dist i.val j.val then
          |featureCorrelation (v n) (a n i) (a n j)| ^ m else 0) ≤ ε) →
    (∃ φ : ℝ → ℝ → ℝ,
      (∀ τ, MemLp (φ τ) 2 (gaussianReal 0 1)) ∧
      (∀ ε > 0, ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |s - t| < η → (∫ z, (φ s z - φ t z) ^ 2 ∂gaussianReal 0 1) ≤ ε) ∧
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i,
        (∫ z, ((P n i).eval z -
          φ (((i.val : ℝ) + 1) / n) z) ^ 2 ∂gaussianReal 0 1) ≤ ε) →
    0 < V →
    Tendsto (fun n : ℕ => Var[fun x => (Real.sqrt n)⁻¹ * ∑ i,
      (P n i).eval (standardizedFeatureObservation (v n) (a n i) x);
        featureGaussian (v n)]) atTop (𝓝 V) →
    TendstoInDistribution (fun n : ℕ => fun x => (Real.sqrt n)⁻¹ * ∑ i,
      (P n i).eval (standardizedFeatureObservation (v n) (a n i) x)) atTop
      (fun z : ℝ => Real.sqrt V * z) (fun n => featureGaussian (v n))
      (gaussianReal 0 1)

/-- A weighted local-array CLT corollary suggested by the connected-diagram
argument, but not literally Theorem 1(ii) of Bardet--Surgailis.  Until the local
window reindexing and equivalent-kernel profile bridge is proved in Lean, this
proposition is an internal supporting statement rather than an external citation. -/
def WeightedFiniteHermiteTriangularCLT : Prop :=
  ∀ (m : ℕ → ℕ)
    (v : ∀ n, Fin n → Lp ℂ 2 (volume : Measure ℝ))
    (w : ∀ n, Fin (m n) → ℝ)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ (Fin n))
    (c : ℕ → ℝ) (K : ℕ) (V : ℝ),
    (∀ᶠ n in atTop, ∀ i, ∑ j, a n i j • v n j ≠ 0) →
    (∃ R ≥ 0, ∀ᶠ n in atTop,
      ∀ i, ∑ j, featureCorrelation (v n) (a n i) (a n j) ^ 2 ≤ R) →
    (∃ C ≥ 0, ∀ᶠ n in atTop,
      (c n) ^ 2 * ∑ i, (w n i) ^ 2 ≤ C) →
    (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, 0 ≤ ε n ∧ ∀ i, |c n * w n i| ≤ ε n) →
    Tendsto (fun n => Var[fun x => c n *
      gaussianLogTruncationStatistic (v n) (w n) (a n) K x;
        featureGaussian (v n)]) atTop (𝓝 V) →
    TendstoInDistribution (fun n x => c n *
      gaussianLogTruncationStatistic (v n) (w n) (a n) K x) atTop
      (fun z : ℝ => Real.sqrt V * z) (fun n => featureGaussian (v n))
      (gaussianReal 0 1)

/-- Every actual local-polynomial weight, after the short-memory normalization,
is bounded by a deterministic envelope tending to zero. -/
theorem localPolynomialWeights_sqrt_envelope (r q : ℕ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∃ D > 0,
      Tendsto (fun n : ℕ => D * (Real.sqrt ((n : ℝ) * δ n))⁻¹) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, 0 ≤ D * (Real.sqrt ((n : ℝ) * δ n))⁻¹ ∧
        ∀ i, |Real.sqrt ((n : ℝ) * δ n) *
          localPolynomialWeights r n q (δ n) t i| ≤
            D * (Real.sqrt ((n : ℝ) * δ n))⁻¹ := by
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_uniform_stability r q
  refine ⟨D, hD, ?_, ?_⟩
  · simpa only [Function.comp_apply, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)).const_mul D
  · filter_upwards [hδ, hδ0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop N₀, eventually_ge_atTop (q + 1)] with n hnδ hnδhalf hnN hnq
    have hn0 : 0 < n := by omega
    have hx : 0 < (n : ℝ) * δ n := mul_pos (by exact_mod_cast hn0) hnδ
    have hs : 0 < Real.sqrt ((n : ℝ) * δ n) := Real.sqrt_pos.mpr hx
    obtain ⟨_, hmax, _, _⟩ := hw n hn0 (by omega) (δ n) t hnδ hnδhalf.le ht hnN
    refine ⟨mul_nonneg hD.le (inv_nonneg.mpr (Real.sqrt_nonneg _)), ?_⟩
    intro i
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt ((n : ℝ) * δ n) * |localPolynomialWeights r n q (δ n) t i|
          ≤ Real.sqrt ((n : ℝ) * δ n) * (D / ((n : ℝ) * δ n)) :=
        mul_le_mul_of_nonneg_left (hmax i) (Real.sqrt_nonneg _)
      _ = D * (Real.sqrt ((n : ℝ) * δ n))⁻¹ := by
        have hxsq : Real.sqrt ((n : ℝ) * δ n) * Real.sqrt ((n : ℝ) * δ n) =
            (n : ℝ) * δ n := Real.mul_self_sqrt hx.le
        have hinv : ((n : ℝ) * δ n)⁻¹ =
            (Real.sqrt ((n : ℝ) * δ n))⁻¹ *
              (Real.sqrt ((n : ℝ) * δ n))⁻¹ := by
          calc
            ((n : ℝ) * δ n)⁻¹ =
                (Real.sqrt ((n : ℝ) * δ n) * Real.sqrt ((n : ℝ) * δ n))⁻¹ :=
              congrArg Inv.inv hxsq.symm
            _ = _ := mul_inv_rev _ _
        rw [div_eq_mul_inv, hinv]
        field_simp [hs.ne']

/-- Actual q=1 finite Hermite statistics at an arbitrary shrinking local
bandwidth satisfy every hypothesis of `WeightedFiniteHermiteTriangularCLT` except the
variance limit itself. -/
theorem hurstHolder_stride_first_finiteHermite_CLT
    (hWeightedCLT : WeightedFiniteHermiteTriangularCLT)
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (K : ℕ) (V : ℝ)
    (hvar : Tendsto (fun (n : ℕ) => Var[fun x => Real.sqrt ((n : ℝ) * δ n) *
      gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 1 (δ n) t)
        (gridStrideFirstCoefficients n 1) K x;
          featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))])
      atTop (𝓝 V)) :
    TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * δ n) * gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 1 (δ n) t)
        (gridStrideFirstCoefficients n 1) K x) atTop
      (fun z : ℝ => Real.sqrt V * z)
      (fun (n : ℕ) => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1) := by
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM 1 (by norm_num)
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_energy r 1
  obtain ⟨E, hE, hEtend, hEenvelope⟩ :=
    localPolynomialWeights_sqrt_envelope r 1 t ht δ hδ hδ0 hN
  apply hWeightedCLT (fun n => n - 1)
    (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => localPolynomialWeights r n 1 (δ n) t)
    (fun n => gridStrideFirstCoefficients n 1)
    (fun n => Real.sqrt ((n : ℝ) * δ n)) K V
  · filter_upwards [hrows, eventually_ge_atTop 1] with n hn hn1
    obtain ⟨hzero, _⟩ := hn f hf hF
    have hn0 : 0 < n := by omega
    intro i
    rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
      (midpointSampleHurst f hf.1 n) i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  · refine ⟨R, hR, ?_⟩
    filter_upwards [hrows, eventually_ge_atTop 1] with n hn hn1
    obtain ⟨_, hrow⟩ := hn f hf hF
    have hn0 : 0 < n := by omega
    intro i
    simpa only [gridStrideFirst_correlation_identity n 1 hn0 (by norm_num)
      (midpointSampleHurst f hf.1 n)] using hrow i
  · refine ⟨D, hD.le, ?_⟩
    filter_upwards [hδ, hδ0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop N₀, eventually_ge_atTop 1] with n hnδ hnδhalf hnN hn1
    have hn0 : 0 < n := by omega
    have he := hw n hn0 (by omega) (δ n) t hnδ hnδhalf.le ht hnN
    rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hnδ.le)]
    exact he
  · exact ⟨fun n => E * (Real.sqrt ((n : ℝ) * δ n))⁻¹, hEtend, hEenvelope⟩
  · exact hvar

/-- Combining the external finite-Hermite CLT with actual q=1 model
verification and the already formalized Hermite-tail transfer. -/
theorem hurstHolder_stride_first_log_CLT_of_weighted_array_CLT
    (hWeightedCLT : WeightedFiniteHermiteTriangularCLT)
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hvar : ∀ K, Tendsto (fun (n : ℕ) => Var[fun x => Real.sqrt ((n : ℝ) * δ n) *
      gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 1 (δ n) t)
        (gridStrideFirstCoefficients n 1) K x;
          featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))])
      atTop (𝓝 (Vk K))) :
    TendstoInDistribution (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * δ n) *
      (gaussianLogStatistic (localPolynomialWeights r n 1 (δ n) t)
          (gridStrideFirstCoefficients n 1) x -
        (∫ y, gaussianLogStatistic (localPolynomialWeights r n 1 (δ n) t)
          (gridStrideFirstCoefficients n 1) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop
      (fun z : ℝ => Real.sqrt V * z)
      (fun (n : ℕ) => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1) := by
  apply hurstHolder_stride_first_CLT_of_polynomial_limits p a b M r hp ha hb hab hM
    f hf hF t ht δ hδ hδ0 hN V Vk hV
  intro K
  exact hurstHolder_stride_first_finiteHermite_CLT hWeightedCLT p a b M r hp ha hb hab hM
    f hf hF t ht δ hδ hδ0 hN K (Vk K) (hvar K)

/-- Actual q=2 finite Hermite statistics satisfy the same external array
conditions throughout the paper's full compact range `b < 1`. -/
theorem hurstHolder_grid_second_finiteHermite_CLT
    (hWeightedCLT : WeightedFiniteHermiteTriangularCLT)
    (p a b M : ℝ) (r : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (K : ℕ) (V : ℝ)
    (hvar : Tendsto (fun (n : ℕ) => Var[fun x => Real.sqrt ((n : ℝ) * δ n) *
      gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 2 (δ n) t) (gridSecondCoefficients n) K x;
          featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))])
      atTop (𝓝 V)) :
    TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * δ n) * gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 2 (δ n) t) (gridSecondCoefficients n) K x) atTop
      (fun z : ℝ => Real.sqrt V * z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1) := by
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_grid_second_correlation_rows p a b M hp ha hb hab hM
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_energy r 2
  obtain ⟨E, hE, hEtend, hEenvelope⟩ :=
    localPolynomialWeights_sqrt_envelope r 2 t ht δ hδ hδ0 hN
  apply hWeightedCLT (fun n => n - 2)
    (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => localPolynomialWeights r n 2 (δ n) t)
    (fun n => gridSecondCoefficients n)
    (fun n => Real.sqrt ((n : ℝ) * δ n)) K V
  · filter_upwards [hrows, eventually_ge_atTop 2] with n hn hn2
    obtain ⟨hzero, _⟩ := hn f hf hF
    have hn0 : 0 < n := by omega
    intro i
    rw [gridSecond_feature_identity n hn0 (midpointSampleHurst f hf.1 n) i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  · refine ⟨R, hR, ?_⟩
    filter_upwards [hrows, eventually_ge_atTop 2] with n hn hn2
    obtain ⟨_, hrow⟩ := hn f hf hF
    have hn0 : 0 < n := by omega
    intro i
    simpa only [gridSecond_correlation_identity n hn0
      (midpointSampleHurst f hf.1 n)] using hrow i
  · refine ⟨D, hD.le, ?_⟩
    filter_upwards [hδ, hδ0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop N₀, eventually_ge_atTop 2] with n hnδ hnδhalf hnN hn2
    have hn0 : 0 < n := by omega
    have he := hw n hn0 (by omega) (δ n) t hnδ hnδhalf.le ht hnN
    rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hnδ.le)]
    exact he
  · exact ⟨fun n => E * (Real.sqrt ((n : ℝ) * δ n))⁻¹, hEtend, hEenvelope⟩
  · exact hvar

theorem hurstHolder_grid_second_log_CLT_of_weighted_array_CLT
    (hWeightedCLT : WeightedFiniteHermiteTriangularCLT)
    (p a b M : ℝ) (r : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hvar : ∀ K, Tendsto (fun (n : ℕ) => Var[fun x => Real.sqrt ((n : ℝ) * δ n) *
      gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 2 (δ n) t) (gridSecondCoefficients n) K x;
          featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))])
      atTop (𝓝 (Vk K))) :
    TendstoInDistribution (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * δ n) *
      (gaussianLogStatistic (localPolynomialWeights r n 2 (δ n) t)
          (gridSecondCoefficients n) x -
        (∫ y, gaussianLogStatistic (localPolynomialWeights r n 2 (δ n) t)
          (gridSecondCoefficients n) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop
      (fun z : ℝ => Real.sqrt V * z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1) := by
  apply hurstHolder_grid_second_CLT_of_polynomial_limits p a b M r hp ha hb hab hM
    f hf hF t ht δ hδ hδ0 hN V Vk hV
  intro K
  exact hurstHolder_grid_second_finiteHermite_CLT hWeightedCLT p a b M r hp ha hb hab hM
    f hf hF t ht δ hδ hδ0 hN K (Vk K) (hvar K)

/-- The preceding reduction specialized to the paper's optimal bandwidth.  No
bandwidth regularity or Gaussian-array applicability condition remains as an
input; only the external CLT principle and the actual truncated variance limits
are exposed. -/
theorem hurstHolder_stride_first_optimal_log_CLT_of_weighted_array_CLT
    (hWeightedCLT : WeightedFiniteHermiteTriangularCLT)
    (a b M : ℝ) (r : ℕ)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass ((r : ℝ) + 1) M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hvar : ∀ K, Tendsto (fun (n : ℕ) => Var[fun x =>
      Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        gaussianLogTruncationStatistic
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
          (gridStrideFirstCoefficients n 1) K x;
        featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))])
      atTop (𝓝 (Vk K))) :
    TendstoInDistribution (fun (n : ℕ) x =>
      Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        (gaussianLogStatistic
            (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
            (gridStrideFirstCoefficients n 1) x -
          (∫ y, gaussianLogStatistic
              (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
              (gridStrideFirstCoefficients n 1) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop
      (fun z : ℝ => Real.sqrt V * z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1) := by
  obtain ⟨hδ, hδ0, hN, _, _⟩ := optimalLocalBandwidth_bias_conditions r b hb
  have hp : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  exact hurstHolder_stride_first_log_CLT_of_weighted_array_CLT hWeightedCLT ((r : ℝ) + 1) a b M r
    hp ha hb hab hM f hf hF t ht (optimalLocalBandwidth ((r : ℝ) + 1))
    hδ hδ0 hN V Vk hV hvar

/-- The q=2 counterpart at the paper's optimal bandwidth. -/
theorem hurstHolder_grid_second_optimal_log_CLT_of_weighted_array_CLT
    (hWeightedCLT : WeightedFiniteHermiteTriangularCLT)
    (a b M : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass ((r : ℝ) + 1) M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hvar : ∀ K, Tendsto (fun (n : ℕ) => Var[fun x =>
      Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        gaussianLogTruncationStatistic
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
          (gridSecondCoefficients n) K x;
        featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))])
      atTop (𝓝 (Vk K))) :
    TendstoInDistribution (fun (n : ℕ) x =>
      Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        (gaussianLogStatistic
            (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
            (gridSecondCoefficients n) x -
          (∫ y, gaussianLogStatistic
              (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
              (gridSecondCoefficients n) y
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop
      (fun z : ℝ => Real.sqrt V * z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1) := by
  obtain ⟨hδ, hδ0, hN, _, _⟩ := optimalLocalBandwidth_bias_conditions r 0 (by norm_num)
  have hp : (2 : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast (show 2 ≤ r + 1 by omega)
  exact hurstHolder_grid_second_log_CLT_of_weighted_array_CLT hWeightedCLT
    ((r : ℝ) + 1) a b M r hp ha hb hab hM f hf hF t ht
    (optimalLocalBandwidth ((r : ℝ) + 1)) hδ hδ0 hN V Vk hV hvar

end Hurst
