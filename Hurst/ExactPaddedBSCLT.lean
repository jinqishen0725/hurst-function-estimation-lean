import Hurst.BardetSurgailisFixedRow
import Hurst.ExactPaddedPolynomialProfile
import Hurst.EventualUniformRows

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace Hurst

set_option maxHeartbeats 800000 in
/-- Internal exact-row application of Bardet--Surgailis Theorem 1(ii).
Every model-specific condition is reduced to a retained variable-row
hypothesis and proved stable under dense independent padding. -/
theorem exactPadded_gaussianLogTruncation_clt
    (hBS : BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0})
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1)
    (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ) (D : ℝ)
    (s : ℕ → ℕ) (K : ℕ) (V : ℝ)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hs : Tendsto s atTop atTop)
    (hfit : ∀ᶠ N in atTop, m (s N) ≤ N)
    (hratio : Tendsto (fun N : ℕ => (m (s N) : ℝ) / (N : ℝ))
      atTop (𝓝 1))
    (hrow : ∃ R ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n),
      ∑ j, |featureCorrelation (u n)
        (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
        (EuclideanSpace.basisFun (Fin (m n)) ℝ j)| ^ 2 ≤ R)
    (htail : ∀ ε > 0, ∃ L : ℕ, ∀ᶠ n : ℕ in atTop,
      (m n : ℝ)⁻¹ * ∑ i : Fin (m n), ∑ j : Fin (m n),
        (if L < Nat.dist i.val j.val then
          |featureCorrelation (u n)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ j)| ^ 2 else 0) ≤ ε)
    (hgUC : UniformContinuous g)
    (hgBound : ∀ x, |g x| ≤ D)
    (hc : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n),
      |c n i - g (((i.val : ℝ) + 1) / m n)| ≤ ε)
    (hactive : Tendsto (fun n : ℕ => (m n : ℝ)⁻¹ *
      ∑ i : Fin (m n), ∑ j : Fin (m n), c n i * c n j *
        gaussianLogTruncationCovariance K
          (featureCorrelation (u n)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ j))) atTop (𝓝 V))
    (hV : 0 < V) :
    TendstoInDistribution (fun N : ℕ => fun x =>
      (Real.sqrt (N : ℝ))⁻¹ *
        gaussianLogTruncationStatistic (exactPaddedFeatureRow m u s N)
          (exactPaddedCoefficientRow m c g s N)
          (fun i => EuclideanSpace.basisFun (Fin N) ℝ i) K x) atTop
      (fun z : ℝ => Real.sqrt V * z)
      (fun N => featureGaussian (exactPaddedFeatureRow m u s N))
      (gaussianReal 0 1) := by
  let v : ∀ N, Fin N → WithLp 2 (E × Lp ℝ 2 (volume : Measure ℝ)) :=
    exactPaddedFeatureRow m u s
  let w : ∀ N, Fin N → ℝ := exactPaddedCoefficientRow m c g s
  let P : ∀ N, Fin N → Polynomial ℝ := fun N i =>
    exactPaddedPolynomialRow m c g s
      (hermiteTruncationPolynomial gaussianLogLp K) N i
  let φ := scalarPolynomialProfile g
    (hermiteTruncationPolynomial gaussianLogLp K)
  have hvnorm : ∀ N i, ‖v N i‖ = 1 :=
    exactPaddedFeatureRow_norm m u hu s
  have hmean : ∀ N i,
      ∫ z : ℝ, (P N i).eval z ∂gaussianReal 0 1 = 0 := by
    intro N i
    exact exactPaddedPolynomialRow_mean_zero m c g s _
      (gaussianLogTruncationPolynomial_mean K) N i
  have hrank : ∀ N i k, k < 2 →
      ∫ z : ℝ, (P N i).eval z * (gaussianHermite k).eval z
        ∂gaussianReal 0 1 = 0 := by
    intro N i k hk
    exact exactPaddedPolynomialRow_hermite_orthogonal m c g s _ 2
      (gaussianLogTruncationPolynomial_hermite_rank_two K) N i k hk
  obtain ⟨R, hR1, hrowR⟩ := hrow
  have hrowExactEv : ∀ᶠ N : ℕ in atTop, ∀ i : Fin N,
      ∑ j, |featureCorrelation (v N)
        (EuclideanSpace.basisFun (Fin N) ℝ i)
        (EuclideanSpace.basisFun (Fin N) ℝ j)| ^ 2 ≤ R := by
    have hrowSel := hrowR.filter_mono hs
    filter_upwards [hfit, hrowSel] with N hN hrowN
    intro i
    have hrowNsq : ∀ k : Fin (m (s N)),
        ∑ j, featureCorrelation (u (s N))
          (EuclideanSpace.basisFun (Fin (m (s N))) ℝ k)
          (EuclideanSpace.basisFun (Fin (m (s N))) ℝ j) ^ 2 ≤ R := by
      intro k
      simpa only [sq_abs] using hrowN k
    simpa only [v, sq_abs] using
      exactPaddedFeatureRow_correlation_square_row_le_of_le
        m u hu s N hN R hR1 hrowNsq i
  have hrowExact : ∃ C ≥ 0, ∀ N i,
      ∑ j, |featureCorrelation (v N)
        (EuclideanSpace.basisFun (Fin N) ℝ i)
        (EuclideanSpace.basisFun (Fin N) ℝ j)| ^ 2 ≤ C := by
    apply exists_uniform_finrow_bound_of_eventually
      (fun N i => ∑ j, |featureCorrelation (v N)
        (EuclideanSpace.basisFun (Fin N) ℝ i)
        (EuclideanSpace.basisFun (Fin N) ℝ j)| ^ 2)
    · intro N i
      positivity
    · exact ⟨R, le_trans (by norm_num) hR1, hrowExactEv⟩
  have htailEv := exactPaddedFeatureRow_correlation_square_average_tail
    m u hu s hm hfit htail hs
  have htailExact : ∀ ε > 0, ∃ L : ℕ, ∀ N : ℕ,
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        (if L < Nat.dist i.val j.val then
          |featureCorrelation (v N)
            (EuclideanSpace.basisFun (Fin N) ℝ i)
            (EuclideanSpace.basisFun (Fin N) ℝ j)| ^ 2 else 0) ≤ ε := by
    exact cutoff_average_tail_all_rows_of_eventually 2
      (fun N i j => featureCorrelation (v N)
        (EuclideanSpace.basisFun (Fin N) ℝ i)
        (EuclideanSpace.basisFun (Fin N) ℝ j)) htailEv
  have hcExact := exactPaddedCoefficientRow_uniform_tendsto
    m c g s hs hm hfit hratio hgUC hc
  have hprofile := exactPaddedPolynomialRow_L2_uniform_tendsto
    m c g s (hermiteTruncationPolynomial gaussianLogLp K) hcExact
  have hvarExact :=
    exactPaddedFeatureRow_normalized_truncation_variance_tendsto
      m u hu c g D s K V hm hs hfit hratio hactive hgBound
  have hvarBS : Tendsto (fun N : ℕ =>
      Var[fun x => (Real.sqrt N)⁻¹ * ∑ i,
        (P N i).eval (standardizedFeatureObservation (v N)
          (EuclideanSpace.basisFun (Fin N) ℝ i) x);
        featureGaussian (v N)]) atTop (𝓝 V) := by
    apply hvarExact.congr'
    filter_upwards with N
    congr 1
    funext x
    rw [exactPaddedPolynomialRow_sum_eq_truncationStatistic m u hu c g s N K]
  have hclt := hBS
    (WithLp 2 (E × Lp ℝ 2 (volume : Measure ℝ))) 2 (by norm_num)
    v P φ V hvnorm hmean hrank hrowExact htailExact
    (scalarPolynomialProfile_memLp g
      (hermiteTruncationPolynomial gaussianLogLp K))
    (scalarPolynomialProfile_centered g
      (hermiteTruncationPolynomial gaussianLogLp K)
      (gaussianLogTruncationPolynomial_mean K))
    (scalarPolynomialProfile_L2_uniformContinuous g
      (hermiteTruncationPolynomial gaussianLogLp K) hgUC)
    hprofile hV hvarBS
  apply TendstoInDistribution.congr
    (X := fun N : ℕ => fun x => (Real.sqrt N)⁻¹ * ∑ i,
      (P N i).eval (standardizedFeatureObservation (v N)
        (EuclideanSpace.basisFun (Fin N) ℝ i) x))
    (Z := fun z : ℝ => Real.sqrt V * z) (μ := fun N => featureGaussian (v N))
    (Y := fun N : ℕ => fun x => (Real.sqrt (N : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (exactPaddedFeatureRow m u s N)
        (exactPaddedCoefficientRow m c g s N)
        (fun i => EuclideanSpace.basisFun (Fin N) ℝ i) K x)
    (T := fun z : ℝ => Real.sqrt V * z)
  · intro N
    filter_upwards with x
    exact congrArg ((Real.sqrt (N : ℝ))⁻¹ * ·)
      (exactPaddedPolynomialRow_sum_eq_truncationStatistic
        m u hu c g s N K x)
  · exact Filter.EventuallyEq.rfl
  · exact hclt

end Hurst
