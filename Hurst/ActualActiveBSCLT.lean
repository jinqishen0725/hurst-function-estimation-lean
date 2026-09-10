import Hurst.ActualActiveFiniteCLT
import Hurst.VariableRowBSCLT
import Hurst.SafeStandardizedFeatureRow
import Hurst.ActiveBSApplicability
import Hurst.ActiveStatisticLaw
import Hurst.ActiveCorrelationTail
import Hurst.ActualFullTruncatedVarianceLimit
import Hurst.OptimalActiveRowDensity
import Hurst.DistributionVaryingLawTransfer
import Hurst.ShortMemoryVariancePositive
import Hurst.ExactPaddedPolynomialProfile

/-!
# Actual active-row finite-Hermite CLT

This module replaces the internal premise
`WeightedFiniteHermiteTriangularCLT` of the q = 1 and q = 2 finite-Hermite
central limit theorems by an actual instantiation of the generic variable-row
Bardet--Surgailis reduction `variableRow_gaussianLogTruncation_clt`, whose only
probability premise is the exact external theorem
`BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0}`.

Three bridges are combined:

* a law bridge (`gaussianLogTruncationStatistic_activeBS_safe_identDistrib`)
  identifying the actual statistic with the safe active-row statistic whose
  unit-norm row is the `safeStandardizedFeatureRow` reindexing of the active
  window;
* the deterministic profile bridge (`hcProf` below) given by
  `localPolynomialWeights_active_bsCoefficient_uniform_tendsto`;
* the variance bridge (`hactive` below) given by
  `hurstHolder_stride_first_full_truncatedVariance_tendsto` together with the
  exact normalized-variance covariance identity.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace Hurst

section GeneralHelpers

variable {ι F : Type*} {Omega Psi : ι → Type*}

/-- Convergence in distribution is unchanged by rowwise replacement with an
identically distributed variable along an eventually defined rowwise
`IdentDistrib`, even when both row probability spaces vary.  Measurability of
the source rows is needed at every index because `TendstoInDistribution`
records it for all indices. -/
theorem tendstoInDistribution_of_eventual_identDistrib_rows_varying
    [∀ i, MeasurableSpace (Omega i)] [∀ i, MeasurableSpace (Psi i)]
    (P : ∀ i, Measure (Omega i)) [∀ i, IsProbabilityMeasure (P i)]
    (nu : ∀ i, Measure (Psi i)) [∀ i, IsProbabilityMeasure (nu i)]
    {Omega' : Type*} [MeasurableSpace Omega'] (P' : Measure Omega')
    [IsProbabilityMeasure P']
    [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    (X : ∀ i, Omega i → F) (Y : ∀ i, Psi i → F)
    (Z : Omega' → F) (l : Filter ι)
    (hX : ∀ i, AEMeasurable (X i) (P i))
    (hXY : ∀ᶠ i in l, IdentDistrib (X i) (Y i) (P i) (nu i))
    (hY : TendstoInDistribution Y l Z nu P') :
    TendstoInDistribution X l Z P P' where
  forall_aemeasurable := hX
  aemeasurable_limit := hY.aemeasurable_limit
  tendsto := by
    refine (tendsto_congr' ?_).mpr hY.tendsto
    filter_upwards [hXY] with i hi
    exact Subtype.ext hi.map_eq

/-- The constant zero sequence converges in distribution to the constant zero
limit along any family of probability spaces.  This disposes of the finitely
truncated log statistics whose Hermite rank-two truncation is identically
zero. -/
theorem tendstoInDistribution_const_zero
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (P : ∀ n, Measure (Omega n)) [∀ n, IsProbabilityMeasure (P n)] :
    TendstoInDistribution (fun (n : ℕ) (_ : Omega n) => (0 : ℝ)) atTop
      (fun z : ℝ => Real.sqrt 0 * z) P (gaussianReal 0 1) := by
  have hX : ∀ n : ℕ,
      (P n).map (fun _ : Omega n => (0 : ℝ)) =
        (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt 0 * z) := by
    intro n
    have hf : (fun z : ℝ => Real.sqrt 0 * z) = fun _ => (0 : ℝ) := by
      funext z
      simp
    rw [hf, Measure.map_const, Measure.map_const,
      IsProbabilityMeasure.measure_univ, IsProbabilityMeasure.measure_univ]
  refine ⟨fun n => measurable_const.aemeasurable,
    (by
      have hz : (fun z : ℝ => Real.sqrt 0 * z) = fun _ => (0 : ℝ) := by
        funext z
        simp
      rw [hz]
      exact measurable_const.aemeasurable), ?_⟩
  refine (tendsto_congr' ?_).mpr tendsto_const_nhds
  exact Eventually.of_forall fun n => Subtype.ext (hX n)

end GeneralHelpers

/-- The scalar coefficient profile of the active-row B&S normalization:
`sqrt 2` times the equivalent kernel evaluated at the centered rank
coordinate. -/
def activeBSProfileFunction (r : ℕ) (τ : ℝ) : ℝ :=
  Real.sqrt 2 * equivalentKernel r (2 * τ - 1)

theorem uniformContinuous_activeBSProfileFunction (r : ℕ) :
    UniformContinuous (activeBSProfileFunction r) := by
  have hker : UniformContinuous (equivalentKernel r) :=
    (equivalentKernel_compactSupport r).uniformContinuous_of_continuous
      (equivalentKernel_continuous r)
  have haff : UniformContinuous (fun τ : ℝ => 2 * τ - 1) := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    refine ⟨ε / 2, half_pos hε, ?_⟩
    intro x y hxy
    have hdist : dist (2 * x - 1) (2 * y - 1) = 2 * dist x y := by
      rw [Real.dist_eq, Real.dist_eq,
        show (2 * x - 1) - (2 * y - 1) = 2 * (x - y) from by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hdist]
    calc 2 * dist x y < 2 * (ε / 2) :=
            mul_lt_mul_of_pos_left hxy (by norm_num : (0 : ℝ) < 2)
      _ = ε := by ring
  have hsmul : UniformContinuous (fun x : ℝ => Real.sqrt 2 * x) := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    refine ⟨ε / Real.sqrt 2, div_pos hε hsq, ?_⟩
    intro x y hxy
    have hdist : dist (Real.sqrt 2 * x) (Real.sqrt 2 * y) =
        Real.sqrt 2 * dist x y := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hsq.le]
    rw [hdist]
    calc Real.sqrt 2 * dist x y < Real.sqrt 2 * (ε / Real.sqrt 2) :=
            mul_lt_mul_of_pos_left hxy hsq
      _ = ε := by field_simp
  exact hsmul.comp (hker.comp haff)

theorem activeBSProfileFunction_bounded (r : ℕ) :
    ∃ D ≥ 0, ∀ x, |activeBSProfileFunction r x| ≤ D := by
  obtain ⟨D, hD, hker⟩ := equivalentKernel_bounded r
  refine ⟨Real.sqrt 2 * D, mul_nonneg (Real.sqrt_nonneg _) hD, ?_⟩
  intro x
  dsimp only [activeBSProfileFunction]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hker _) (Real.sqrt_nonneg _)

/-- The Hermite truncation of the Gaussian log at orders `0` and `1` vanishes
because the log has Hermite rank two. -/
theorem hermiteTruncationPolynomial_gaussianLogLp_eq_zero_of_le_two
    (M : ℕ) (hM : M ≤ 2) :
    hermiteTruncationPolynomial gaussianLogLp M = 0 := by
  unfold hermiteTruncationPolynomial
  apply Finset.sum_eq_zero
  intro n hn
  have hlt : n < M := Finset.mem_range.mp hn
  have h2 : n = 0 ∨ n = 1 := by omega
  rcases h2 with hn0 | hn1
  · subst n
    rw [gaussianLog_hermite_coefficient_zero, zero_mul, zero_smul]
  · subst n
    rw [gaussianLog_hermite_coefficient_odd 1 (by decide), zero_mul, zero_smul]

/-- The truncated log covariance vanishes at truncations `0` and `1`. -/
theorem gaussianLogTruncationCovariance_eq_zero_of_le_two
    (M : ℕ) (hM : M ≤ 2) (ρ : ℝ) :
    gaussianLogTruncationCovariance M ρ = 0 := by
  unfold gaussianLogTruncationCovariance
  apply Finset.sum_eq_zero
  intro n hn
  have hlt : n < M := Finset.mem_range.mp hn
  have h2 : n = 0 ∨ n = 1 := by omega
  rcases h2 with hn0 | hn1
  · subst n
    simp only [gaussianLogHermiteCoefficient, gaussianLog_hermite_coefficient_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, pow_zero]
  · subst n
    simp only [gaussianLogHermiteCoefficient, gaussianLog_hermite_coefficient_odd 1 (by decide),
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, pow_one]

/-- A finite Hermite log statistic whose truncation order is at most two is
the zero function. -/
theorem gaussianLogTruncationStatistic_eq_zero_of_le_two
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (M : ℕ) (hM : M ≤ 2) :
    gaussianLogTruncationStatistic v w a M = fun _ => 0 := by
  have hp := hermiteTruncationPolynomial_gaussianLogLp_eq_zero_of_le_two M hM
  unfold gaussianLogTruncationStatistic
  rw [hp]
  funext x
  simp

/-- Law bridge: the normalized local-polynomial log statistic of the original
features is identically distributed to the B&S-normalized active-row statistic
under the safe active row. -/
theorem gaussianLogTruncationStatistic_activeBS_safe_identDistrib
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n q M : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (v : Fin n → E)
    (a : Fin (n - q) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) :
    IdentDistrib
      (fun x => Real.sqrt ((n : ℝ) * δ) *
        gaussianLogTruncationStatistic v
          (localPolynomialWeights r n q δ t) a M x)
      (fun x => (Real.sqrt ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
        gaussianLogTruncationStatistic (safeActiveFeatureRow n q δ t v a)
          (activeBSCoefficient r n q δ t)
          (fun i => EuclideanSpace.basisFun
            (Fin (localWeightActiveSet n q δ t).card) ℝ i) M x)
      (featureGaussian v)
      (featureGaussian (safeActiveFeatureRow n q δ t v a)) := by
  have hmeas : featureGaussian (safeActiveFeatureRow n q δ t v a) =
      featureGaussian (fun k => standardizedFeatureVector v
        (a (localWeightActiveIndex n q δ t k))) :=
    safeStandardizedFeatureRow_gaussian_eq_of_nonzero v _
      (fun k => ha (localWeightActiveIndex n q δ t k))
  have h1 := gaussianLogTruncationStatistic_activeBS_identDistrib
    r n q M hn δ t hδ hcard v a ha
  have hfun : (fun x => (Real.sqrt
        ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
      ∑ j, (activeBSPolynomial r n q δ t
        (hermiteTruncationPolynomial gaussianLogLp M) j).eval
          (standardizedFeatureObservation
            (fun k => standardizedFeatureVector v
              (a (localWeightActiveIndex n q δ t k)))
            (EuclideanSpace.basisFun
              (Fin (localWeightActiveSet n q δ t).card) ℝ j) x)) =
      (fun x => (Real.sqrt
        ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ *
        gaussianLogTruncationStatistic (safeActiveFeatureRow n q δ t v a)
          (activeBSCoefficient r n q δ t)
          (fun i => EuclideanSpace.basisFun
            (Fin (localWeightActiveSet n q δ t).card) ℝ i) M x) := by
    funext x
    rw [gaussianLogTruncationStatistic_basis_normalized
      (safeActiveFeatureRow n q δ t v a)
      (safeActiveFeatureRow_norm n q δ t v a)]
    apply congrArg ((Real.sqrt
      ((localWeightActiveSet n q δ t).card : ℝ))⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro j _
    rw [standardizedFeatureObservation_basis_normalized _
      (fun k => norm_standardizedFeatureVector v _
        (ha (localWeightActiveIndex n q δ t k)))]
    simp [activeBSPolynomial, activeBSCoefficient]
  rw [hmeas, ← hfun]
  exact h1

set_option maxHeartbeats 1200000 in
/-- **Actual q = 1 finite-Hermite CLT.**  The internal premise
`WeightedFiniteHermiteTriangularCLT` is replaced by the exact external
Bardet--Surgailis theorem plus ordinary bandwidth regularity.  The only
probabilistic premise besides the external theorem is the convergence of the
truncated variance to `V`. -/
theorem hurstHolder_stride_first_finiteHermite_CLT_actual
    (hBS : BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0})
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hSsucc : Tendsto (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) * δ (n + 1)) / ((n : ℝ) * δ n)) atTop (𝓝 1))
    (K : ℕ) (V : ℝ) (hV : 0 < V)
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
  classical
  -- full nondegeneracy and uniform row bound for the stride-first rows
  obtain ⟨R₀, hR₀, hrows⟩ :=
    hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM 1 (by norm_num)
  -- active-window rank tail
  have htailOrig := hurstHolder_stride_first_active_correlation_square_average_tail
    p a b M r hp ha hb hab hM f hf hF t ht δ hδ hδ0 hN
  have hcardPos : ∀ᶠ n : ℕ in atTop,
      0 < (localWeightActiveSet n 1 (δ n) t).card :=
    (localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδ hδ0 hN).1
  have hevent := hrows.and
    (hcardPos.and (hδ.and (eventually_ge_atTop 1)))
  -- variance bridge: the active double covariance sum is the original variance
  have hactive : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ)⁻¹ *
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          activeBSCoefficient r n 1 (δ n) t i * activeBSCoefficient r n 1 (δ n) t j *
            gaussianLogTruncationCovariance K
              (featureCorrelation (safeActiveFeatureRow n 1 (δ n) t
                  (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
                  (gridStrideFirstCoefficients n 1))
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n 1 (δ n) t).card) ℝ i)
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n 1 (δ n) t).card) ℝ j))) atTop (𝓝 V) := by
    refine hvar.congr' ?_
    filter_upwards [hevent] with n hn
    obtain ⟨hPhi, hcard, hnδ, hn1⟩ := hn
    obtain ⟨hzero, hrow⟩ := hPhi f hf hF
    have hn0 : 0 < n := by omega
    have hfull : ∀ i, ∑ j, gridStrideFirstCoefficients n 1 i j •
        gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0 := by
      intro i
      rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
        (midpointSampleHurst f hf.1 n) i]
      exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
    rw [← normalized_gaussianLogTruncation_variance_eq_covariance hcard
      (safeActiveFeatureRow n 1 (δ n) t
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridStrideFirstCoefficients n 1))
      (safeActiveFeatureRow_norm n 1 (δ n) t
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridStrideFirstCoefficients n 1))
      (activeBSCoefficient r n 1 (δ n) t)]
    exact (safeActiveFeatureRow_normalized_variance_eq_original r n 1 K hn0
      (δ n) t hnδ hcard
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1) hfull).symm
  -- row bound for the safe active rows
  have hrowSafe : ∃ R ≥ 1, ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j, |featureCorrelation (safeActiveFeatureRow n 1 (δ n) t
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
            (gridStrideFirstCoefficients n 1))
          (EuclideanSpace.basisFun
            (Fin (localWeightActiveSet n 1 (δ n) t).card) ℝ i)
          (EuclideanSpace.basisFun
            (Fin (localWeightActiveSet n 1 (δ n) t).card) ℝ j)| ^ 2 ≤ R := by
    refine ⟨max R₀ 1, le_max_right _ _, ?_⟩
    filter_upwards [hevent] with n hn
    obtain ⟨hPhi, hcard, hnδ, hn1⟩ := hn
    obtain ⟨hzero, hrow⟩ := hPhi f hf hF
    have hn0 : 0 < n := by omega
    have hfull : ∀ i, ∑ j, gridStrideFirstCoefficients n 1 i j •
        gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0 := by
      intro i
      rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
        (midpointSampleHurst f hf.1 n) i]
      exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
    intro i
    simp only [safeActiveFeatureRow_correlation_of_nonzero n 1 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1) hfull]
    let e : Fin (localWeightActiveSet n 1 (δ n) t).card ↪ Fin (n - 1) :=
      ⟨localWeightActiveIndex n 1 (δ n) t,
        localWeightActiveIndex_injective n 1 (δ n) t⟩
    have hrestrict := featureCorrelation_row_sum_restrict
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1) e i
    refine le_trans hrestrict ?_
    have hsum : (∑ j : Fin (n - 1),
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridStrideFirstCoefficients n 1 (e i))
          (gridStrideFirstCoefficients n 1 j)| ^ 2) =
        ∑ j : Fin (n - 1),
          vectorCorrelation
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) (e i))
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [gridStrideFirst_correlation_identity n 1 hn0 (by norm_num)
        (midpointSampleHurst f hf.1 n), sq_abs]
    rw [hsum]
    exact le_trans (hrow (localWeightActiveIndex n 1 (δ n) t i)) (le_max_left _ _)
  -- long-distance tail for the safe active rows
  have htailSafe : ∀ ε > 0, ∃ L : ℕ, ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ)⁻¹ *
        ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (if L < Nat.dist i.val j.val then
              |featureCorrelation (safeActiveFeatureRow n 1 (δ n) t
                  (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
                  (gridStrideFirstCoefficients n 1))
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n 1 (δ n) t).card) ℝ i)
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n 1 (δ n) t).card) ℝ j)| ^ 2
              else 0) ≤ ε := by
    intro ε hε
    obtain ⟨L, hL⟩ := htailOrig ε hε
    refine ⟨L, ?_⟩
    filter_upwards [hL, hevent] with n hLn hn
    obtain ⟨hPhi, hcard, hnδ, hn1⟩ := hn
    obtain ⟨hzero, hrow⟩ := hPhi f hf hF
    have hn0 : 0 < n := by omega
    have hfull : ∀ i, ∑ j, gridStrideFirstCoefficients n 1 i j •
        gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0 := by
      intro i
      rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
        (midpointSampleHurst f hf.1 n) i]
      exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
    simpa only [safeActiveFeatureRow_correlation_of_nonzero n 1 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1) hfull] using hLn
  -- coefficient profile convergence
  have hcProf : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |activeBSCoefficient r n 1 (δ n) t i -
          activeBSProfileFunction r
            (((i.val : ℝ) + 1) / (localWeightActiveSet n 1 (δ n) t).card)| ≤ ε := by
    intro ε hε
    have hlem := localPolynomialWeights_active_bsCoefficient_uniform_tendsto
      r 1 t ht δ hδ hδ0 hN ε hε
    refine hlem.mono ?_
    intro n hn i
    have hcoord : ((i.val + 1 : ℕ) : ℝ) = (i.val : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [← hcoord]
    exact hn i
  -- the generic variable-row theorem applied to the safe active rows
  obtain ⟨Dk, hDk, hkernel⟩ := activeBSProfileFunction_bounded r
  have hCLT := variableRow_gaussianLogTruncation_clt hBS
    (fun n => (localWeightActiveSet n 1 (δ n) t).card)
    (fun n => safeActiveFeatureRow n 1 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1))
    (fun n i => safeActiveFeatureRow_norm n 1 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1) i)
    (fun n => activeBSCoefficient r n 1 (δ n) t)
    (activeBSProfileFunction r) Dk K V
    (localWeightActiveSet_card_tendsto_atTop 1 t ht δ hδ hδ0 hN)
    (localWeightActiveSet_card_succ_ratio_tendsto_one 1 t ht δ hδ hδ0 hN hSsucc)
    hrowSafe htailSafe (uniformContinuous_activeBSProfileFunction r)
    hkernel hcProf hactive hV
  -- transfer the CLT from the safe active rows back to the actual statistic
  exact tendstoInDistribution_of_eventual_identDistrib_rows_varying
    (P := fun n => featureGaussian
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
    (nu := fun n => featureGaussian (safeActiveFeatureRow n 1 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1)))
    (P' := gaussianReal 0 1)
    (X := fun (n : ℕ) x => Real.sqrt ((n : ℝ) * δ n) * gaussianLogTruncationStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (localPolynomialWeights r n 1 (δ n) t)
      (gridStrideFirstCoefficients n 1) K x)
    (Y := fun (n : ℕ) x => (Real.sqrt
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (safeActiveFeatureRow n 1 (δ n) t
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridStrideFirstCoefficients n 1))
      (activeBSCoefficient r n 1 (δ n) t)
      (fun i => EuclideanSpace.basisFun
        (Fin (localWeightActiveSet n 1 (δ n) t).card) ℝ i) K x)
    (Z := fun z : ℝ => Real.sqrt V * z)
    (l := atTop)
    (hX := fun n =>
      ((gaussianLogTruncationStatistic_memLp_two
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 1 (δ n) t)
        (gridStrideFirstCoefficients n 1) K).1.const_mul
        (Real.sqrt ((n : ℝ) * δ n))).aemeasurable)
    (hXY := by
      filter_upwards [hevent] with n hn
      obtain ⟨hPhi, hcard, hnδ, hn1⟩ := hn
      obtain ⟨hzero, hrow⟩ := hPhi f hf hF
      have hn0 : 0 < n := by omega
      have hfull : ∀ i, ∑ j, gridStrideFirstCoefficients n 1 i j •
          gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0 := by
        intro i
        rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
          (midpointSampleHurst f hf.1 n) i]
        exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
      exact gaussianLogTruncationStatistic_activeBS_safe_identDistrib r n 1 K hn0
        (δ n) t hnδ hcard
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridStrideFirstCoefficients n 1) hfull)
    (hY := hCLT)

set_option maxHeartbeats 1200000 in
/-- **Actual q = 2 finite-Hermite CLT.**  The internal premise
`WeightedFiniteHermiteTriangularCLT` is replaced by the exact external
Bardet--Surgailis theorem plus ordinary bandwidth regularity, throughout the
paper's full compact range `b < 1`. -/
theorem hurstHolder_grid_second_finiteHermite_CLT_actual
    (hBS : BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0})
    (p a b M : ℝ) (r : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hSsucc : Tendsto (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) * δ (n + 1)) / ((n : ℝ) * δ n)) atTop (𝓝 1))
    (K : ℕ) (V : ℝ) (hV : 0 < V)
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
  classical
  -- full nondegeneracy and uniform row bound for the q = 2 rows
  obtain ⟨R₀, hR₀, hrows⟩ :=
    hurstHolder_grid_second_correlation_rows p a b M hp ha hb hab hM
  have htailOrig := hurstHolder_grid_second_active_correlation_square_average_tail
    p a b M r hp ha hb hab hM f hf hF t ht δ hδ hδ0 hN
  have hcardPos : ∀ᶠ n : ℕ in atTop,
      0 < (localWeightActiveSet n 2 (δ n) t).card :=
    (localWeightActiveSet_card_ratio_tendsto_two 2 t ht δ hδ hδ0 hN).1
  have hevent := hrows.and
    (hcardPos.and (hδ.and (eventually_ge_atTop 2)))
  -- variance bridge
  have hactive : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 2 (δ n) t).card : ℝ)⁻¹ *
      ∑ i : Fin (localWeightActiveSet n 2 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 2 (δ n) t).card,
          activeBSCoefficient r n 2 (δ n) t i * activeBSCoefficient r n 2 (δ n) t j *
            gaussianLogTruncationCovariance K
              (featureCorrelation (safeActiveFeatureRow n 2 (δ n) t
                  (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
                  (gridSecondCoefficients n))
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n 2 (δ n) t).card) ℝ i)
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n 2 (δ n) t).card) ℝ j))) atTop (𝓝 V) := by
    refine hvar.congr' ?_
    filter_upwards [hevent] with n hn
    obtain ⟨hPhi, hcard, hnδ, hn2⟩ := hn
    obtain ⟨hzero, hrow⟩ := hPhi f hf hF
    have hn0 : 0 < n := by omega
    have hfull : ∀ i, ∑ j, gridSecondCoefficients n i j •
        gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0 := by
      intro i
      rw [gridSecond_feature_identity n hn0 (midpointSampleHurst f hf.1 n) i]
      exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
    rw [← normalized_gaussianLogTruncation_variance_eq_covariance hcard
      (safeActiveFeatureRow n 2 (δ n) t
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridSecondCoefficients n))
      (safeActiveFeatureRow_norm n 2 (δ n) t
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridSecondCoefficients n))
      (activeBSCoefficient r n 2 (δ n) t)]
    exact (safeActiveFeatureRow_normalized_variance_eq_original r n 2 K hn0
      (δ n) t hnδ hcard
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n) hfull).symm
  -- row bound
  have hrowSafe : ∃ R ≥ 1, ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 2 (δ n) t).card,
        ∑ j, |featureCorrelation (safeActiveFeatureRow n 2 (δ n) t
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
            (gridSecondCoefficients n))
          (EuclideanSpace.basisFun
            (Fin (localWeightActiveSet n 2 (δ n) t).card) ℝ i)
          (EuclideanSpace.basisFun
            (Fin (localWeightActiveSet n 2 (δ n) t).card) ℝ j)| ^ 2 ≤ R := by
    refine ⟨max R₀ 1, le_max_right _ _, ?_⟩
    filter_upwards [hevent] with n hn
    obtain ⟨hPhi, hcard, hnδ, hn2⟩ := hn
    obtain ⟨hzero, hrow⟩ := hPhi f hf hF
    have hn0 : 0 < n := by omega
    have hfull : ∀ i, ∑ j, gridSecondCoefficients n i j •
        gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0 := by
      intro i
      rw [gridSecond_feature_identity n hn0 (midpointSampleHurst f hf.1 n) i]
      exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
    intro i
    simp only [safeActiveFeatureRow_correlation_of_nonzero n 2 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n) hfull]
    let e : Fin (localWeightActiveSet n 2 (δ n) t).card ↪ Fin (n - 2) :=
      ⟨localWeightActiveIndex n 2 (δ n) t,
        localWeightActiveIndex_injective n 2 (δ n) t⟩
    have hrestrict := featureCorrelation_row_sum_restrict
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n) e i
    refine le_trans hrestrict ?_
    have hsum : (∑ j : Fin (n - 2),
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridSecondCoefficients n (e i))
          (gridSecondCoefficients n j)| ^ 2) =
        ∑ j : Fin (n - 2),
          vectorCorrelation
            (gridSecondActual n (midpointSampleHurst f hf.1 n) (e i))
            (gridSecondActual n (midpointSampleHurst f hf.1 n) j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [gridSecond_correlation_identity n hn0 (midpointSampleHurst f hf.1 n), sq_abs]
    rw [hsum]
    exact le_trans (hrow (localWeightActiveIndex n 2 (δ n) t i)) (le_max_left _ _)
  -- long-distance tail
  have htailSafe : ∀ ε > 0, ∃ L : ℕ, ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 2 (δ n) t).card : ℝ)⁻¹ *
        ∑ i : Fin (localWeightActiveSet n 2 (δ n) t).card,
          ∑ j : Fin (localWeightActiveSet n 2 (δ n) t).card,
            (if L < Nat.dist i.val j.val then
              |featureCorrelation (safeActiveFeatureRow n 2 (δ n) t
                  (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
                  (gridSecondCoefficients n))
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n 2 (δ n) t).card) ℝ i)
                (EuclideanSpace.basisFun
                  (Fin (localWeightActiveSet n 2 (δ n) t).card) ℝ j)| ^ 2
              else 0) ≤ ε := by
    intro ε hε
    obtain ⟨L, hL⟩ := htailOrig ε hε
    refine ⟨L, ?_⟩
    filter_upwards [hL, hevent] with n hLn hn
    obtain ⟨hPhi, hcard, hnδ, hn2⟩ := hn
    obtain ⟨hzero, hrow⟩ := hPhi f hf hF
    have hn0 : 0 < n := by omega
    have hfull : ∀ i, ∑ j, gridSecondCoefficients n i j •
        gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0 := by
      intro i
      rw [gridSecond_feature_identity n hn0 (midpointSampleHurst f hf.1 n) i]
      exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
    simpa only [safeActiveFeatureRow_correlation_of_nonzero n 2 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n) hfull] using hLn
  -- coefficient profile convergence
  have hcProf : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 2 (δ n) t).card,
        |activeBSCoefficient r n 2 (δ n) t i -
          activeBSProfileFunction r
            (((i.val : ℝ) + 1) / (localWeightActiveSet n 2 (δ n) t).card)| ≤ ε := by
    intro ε hε
    have hlem := localPolynomialWeights_active_bsCoefficient_uniform_tendsto
      r 2 t ht δ hδ hδ0 hN ε hε
    refine hlem.mono ?_
    intro n hn i
    have hcoord : ((i.val + 1 : ℕ) : ℝ) = (i.val : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [← hcoord]
    exact hn i
  -- the generic variable-row theorem applied to the safe active rows
  obtain ⟨Dk, hDk, hkernel⟩ := activeBSProfileFunction_bounded r
  have hCLT := variableRow_gaussianLogTruncation_clt hBS
    (fun n => (localWeightActiveSet n 2 (δ n) t).card)
    (fun n => safeActiveFeatureRow n 2 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n))
    (fun n i => safeActiveFeatureRow_norm n 2 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n) i)
    (fun n => activeBSCoefficient r n 2 (δ n) t)
    (activeBSProfileFunction r) Dk K V
    (localWeightActiveSet_card_tendsto_atTop 2 t ht δ hδ hδ0 hN)
    (localWeightActiveSet_card_succ_ratio_tendsto_one 2 t ht δ hδ hδ0 hN hSsucc)
    hrowSafe htailSafe (uniformContinuous_activeBSProfileFunction r)
    hkernel hcProf hactive hV
  -- transfer back to the actual statistic
  exact tendstoInDistribution_of_eventual_identDistrib_rows_varying
    (P := fun n => featureGaussian
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
    (nu := fun n => featureGaussian (safeActiveFeatureRow n 2 (δ n) t
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n)))
    (P' := gaussianReal 0 1)
    (X := fun (n : ℕ) x => Real.sqrt ((n : ℝ) * δ n) * gaussianLogTruncationStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (localPolynomialWeights r n 2 (δ n) t) (gridSecondCoefficients n) K x)
    (Y := fun (n : ℕ) x => (Real.sqrt
      ((localWeightActiveSet n 2 (δ n) t).card : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (safeActiveFeatureRow n 2 (δ n) t
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridSecondCoefficients n))
      (activeBSCoefficient r n 2 (δ n) t)
      (fun i => EuclideanSpace.basisFun
        (Fin (localWeightActiveSet n 2 (δ n) t).card) ℝ i) K x)
    (Z := fun z : ℝ => Real.sqrt V * z)
    (l := atTop)
    (hX := fun n =>
      ((gaussianLogTruncationStatistic_memLp_two
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 2 (δ n) t)
        (gridSecondCoefficients n) K).1.const_mul
        (Real.sqrt ((n : ℝ) * δ n))).aemeasurable)
    (hXY := by
      filter_upwards [hevent] with n hn
      obtain ⟨hPhi, hcard, hnδ, hn2⟩ := hn
      obtain ⟨hzero, hrow⟩ := hPhi f hf hF
      have hn0 : 0 < n := by omega
      have hfull : ∀ i, ∑ j, gridSecondCoefficients n i j •
          gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0 := by
        intro i
        rw [gridSecond_feature_identity n hn0 (midpointSampleHurst f hf.1 n) i]
        exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
      exact gaussianLogTruncationStatistic_activeBS_safe_identDistrib r n 2 K hn0
        (δ n) t hnδ hcard
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridSecondCoefficients n) hfull)
    (hY := hCLT)

end Hurst
