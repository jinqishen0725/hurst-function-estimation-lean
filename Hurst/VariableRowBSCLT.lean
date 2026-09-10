import Hurst.ExactPaddedBSCLT
import Hurst.DenseRowSelector
import Hurst.DistributionSubsequence

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem normalized_gaussianLogTruncation_variance_eq_covariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n K : ℕ} (hn : 0 < n) (u : Fin n → E) (hu : ∀ i, ‖u i‖ = 1)
    (c : Fin n → ℝ) :
    Var[fun x => (Real.sqrt (n : ℝ))⁻¹ *
      gaussianLogTruncationStatistic u c
        (fun i => EuclideanSpace.basisFun (Fin n) ℝ i) K x;
      featureGaussian u] =
      (n : ℝ)⁻¹ * ∑ i, ∑ j, c i * c j *
        gaussianLogTruncationCovariance K
          (featureCorrelation u
            (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  have hnz : ∀ i : Fin n, ∑ j,
      (EuclideanSpace.basisFun (Fin n) ℝ i) j • u j ≠ 0 := by
    intro i
    have heq : (∑ j, (EuclideanSpace.basisFun (Fin n) ℝ i) j • u j) = u i := by
      simp [EuclideanSpace.basisFun_apply]
    rw [heq]
    exact norm_ne_zero_iff.mp (by rw [hu i]; norm_num)
  rw [variance_const_mul,
    featureGaussian_logTruncation_variance u c _ hnz K]
  have hnR : (0 : ℝ) ≤ n := by positivity
  rw [inv_pow, Real.sq_sqrt hnR]

set_option maxHeartbeats 1200000 in
/-- Internal variable-row reduction to the exact fixed-row statement of
Bardet--Surgailis Theorem 1(ii).  The proof uses an arbitrary-subsequence
criterion, a strictly increasing row-size subsubsequence, and exact-hit dense
padding. -/
theorem variableRow_gaussianLogTruncation_clt
    (hBS : BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert.{0})
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1)
    (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ) (D : ℝ)
    (K : ℕ) (V : ℝ)
    (hmTop : Tendsto m atTop atTop)
    (hmSucc : Tendsto (fun n : ℕ => (m (n + 1) : ℝ) / (m n : ℝ))
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
    TendstoInDistribution (fun n : ℕ => fun x =>
      (Real.sqrt (m n : ℝ))⁻¹ * gaussianLogTruncationStatistic
        (u n) (c n) (fun i => EuclideanSpace.basisFun (Fin (m n)) ℝ i) K x)
      atTop (fun z : ℝ => Real.sqrt V * z)
      (fun n => featureGaussian (u n)) (gaussianReal 0 1) := by
  let X : ∀ n, EuclideanSpace ℝ (Fin (m n)) → ℝ := fun n x =>
    (Real.sqrt (m n : ℝ))⁻¹ * gaussianLogTruncationStatistic
      (u n) (c n) (fun i => EuclideanSpace.basisFun (Fin (m n)) ℝ i) K x
  have hX : ∀ n, AEMeasurable (X n) (featureGaussian (u n)) := by
    intro n
    exact (gaussianLogTruncationStatistic_memLp_two (u n) (c n)
      (fun i => EuclideanSpace.basisFun (Fin (m n)) ℝ i) K).1.const_mul
        (Real.sqrt (m n : ℝ))⁻¹ |>.aemeasurable
  have hZ : AEMeasurable (fun z : ℝ => Real.sqrt V * z)
      (gaussianReal 0 1) := by fun_prop
  apply tendstoInDistribution_of_every_subsequence
    (fun n => EuclideanSpace ℝ (Fin (m n)))
    (fun n => featureGaussian (u n)) X
    (fun z : ℝ => Real.sqrt V * z) (gaussianReal 0 1) hX hZ
  intro ns hns
  obtain ⟨ms, hms, hR⟩ :=
    exists_strictMono_rowSize_subsequence m ns hmTop hns
  let source : ℕ → ℕ := fun k => ns (ms k)
  let R : ℕ → ℕ := fun k => m (source k)
  let dense : ℕ → ℕ := denseRowSelector m hmTop
  let s : ℕ → ℕ := overrideDenseSelector R source dense
  have hsource : Tendsto source atTop atTop := hns.comp hms.tendsto_atTop
  have hdense : Tendsto dense atTop atTop := denseRowSelector_tendsto_atTop m hmTop
  have hdenseFit : ∀ᶠ N : ℕ in atTop, m (dense N) ≤ N :=
    denseRowSelector_eventually_le m hmTop
  have hdenseRatio : Tendsto (fun N : ℕ => (m (dense N) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := denseRowSelector_size_ratio_tendsto_one m hmTop hmSucc
  have hs : Tendsto s atTop atTop :=
    overrideDenseSelector_tendsto_atTop R source dense hR hsource hdense
  have hfit : ∀ᶠ N : ℕ in atTop, m (s N) ≤ N := by
    exact overrideDenseSelector_eventually_fits m R source dense
      (fun _ => rfl) hdenseFit
  have hratio : Tendsto (fun N : ℕ => (m (s N) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
    exact overrideDenseSelector_size_ratio_tendsto_one m R source dense
      (fun _ => rfl) hdenseRatio
  have hmPos : ∀ᶠ n : ℕ in atTop, 0 < m n := hmTop.eventually_gt_atTop 0
  have hExact := exactPadded_gaussianLogTruncation_clt hBS
    m u hu c g D s K V hmPos hs hfit hratio hrow htail
    hgUC hgBound hc hactive hV
  refine ⟨ms, ?_⟩
  apply tendstoInDistribution_of_identDistrib_exactRows
    (fun k => EuclideanSpace ℝ (Fin (m (source k))))
    (fun k => featureGaussian (u (source k)))
    (fun k x => (Real.sqrt (m (source k) : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (u (source k)) (c (source k))
        (fun i => EuclideanSpace.basisFun (Fin (m (source k))) ℝ i) K x)
    (fun N => EuclideanSpace ℝ (Fin N))
    (fun N => featureGaussian (exactPaddedFeatureRow m u s N))
    (fun N x => (Real.sqrt (N : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (exactPaddedFeatureRow m u s N)
        (exactPaddedCoefficientRow m c g s N)
        (fun i => EuclideanSpace.basisFun (Fin N) ℝ i) K x)
    (fun z : ℝ => Real.sqrt V * z) (gaussianReal 0 1)
    R hR.tendsto_atTop hExact
  intro k
  exact exactPaddedFeatureRow_identDistrib_at_override_hit
    m u hu c g source dense hR k K

end Hurst
