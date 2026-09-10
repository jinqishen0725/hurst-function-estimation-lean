import Hurst.ExactPaddedRow
import Hurst.EventualUniformRows

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem exactPaddedFeatureRow_correlation_square_row_sum_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1) (s : ℕ → ℕ)
    (N : ℕ) (h : m (s N) ≤ N) (i : Fin N) :
    (∑ j : Fin N, featureCorrelation (exactPaddedFeatureRow m u s N)
      (EuclideanSpace.basisFun (Fin N) ℝ i)
      (EuclideanSpace.basisFun (Fin N) ℝ j) ^ 2) =
    ∑ j : Fin (m (s N) + (N - m (s N))),
      featureCorrelation (paddedFeatureRow (u (s N)) (N - m (s N)))
        (EuclideanSpace.basisFun _ ℝ
          (finCongr (Nat.add_sub_of_le h).symm i))
        (EuclideanSpace.basisFun _ ℝ j) ^ 2 := by
  let e := finCongr (Nat.add_sub_of_le h).symm
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun x : ℝ => x ^ 2)
    (exactPaddedFeatureRow_correlation_of_le m u hu s N h i j)

theorem exactPaddedFeatureRow_correlation_square_row_le_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1) (s : ℕ → ℕ)
    (N : ℕ) (h : m (s N) ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (hrow : ∀ i, ∑ j, featureCorrelation (u (s N))
      (EuclideanSpace.basisFun (Fin (m (s N))) ℝ i)
      (EuclideanSpace.basisFun (Fin (m (s N))) ℝ j) ^ 2 ≤ R) :
    ∀ i, ∑ j, featureCorrelation (exactPaddedFeatureRow m u s N)
      (EuclideanSpace.basisFun (Fin N) ℝ i)
      (EuclideanSpace.basisFun (Fin N) ℝ j) ^ 2 ≤ R := by
  intro i
  rw [exactPaddedFeatureRow_correlation_square_row_sum_of_le m u hu s N h i]
  exact paddedFeatureRow_correlation_square_row_le
    (u (s N)) (hu (s N)) (N - m (s N)) R hR hrow _

theorem exactPaddedFeatureRow_correlation_tail_sum_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1) (s : ℕ → ℕ)
    (N : ℕ) (h : m (s N) ≤ N) (K : ℕ) :
    (∑ i : Fin N, ∑ j : Fin N,
      if K < Nat.dist i.val j.val then
        |featureCorrelation (exactPaddedFeatureRow m u s N)
          (EuclideanSpace.basisFun (Fin N) ℝ i)
          (EuclideanSpace.basisFun (Fin N) ℝ j)| ^ 2 else 0) =
    ∑ i : Fin (m (s N) + (N - m (s N))),
      ∑ j : Fin (m (s N) + (N - m (s N))),
      if K < Nat.dist i.val j.val then
        |featureCorrelation (paddedFeatureRow (u (s N)) (N - m (s N)))
          (EuclideanSpace.basisFun _ ℝ i)
          (EuclideanSpace.basisFun _ ℝ j)| ^ 2 else 0 := by
  let e := finCongr (Nat.add_sub_of_le h).symm
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  have hc := exactPaddedFeatureRow_correlation_of_le m u hu s N h i j
  simp only [e, finCongr_apply, Fin.val_cast] at hc ⊢
  rw [hc]

theorem exactPaddedFeatureRow_truncationCovariance_sum_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1)
    (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ) (s : ℕ → ℕ)
    (N : ℕ) (h : m (s N) ≤ N) (K : ℕ) :
    (∑ i : Fin N, ∑ j : Fin N,
      exactPaddedCoefficientRow m c g s N i *
        exactPaddedCoefficientRow m c g s N j *
        gaussianLogTruncationCovariance K
          (featureCorrelation (exactPaddedFeatureRow m u s N)
            (EuclideanSpace.basisFun (Fin N) ℝ i)
            (EuclideanSpace.basisFun (Fin N) ℝ j))) =
    ∑ i : Fin (m (s N) + (N - m (s N))),
      ∑ j : Fin (m (s N) + (N - m (s N))),
      paddedCoefficientRow (c (s N)) g (N - m (s N)) i *
        paddedCoefficientRow (c (s N)) g (N - m (s N)) j *
        gaussianLogTruncationCovariance K
          (featureCorrelation (paddedFeatureRow (u (s N)) (N - m (s N)))
            (EuclideanSpace.basisFun _ ℝ i)
            (EuclideanSpace.basisFun _ ℝ j)) := by
  let e := finCongr (Nat.add_sub_of_le h).symm
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [exactPaddedCoefficientRow_of_le m c g s N h,
    exactPaddedCoefficientRow_of_le m c g s N h,
    exactPaddedFeatureRow_correlation_of_le m u hu s N h]

/-- Exact `Fin N` casting changes neither the normalized finite-Hermite
variance nor its target-plus-filler decomposition. -/
theorem exactPaddedFeatureRow_normalized_truncation_variance_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1)
    (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ) (s : ℕ → ℕ)
    (N : ℕ) (h : m (s N) ≤ N) (K : ℕ) :
    Var[fun x => (Real.sqrt (N : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (exactPaddedFeatureRow m u s N)
        (exactPaddedCoefficientRow m c g s N)
        (fun i => EuclideanSpace.basisFun (Fin N) ℝ i) K x;
      featureGaussian (exactPaddedFeatureRow m u s N)] =
    Var[fun x => (Real.sqrt (m (s N) + (N - m (s N)) : ℝ))⁻¹ *
      gaussianLogTruncationStatistic
        (paddedFeatureRow (u (s N)) (N - m (s N)))
        (paddedCoefficientRow (c (s N)) g (N - m (s N)))
        (fun i => EuclideanSpace.basisFun
          (Fin (m (s N) + (N - m (s N)))) ℝ i) K x;
      featureGaussian (paddedFeatureRow (u (s N)) (N - m (s N)))] := by
  have hnz : ∀ i : Fin N,
      ∑ j, (EuclideanSpace.basisFun (Fin N) ℝ i) j •
        exactPaddedFeatureRow m u s N j ≠ 0 := by
    intro i
    have heq : (∑ j, (EuclideanSpace.basisFun (Fin N) ℝ i) j •
        exactPaddedFeatureRow m u s N j) = exactPaddedFeatureRow m u s N i := by
      simp [EuclideanSpace.basisFun_apply]
    rw [heq]
    exact norm_ne_zero_iff.mp (by
      rw [exactPaddedFeatureRow_norm m u hu s N i]
      norm_num)
  have hpnz : ∀ i : Fin (m (s N) + (N - m (s N))),
      ∑ j, (EuclideanSpace.basisFun _ ℝ i) j •
        paddedFeatureRow (u (s N)) (N - m (s N)) j ≠ 0 := by
    intro i
    have heq : (∑ j, (EuclideanSpace.basisFun _ ℝ i) j •
        paddedFeatureRow (u (s N)) (N - m (s N)) j) =
        paddedFeatureRow (u (s N)) (N - m (s N)) i := by
      simp [EuclideanSpace.basisFun_apply]
    rw [heq]
    exact norm_ne_zero_iff.mp (by
      rw [paddedFeatureRow_norm (u (s N)) (hu (s N)) _ i]
      norm_num)
  rw [variance_const_mul,
    featureGaussian_logTruncation_variance _ _ _ hnz K,
    variance_const_mul,
    featureGaussian_logTruncation_variance _ _ _ hpnz K,
    exactPaddedFeatureRow_truncationCovariance_sum_of_le m u hu c g s N h K]
  have hEqR : (N : ℝ) = (m (s N) + (N - m (s N)) : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le h).symm
  rw [hEqR]
  have hmle : (m (s N) : ℝ) ≤
      (m (s N) + (N - m (s N)) : ℕ) := by
    exact_mod_cast Nat.le_add_right (m (s N)) (N - m (s N))
  have hsimplify : (m (s N) : ℝ) +
      (((m (s N) + (N - m (s N)) : ℕ) : ℝ) - (m (s N) : ℝ)) =
      (m (s N) + (N - m (s N)) : ℕ) := by
    linarith
  rw [hsimplify]

/-- Dense exact-row casting preserves the retained-row normalized
finite-Hermite variance limit. -/
theorem exactPaddedFeatureRow_normalized_truncation_variance_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1)
    (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ) (D : ℝ)
    (s : ℕ → ℕ) (K : ℕ) (V : ℝ)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hs : Tendsto s atTop atTop)
    (hfit : ∀ᶠ N in atTop, m (s N) ≤ N)
    (hratio : Tendsto (fun N : ℕ => (m (s N) : ℝ) / (N : ℝ))
      atTop (𝓝 1))
    (hactive : Tendsto (fun n : ℕ => (m n : ℝ)⁻¹ *
      ∑ i : Fin (m n), ∑ j : Fin (m n), c n i * c n j *
        gaussianLogTruncationCovariance K
          (featureCorrelation (u n)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ j))) atTop (𝓝 V))
    (hg : ∀ x, |g x| ≤ D) :
    Tendsto (fun N : ℕ =>
      Var[fun x => (Real.sqrt (N : ℝ))⁻¹ *
        gaussianLogTruncationStatistic (exactPaddedFeatureRow m u s N)
          (exactPaddedCoefficientRow m c g s N)
          (fun i => EuclideanSpace.basisFun (Fin N) ℝ i) K x;
        featureGaussian (exactPaddedFeatureRow m u s N)]) atTop (𝓝 V) := by
  let ms : ℕ → ℕ := fun N => m (s N)
  let d : ℕ → ℕ := fun N => N - ms N
  have hms : ∀ᶠ N in atTop, 0 < ms N := hm.filter_mono hs
  have hratio' : Tendsto (fun N : ℕ =>
      (ms N : ℝ) / (ms N + d N : ℝ)) atTop (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [hfit] with N hN
    dsimp only [ms, d]
    have hEqR : (N : ℝ) = (m (s N) : ℝ) + (N - m (s N) : ℕ) := by
      exact_mod_cast (Nat.add_sub_of_le hN).symm
    rw [hEqR]
  have hactive' : Tendsto (fun N : ℕ => (ms N : ℝ)⁻¹ *
      ∑ i : Fin (ms N), ∑ j : Fin (ms N), c (s N) i * c (s N) j *
        gaussianLogTruncationCovariance K
          (featureCorrelation (u (s N))
            (EuclideanSpace.basisFun (Fin (ms N)) ℝ i)
            (EuclideanSpace.basisFun (Fin (ms N)) ℝ j))) atTop (𝓝 V) := by
    have hc := hactive.comp hs
    change Tendsto (fun N : ℕ => (m (s N) : ℝ)⁻¹ *
      ∑ i : Fin (m (s N)), ∑ j : Fin (m (s N)),
        c (s N) i * c (s N) j * gaussianLogTruncationCovariance K
          (featureCorrelation (u (s N))
            (EuclideanSpace.basisFun (Fin (m (s N))) ℝ i)
            (EuclideanSpace.basisFun (Fin (m (s N))) ℝ j))) atTop (𝓝 V)
    change Tendsto (fun N : ℕ => (m (s N) : ℝ)⁻¹ *
      ∑ i : Fin (m (s N)), ∑ j : Fin (m (s N)),
        c (s N) i * c (s N) j * gaussianLogTruncationCovariance K
          (featureCorrelation (u (s N))
            (EuclideanSpace.basisFun (Fin (m (s N))) ℝ i)
            (EuclideanSpace.basisFun (Fin (m (s N))) ℝ j))) atTop (𝓝 V) at hc
    exact hc
  have hpad := paddedFeatureRow_normalized_truncation_variance_tendsto
    ms d (fun N => u (s N)) (fun N => hu (s N))
    (fun N => c (s N)) g D K V hms hratio' hactive' hg
  apply hpad.congr'
  filter_upwards [hfit] with N hN
  dsimp only [ms, d]
  have he := (exactPaddedFeatureRow_normalized_truncation_variance_of_le
    m u hu c g s N hN K).symm
  convert he using 1
  rw [Nat.cast_sub hN]

theorem exactPaddedFeatureRow_correlation_square_average_tail
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1) (s : ℕ → ℕ)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hfit : ∀ᶠ N in atTop, m (s N) ≤ N)
    (htail : ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (m n : ℝ)⁻¹ * ∑ i : Fin (m n), ∑ j : Fin (m n),
        (if K < Nat.dist i.val j.val then
          |featureCorrelation (u n)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ j)| ^ 2 else 0) ≤ ε)
    (hs : Tendsto s atTop atTop) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ N : ℕ in atTop,
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        (if K < Nat.dist i.val j.val then
          |featureCorrelation (exactPaddedFeatureRow m u s N)
            (EuclideanSpace.basisFun (Fin N) ℝ i)
            (EuclideanSpace.basisFun (Fin N) ℝ j)| ^ 2 else 0) ≤ ε := by
  have hsel : ∀ ε > 0, ∃ K : ℕ, ∀ᶠ N : ℕ in atTop,
      (m (s N) : ℝ)⁻¹ * ∑ i : Fin (m (s N)), ∑ j : Fin (m (s N)),
        (if K < Nat.dist i.val j.val then
          |featureCorrelation (u (s N))
            (EuclideanSpace.basisFun (Fin (m (s N))) ℝ i)
            (EuclideanSpace.basisFun (Fin (m (s N))) ℝ j)| ^ 2 else 0) ≤ ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := htail ε hε
    exact ⟨K, hK.filter_mono hs⟩
  have hpad := paddedFeatureRow_correlation_square_average_tail
    (fun N => m (s N)) (fun N => N - m (s N))
    (fun N => u (s N)) (fun N => hu (s N))
    (hm.filter_mono hs) hsel
  intro ε hε
  obtain ⟨K, hK⟩ := hpad ε hε
  refine ⟨K, ?_⟩
  filter_upwards [hfit, hK] with N hN hKN
  rw [exactPaddedFeatureRow_correlation_tail_sum_of_le m u hu s N hN K]
  have hEqR : (m (s N) : ℝ) + ((N - m (s N) : ℕ) : ℝ) = (N : ℝ) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le hN]
  rw [hEqR] at hKN
  exact hKN

end Hurst
