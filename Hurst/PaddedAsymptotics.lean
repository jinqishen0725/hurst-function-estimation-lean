import Hurst.PaddedProfile
import Hurst.PaddedCorrelationTail

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Hurst

/-- If the retained part occupies asymptotically all of a padded row, then
the padding fraction vanishes. -/
theorem padding_fraction_tendsto_zero
    (m d : ℕ → ℕ) (hm : ∀ᶠ n in atTop, 0 < m n)
    (hratio : Tendsto (fun n : ℕ => (m n : ℝ) / (m n + d n : ℝ))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (d n : ℝ) / (m n + d n : ℝ))
      atTop (𝓝 0) := by
  have hsub := (tendsto_const_nhds.sub hratio :
    Tendsto (fun n : ℕ => (1 : ℝ) - (m n : ℝ) / (m n + d n : ℝ))
      atTop (𝓝 (1 - 1)))
  norm_num at hsub
  apply hsub.congr'
  filter_upwards [hm] with n hmn
  have hden : (m n + d n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The equivalent padding-to-retained ratio also vanishes.  This is the
coordinate error used by the padded profile theorem. -/
theorem padding_to_retained_ratio_tendsto_zero
    (m d : ℕ → ℕ) (hm : ∀ᶠ n in atTop, 0 < m n)
    (hratio : Tendsto (fun n : ℕ => (m n : ℝ) / (m n + d n : ℝ))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (d n : ℝ) / (m n : ℝ)) atTop (𝓝 0) := by
  have hd := padding_fraction_tendsto_zero m d hm hratio
  have hdiv := hd.div hratio (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at hdiv
  apply hdiv.congr'
  filter_upwards [hm] with n hmn
  have hm0 : (m n : ℝ) ≠ 0 := by positivity
  have hden : (m n + d n : ℝ) ≠ 0 := by positivity
  change ((d n : ℝ) / (m n + d n : ℝ)) /
      ((m n : ℝ) / (m n + d n : ℝ)) = (d n : ℝ) / (m n : ℝ)
  field_simp

/-- A bounded profile contributes asymptotically no normalized variance on a
vanishing right-padding block. -/
theorem padded_profile_square_average_tendsto_zero
    (m d : ℕ → ℕ) (g : ℝ → ℝ) (D : ℝ)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hd : Tendsto (fun n : ℕ => (d n : ℝ) / (m n + d n : ℝ))
      atTop (𝓝 0))
    (hg : ∀ x, |g x| ≤ D) :
    Tendsto (fun n : ℕ => ((m n + d n : ℝ)⁻¹) *
      ∑ i : Fin (d n),
        g ((((m n + i.val : ℕ) : ℝ) + 1) / (m n + d n : ℝ)) ^ 2)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hm] with n hmn
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · filter_upwards [hm] with n hmn
    have hD : 0 ≤ D := (abs_nonneg (g 0)).trans (hg 0)
    have hsum : (∑ i : Fin (d n),
        g ((((m n + i.val : ℕ) : ℝ) + 1) / (m n + d n : ℝ)) ^ 2) ≤
        (d n : ℝ) * D ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin (d n), D ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi := hg ((((m n + i.val : ℕ) : ℝ) + 1) /
            (m n + d n : ℝ))
          rw [sq_le_sq]
          simpa [abs_of_nonneg hD] using hi
        _ = (d n : ℝ) * D ^ 2 := by simp
    calc
      ((m n + d n : ℝ)⁻¹) * ∑ i : Fin (d n),
          g ((((m n + i.val : ℕ) : ℝ) + 1) / (m n + d n : ℝ)) ^ 2 ≤
          ((m n + d n : ℝ)⁻¹) * ((d n : ℝ) * D ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (by positivity))
      _ = ((d n : ℝ) / (m n + d n : ℝ)) * D ^ 2 := by ring
  · simpa using hd.mul_const (D ^ 2)

/-- Elementary asymptotic transfer for the exact target-plus-filler variance
decomposition. -/
theorem normalized_padded_decomposition_tendsto
    (m d : ℕ → ℕ) (A F : ℕ → ℝ) (C V : ℝ)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hratio : Tendsto (fun n : ℕ => (m n : ℝ) / (m n + d n : ℝ))
      atTop (𝓝 1))
    (hA : Tendsto (fun n : ℕ => (m n : ℝ)⁻¹ * A n) atTop (𝓝 V))
    (hF : Tendsto (fun n : ℕ => (m n + d n : ℝ)⁻¹ * F n)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (m n + d n : ℝ)⁻¹ * (A n + C * F n))
      atTop (𝓝 V) := by
  have hfirst : Tendsto (fun n : ℕ =>
      (m n + d n : ℝ)⁻¹ * A n) atTop (𝓝 V) := by
    have hmul := hratio.mul hA
    norm_num at hmul
    apply hmul.congr'
    filter_upwards [hm] with n hmn
    have hm0 : (m n : ℝ) ≠ 0 := by positivity
    have hden : (m n + d n : ℝ) ≠ 0 := by positivity
    field_simp
  have hsecond : Tendsto (fun n : ℕ =>
      (m n + d n : ℝ)⁻¹ * (C * F n)) atTop (𝓝 0) := by
    have h := hF.const_mul C
    norm_num at h
    convert h using 1
    funext n
    ring
  convert hfirst.add hsecond using 1
  · funext n
    ring
  · ring

/-- The exact variance of a densely padded finite-Hermite row has the same
limit as the retained active row.  All filler estimates are proved here; the
only inputs are the active variance limit and dense-row ratio. -/
theorem paddedFeatureRow_normalized_truncation_variance_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m d : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1) (c : ∀ n, Fin (m n) → ℝ)
    (g : ℝ → ℝ) (D : ℝ) (K : ℕ) (V : ℝ)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hratio : Tendsto (fun n : ℕ => (m n : ℝ) / (m n + d n : ℝ))
      atTop (𝓝 1))
    (hactive : Tendsto (fun n : ℕ => (m n : ℝ)⁻¹ *
      ∑ i : Fin (m n), ∑ j : Fin (m n), c n i * c n j *
        gaussianLogTruncationCovariance K
          (featureCorrelation (u n)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ j))) atTop (𝓝 V))
    (hg : ∀ x, |g x| ≤ D) :
    Tendsto (fun n : ℕ =>
      Var[fun x => (Real.sqrt (m n + d n : ℝ))⁻¹ *
        gaussianLogTruncationStatistic (paddedFeatureRow (u n) (d n))
          (paddedCoefficientRow (c n) g (d n))
          (fun i => EuclideanSpace.basisFun (Fin (m n + d n)) ℝ i) K x;
        featureGaussian (paddedFeatureRow (u n) (d n))]) atTop (𝓝 V) := by
  let A : ℕ → ℝ := fun n =>
    ∑ i : Fin (m n), ∑ j : Fin (m n), c n i * c n j *
      gaussianLogTruncationCovariance K
        (featureCorrelation (u n)
          (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
          (EuclideanSpace.basisFun (Fin (m n)) ℝ j))
  let F : ℕ → ℝ := fun n => ∑ i : Fin (d n),
    g ((((m n + i.val : ℕ) : ℝ) + 1) / (m n + d n : ℝ)) ^ 2
  have hd := padding_fraction_tendsto_zero m d hm hratio
  have hF : Tendsto (fun n : ℕ => (m n + d n : ℝ)⁻¹ * F n)
      atTop (𝓝 0) := by
    simpa only [F] using padded_profile_square_average_tendsto_zero m d g D hm hd hg
  have hdecomp := normalized_padded_decomposition_tendsto m d A F
    (gaussianLogTruncationCovariance K 1) V hm hratio (by simpa only [A] using hactive) hF
  apply hdecomp.congr'
  filter_upwards with n
  rw [paddedFeatureRow_normalized_truncation_variance (u n) (hu n)
    (c n) g (d n) K]

/-- Dense independent padding preserves the exact B&S covariance-square tail
condition. -/
theorem paddedFeatureRow_correlation_square_average_tail
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m d : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (htail : ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (m n : ℝ)⁻¹ * ∑ i : Fin (m n), ∑ j : Fin (m n),
        (if K < Nat.dist i.val j.val then
          |featureCorrelation (u n)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
            (EuclideanSpace.basisFun (Fin (m n)) ℝ j)| ^ 2 else 0) ≤ ε) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (m n + d n : ℝ)⁻¹ * ∑ i : Fin (m n + d n),
        ∑ j : Fin (m n + d n),
        (if K < Nat.dist i.val j.val then
          |featureCorrelation (paddedFeatureRow (u n) (d n))
            (EuclideanSpace.basisFun (Fin (m n + d n)) ℝ i)
            (EuclideanSpace.basisFun (Fin (m n + d n)) ℝ j)| ^ 2 else 0) ≤ ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := htail ε hε
  refine ⟨K, ?_⟩
  filter_upwards [hm, hK] with n hmn hKn
  rw [paddedFeatureRow_correlation_square_tail_sum_eq (u n) (hu n) (d n) K]
  have hsum0 : 0 ≤ ∑ i : Fin (m n), ∑ j : Fin (m n),
      (if K < Nat.dist i.val j.val then
        |featureCorrelation (u n)
          (EuclideanSpace.basisFun (Fin (m n)) ℝ i)
          (EuclideanSpace.basisFun (Fin (m n)) ℝ j)| ^ 2 else 0) := by
    positivity
  have hinv : (m n + d n : ℝ)⁻¹ ≤ (m n : ℝ)⁻¹ := by
    apply inv_anti₀ (by exact_mod_cast hmn)
    exact_mod_cast Nat.le_add_right (m n) (d n)
  exact (mul_le_mul_of_nonneg_right hinv hsum0).trans hKn

end Hurst
