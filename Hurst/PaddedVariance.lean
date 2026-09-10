import Hurst.PaddedPolynomialRow
import Hurst.TruncatedCovarianceLimit
import Hurst.TruncatedVarianceFormula

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Hurst

def paddedCoefficientRow {m : ℕ} (c : Fin m → ℝ) (g : ℝ → ℝ)
    (d : ℕ) (i : Fin (m + d)) : ℝ :=
  if hi : i.val < m then c ⟨i.val, hi⟩
  else g (((i.val : ℝ) + 1) / (m + d : ℝ))

@[simp] theorem paddedCoefficientRow_castAdd {m : ℕ}
    (c : Fin m → ℝ) (g : ℝ → ℝ) (d : ℕ) (i : Fin m) :
    paddedCoefficientRow c g d (Fin.castAdd d i) = c i := by
  simp [paddedCoefficientRow]

@[simp] theorem paddedCoefficientRow_natAdd {m : ℕ}
    (c : Fin m → ℝ) (g : ℝ → ℝ) (d : ℕ) (i : Fin d) :
    paddedCoefficientRow c g d (Fin.natAdd m i) =
      g ((((m + i.val : ℕ) : ℝ) + 1) / (m + d : ℝ)) := by
  simp [paddedCoefficientRow]

theorem gaussianLogTruncationCovariance_zero (K : ℕ) :
    gaussianLogTruncationCovariance K 0 = 0 := by
  have h := gaussianLogTruncationCovariance_abs_le_square K 0 (by norm_num)
  norm_num at h
  exact h

/-- Exact covariance-sum decomposition for an active row followed by
independent filler coordinates.  Cross terms vanish because the Hermite rank
is at least two, hence the truncation covariance is zero at correlation zero. -/
theorem paddedFeatureRow_truncationCovariance_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (c : Fin m → ℝ) (g : ℝ → ℝ) (d K : ℕ) :
    (∑ i : Fin (m + d), ∑ j : Fin (m + d),
      paddedCoefficientRow c g d i * paddedCoefficientRow c g d j *
        gaussianLogTruncationCovariance K
          (featureCorrelation (paddedFeatureRow u d)
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ i)
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ j))) =
      (∑ i : Fin m, ∑ j : Fin m, c i * c j *
        gaussianLogTruncationCovariance K
          (featureCorrelation u
            (EuclideanSpace.basisFun (Fin m) ℝ i)
            (EuclideanSpace.basisFun (Fin m) ℝ j))) +
      gaussianLogTruncationCovariance K 1 *
        ∑ i : Fin d,
          g ((((m + i.val : ℕ) : ℝ) + 1) / (m + d : ℝ)) ^ 2 := by
  rw [Fin.sum_univ_add]
  have htarget : (∑ i : Fin m, ∑ j : Fin (m + d),
      paddedCoefficientRow c g d (Fin.castAdd d i) * paddedCoefficientRow c g d j *
        gaussianLogTruncationCovariance K
          (featureCorrelation (paddedFeatureRow u d)
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d i))
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ j))) =
      ∑ i : Fin m, ∑ j : Fin m, c i * c j *
        gaussianLogTruncationCovariance K
          (featureCorrelation u
            (EuclideanSpace.basisFun (Fin m) ℝ i)
            (EuclideanSpace.basisFun (Fin m) ℝ j)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_add]
    simp only [paddedCoefficientRow_castAdd,
      paddedFeatureRow_correlation_castAdd u hu]
    rw [show (∑ j : Fin d,
        c i * paddedCoefficientRow c g d (Fin.natAdd m j) *
          gaussianLogTruncationCovariance K
            (featureCorrelation (paddedFeatureRow u d)
              (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d i))
              (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m j)))) = 0 by
        apply Finset.sum_eq_zero
        intro j _
        rw [paddedFeatureRow_correlation_cross u hu,
          gaussianLogTruncationCovariance_zero, mul_zero]]
    simp
  rw [htarget]
  have hfiller : (∑ i : Fin d, ∑ j : Fin (m + d),
        paddedCoefficientRow c g d (Fin.natAdd m i) *
          paddedCoefficientRow c g d j *
          gaussianLogTruncationCovariance K
              (featureCorrelation (paddedFeatureRow u d)
                (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m i))
                (EuclideanSpace.basisFun (Fin (m + d)) ℝ j))) =
      gaussianLogTruncationCovariance K 1 *
        ∑ i : Fin d, g ((((m + i.val : ℕ) : ℝ) + 1) / (m + d : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_add]
    have hcross : (∑ j : Fin m,
          paddedCoefficientRow c g d (Fin.natAdd m i) *
            paddedCoefficientRow c g d (Fin.castAdd d j) *
            gaussianLogTruncationCovariance K
              (featureCorrelation (paddedFeatureRow u d)
                (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m i))
                (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d j)))) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [paddedFeatureRow_correlation_cross_rev u hu,
        gaussianLogTruncationCovariance_zero, mul_zero]
    rw [hcross, zero_add]
    rw [show (∑ j : Fin d,
          paddedCoefficientRow c g d (Fin.natAdd m i) *
            paddedCoefficientRow c g d (Fin.natAdd m j) *
            gaussianLogTruncationCovariance K
              (featureCorrelation (paddedFeatureRow u d)
                (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m i))
                (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m j)))) =
          g ((((m + i.val : ℕ) : ℝ) + 1) / (m + d : ℝ)) ^ 2 *
            gaussianLogTruncationCovariance K 1 by
      classical
      rw [Finset.sum_eq_single i]
      · rw [paddedFeatureRow_correlation_natAdd u hu, if_pos rfl]
        rw [paddedCoefficientRow_natAdd]
        ring
      · intro j _ hji
        rw [paddedFeatureRow_correlation_natAdd u hu, if_neg (Ne.symm hji),
          gaussianLogTruncationCovariance_zero, mul_zero]
      · simp]
    ring
  rw [hfiller]

/-- Exact variance formula for the normalized padded row.  It isolates the
original covariance sum and the diagonal variance of the independent filler
coordinates; all later asymptotics reduce to `d / (m+d) → 0`. -/
theorem paddedFeatureRow_normalized_truncation_variance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (c : Fin m → ℝ) (g : ℝ → ℝ) (d K : ℕ) :
    Var[fun x => (Real.sqrt (m + d : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (paddedFeatureRow u d)
        (paddedCoefficientRow c g d)
        (fun i => EuclideanSpace.basisFun (Fin (m + d)) ℝ i) K x;
      featureGaussian (paddedFeatureRow u d)] =
      ((m + d : ℝ)⁻¹) *
        ((∑ i : Fin m, ∑ j : Fin m, c i * c j *
          gaussianLogTruncationCovariance K
            (featureCorrelation u
              (EuclideanSpace.basisFun (Fin m) ℝ i)
              (EuclideanSpace.basisFun (Fin m) ℝ j))) +
        gaussianLogTruncationCovariance K 1 *
          ∑ i : Fin d,
            g ((((m + i.val : ℕ) : ℝ) + 1) / (m + d : ℝ)) ^ 2) := by
  have hnonzero : ∀ i : Fin (m + d),
      ∑ j, (EuclideanSpace.basisFun (Fin (m + d)) ℝ i) j •
        paddedFeatureRow u d j ≠ 0 := by
    intro i
    have hsum : (∑ j, (EuclideanSpace.basisFun (Fin (m + d)) ℝ i) j •
        paddedFeatureRow u d j) = paddedFeatureRow u d i := by
      simp [EuclideanSpace.basisFun_apply]
    rw [hsum]
    exact norm_ne_zero_iff.mp (by rw [paddedFeatureRow_norm u hu d]; norm_num)
  rw [variance_const_mul,
    featureGaussian_logTruncation_variance _ _ _ hnonzero K,
    paddedFeatureRow_truncationCovariance_sum u hu c g d K]
  have hsqrt : (Real.sqrt (m + d : ℝ)) ^ 2 = (m + d : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [inv_pow, hsqrt]

end Hurst
