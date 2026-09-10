import Hurst.ExactPaddedConditions
import Hurst.DistributionRowEmbedding
import Hurst.FeatureObservationMap

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- A feature row and its isometric zero embedding generate exactly the same
finite Gaussian measure. -/
theorem featureGaussian_withLp_zero_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E) :
    featureGaussian (fun i => WithLp.toLp 2 (u i, (0 : Lp ℝ 2 (volume : Measure ℝ)))) =
      featureGaussian u := by
  unfold featureGaussian
  congr 1
  ext i j
  simp [Matrix.gram_apply, WithLp.prod_inner_apply]

/-- At a dense-selector override hit, the selected row exactly fills the
ambient row. -/
theorem exactPaddedFeatureRow_at_override_hit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (source dense : ℕ → ℕ)
    (hR : StrictMono (fun k => m (source k)))
    (n : ℕ) (i : Fin (m (source n))) :
    exactPaddedFeatureRow m u
        (overrideDenseSelector (fun k => m (source k)) source dense)
        (m (source n)) i =
      WithLp.toLp 2 (u (source n) i,
        (0 : Lp ℝ 2 (volume : Measure ℝ))) := by
  simp [exactPaddedFeatureRow,
    overrideDenseSelector_at_hit _ source dense hR n, paddedFeatureRow]
  have hs : overrideDenseSelector (fun k => m (source k)) source dense
      (m (source n)) = source n :=
    overrideDenseSelector_at_hit _ source dense hR n
  apply congr_heq (congr_arg_heq u hs)
  exact (Fin.heq_ext_iff (congrArg m hs)).2 rfl

theorem exactPaddedCoefficientRow_at_override_hit
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (source dense : ℕ → ℕ)
    (hR : StrictMono (fun k => m (source k)))
    (n : ℕ) (i : Fin (m (source n))) :
    exactPaddedCoefficientRow m c g
        (overrideDenseSelector (fun k => m (source k)) source dense)
        (m (source n)) i = c (source n) i := by
  simp [exactPaddedCoefficientRow,
    overrideDenseSelector_at_hit _ source dense hR n, paddedCoefficientRow]
  have hs : overrideDenseSelector (fun k => m (source k)) source dense
      (m (source n)) = source n :=
    overrideDenseSelector_at_hit _ source dense hR n
  apply congr_heq (congr_arg_heq c hs)
  exact (Fin.heq_ext_iff (congrArg m hs)).2 rfl

/-- On every exact selector hit, zero padding changes neither the Gaussian
law nor the normalized coordinate finite-Hermite statistic. -/
theorem exactPaddedFeatureRow_identDistrib_at_override_hit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (u : ∀ n, Fin (m n) → E)
    (hu : ∀ n i, ‖u n i‖ = 1)
    (c : ∀ n, Fin (m n) → ℝ) (g : ℝ → ℝ)
    (source dense : ℕ → ℕ)
    (hR : StrictMono (fun k => m (source k))) (n K : ℕ) :
    IdentDistrib
      (fun x => (Real.sqrt (m (source n) : ℝ))⁻¹ *
        gaussianLogTruncationStatistic (u (source n)) (c (source n))
          (fun i => EuclideanSpace.basisFun (Fin (m (source n))) ℝ i) K x)
      (fun x => (Real.sqrt (m (source n) : ℝ))⁻¹ *
        gaussianLogTruncationStatistic
          (exactPaddedFeatureRow m u
            (overrideDenseSelector (fun k => m (source k)) source dense)
            (m (source n)))
          (exactPaddedCoefficientRow m c g
            (overrideDenseSelector (fun k => m (source k)) source dense)
            (m (source n)))
          (fun i => EuclideanSpace.basisFun (Fin (m (source n))) ℝ i) K x)
      (featureGaussian (u (source n)))
      (featureGaussian (exactPaddedFeatureRow m u
        (overrideDenseSelector (fun k => m (source k)) source dense)
        (m (source n)))) := by
  let s := overrideDenseSelector (fun k => m (source k)) source dense
  have hv : exactPaddedFeatureRow m u s (m (source n)) =
      fun i => WithLp.toLp 2
        (u (source n) i, (0 : Lp ℝ 2 (volume : Measure ℝ))) := by
    funext i
    exact exactPaddedFeatureRow_at_override_hit m u source dense hR n i
  have hw : exactPaddedCoefficientRow m c g s (m (source n)) = c (source n) := by
    funext i
    exact exactPaddedCoefficientRow_at_override_hit m c g source dense hR n i
  have hmeasure : featureGaussian (exactPaddedFeatureRow m u s (m (source n))) =
      featureGaussian (u (source n)) := by
    rw [hv]
    exact featureGaussian_withLp_zero_eq (u (source n))
  have hfun : (fun x => (Real.sqrt (m (source n) : ℝ))⁻¹ *
        gaussianLogTruncationStatistic (exactPaddedFeatureRow m u s (m (source n)))
          (exactPaddedCoefficientRow m c g s (m (source n)))
          (fun i => EuclideanSpace.basisFun (Fin (m (source n))) ℝ i) K x) =
      (fun x => (Real.sqrt (m (source n) : ℝ))⁻¹ *
        gaussianLogTruncationStatistic (u (source n)) (c (source n))
          (fun i => EuclideanSpace.basisFun (Fin (m (source n))) ℝ i) K x) := by
    funext x
    rw [gaussianLogTruncationStatistic_basis_normalized
      (exactPaddedFeatureRow m u s (m (source n)))
      (exactPaddedFeatureRow_norm m u hu s (m (source n)))]
    rw [gaussianLogTruncationStatistic_basis_normalized
      (u (source n)) (hu (source n))]
    rw [hw]
  rw [hmeasure, hfun]
  have hmeas : AEMeasurable (fun x => (Real.sqrt (m (source n) : ℝ))⁻¹ *
      gaussianLogTruncationStatistic (u (source n)) (c (source n))
        (fun i => EuclideanSpace.basisFun (Fin (m (source n))) ℝ i) K x)
      (featureGaussian (u (source n))) :=
    (gaussianLogTruncationStatistic_memLp_two
      (u (source n)) (c (source n))
      (fun i => EuclideanSpace.basisFun (Fin (m (source n))) ℝ i) K).1.const_mul
        (Real.sqrt (m (source n) : ℝ))⁻¹
      |>.aemeasurable
  exact ⟨hmeas, hmeas, rfl⟩

end Hurst
