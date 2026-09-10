import Hurst.MidpointWhitening

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
namespace Hurst

/-- A common nonzero scale cancels from the actual divergence, including singular feature families. -/
theorem featureGaussian_klDiv_smul {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v w : ι → E) (σ : ℝ) (hσ : σ ≠ 0) :
    klDiv (featureGaussian (fun i => σ • v i)) (featureGaussian (fun i => σ • w i)) =
      klDiv (featureGaussian v) (featureGaussian w) := by
  have hdet : IsUnit (Matrix.det (σ • (1 : Matrix ι ι ℝ))) := by
    rw [isUnit_iff_ne_zero, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hσ
  have he := featureGaussian_klDiv_matrix v w (σ • (1 : Matrix ι ι ℝ)) hdet
  have hs (u : ι → E) : (fun i => ∑ j, (σ • (1 : Matrix ι ι ℝ)) i j • u j) = fun i => σ • u i := by
    funext i
    simp [Matrix.one_apply, ite_mul, mul_ite]
  rw [hs v, hs w] at he
  exact he

def scaledHarmonizableGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : ℝ) (h : ι → Ioo (0 : ℝ) 1) (t : ι → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  featureGaussian (fun i => σ • harmonizableFeature (h i) (t i))

/-- The original common-scale observation model has the same whitened KL expression. -/
theorem scaledHarmonizableGaussian_midpoint_klDiv (σ : ℝ) (hσ : σ ≠ 0)
    (n : ℕ) (h : Fin n → Ioo (0 : ℝ) 1) :
    klDiv (scaledHarmonizableGaussian σ h (fun i => grid n i.val))
      (scaledHarmonizableGaussian σ (fun _ => brownianHurst) (fun i => grid n i.val)) =
      klDiv (featureGaussian (fun i => whitenedIncrementFeature (h i) (previousGridHurst h i)
        (midpointLeft n i) (midpointStep n i)))
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  rw [scaledHarmonizableGaussian, scaledHarmonizableGaussian, featureGaussian_klDiv_smul _ _ σ hσ]
  change klDiv (harmonizableGaussian h (fun i => grid n i.val))
    (harmonizableGaussian (fun _ => brownianHurst) (fun i => grid n i.val)) = _
  rw [harmonizableGaussian_midpoint_klDiv_whitening]
  simp_rw [midpoint_whitened_feature_eq]

end Hurst
