import Hurst.FiniteGaussianSpectral

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Hurst

/-- Reindexing Euclidean coordinates by an equivalence is a linear isometry. -/
def euclideanPermutation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp]
theorem euclideanPermutation_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : EuclideanSpace ℝ ι) (j : κ) :
    euclideanPermutation e x j = x (e.symm j) := by
  simp [euclideanPermutation, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

theorem euclideanPermutation_measurePreserving
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (euclideanPermutation e)
      (stdGaussian (EuclideanSpace ℝ ι))
      (stdGaussian (EuclideanSpace ℝ κ)) := by
  refine ⟨(euclideanPermutation e).continuous.measurable, ?_⟩
  exact stdGaussian_map (euclideanPermutation e)

/-- Permuting the coefficients of a finite centered Gaussian spectral sum
does not change its law. -/
theorem centeredSpectralSquares_permute_identDistrib
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (lambda : ι → ℝ) :
    IdentDistrib (centeredSpectralSquares lambda)
      (centeredSpectralSquares (lambda ∘ e))
      (stdGaussian (EuclideanSpace ℝ ι))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let T := euclideanPermutation e
  let F := centeredSpectralSquares lambda
  have hT := euclideanPermutation_measurePreserving e
  have hF : Measurable F := by
    dsimp only [F]
    unfold centeredSpectralSquares
    exact Finset.measurable_sum _ fun i _ => by fun_prop
  have hpoint : F ∘ T = centeredSpectralSquares (lambda ∘ e) := by
    funext x
    change (∑ i, lambda i * ((T x) i ^ 2 - 1)) =
      ∑ i, lambda (e i) * (x i ^ 2 - 1)
    let g : ι → ℝ := fun i ↦ lambda i * (x (e.symm i) ^ 2 - 1)
    have hsum := Equiv.sum_comp e g
    simpa [g, T] using hsum.symm
  refine ⟨hF.aemeasurable, ?_, ?_⟩
  · rw [← hpoint]
    exact hF.aemeasurable.comp_measurable hT.measurable
  · rw [← hpoint, ← Measure.map_map hF hT.measurable, hT.map_eq]

end Hurst
