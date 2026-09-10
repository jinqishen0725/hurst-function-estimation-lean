import Hurst.GaussianLogRisk

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem finite_subfamily_square_rows {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) (he : Function.Injective e) (r : ι → ι → ℝ) (R : ℝ)
    (hr : ∀ i, (∑ j, r i j ^ 2) ≤ R) (i : κ) :
    (∑ j, r (e i) (e j)^2) ≤ R := by
  classical
  have hsum : (∑ j, r (e i) (e j)^2) = ∑ j ∈ Finset.image e Finset.univ, r (e i) j^2 := by
    rw [Finset.sum_image]
    exact fun a _ b _ hab => he hab
  rw [hsum]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)).trans (hr (e i))

end Hurst
