import Hurst.TriangularL1Transfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem distribution_transfer_of_eventual_test_equality
    {Ω Ξ : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)] [∀ n,MeasurableSpace (Ξ n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (Q : ∀ n,Measure (Ξ n)) [∀ n,IsProbabilityMeasure (Q n)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ∀ n,Ω n → ℝ) (Y : ∀ n,Ξ n → ℝ) (Z : Ω' → ℝ)
    (hX : TendstoInDistribution X atTop Z P P')
    (hY : ∀ n,AEMeasurable (Y n) (Q n))
    (he : ∀ᶠ n in atTop,∀ φ : ℝ → ℝ,(∫ x,φ (Y n x) ∂Q n)=∫ x,φ (X n x) ∂P n) :
    TendstoInDistribution Y atTop Z Q P' := by
  refine ⟨hY,hX.aemeasurable_limit,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hb hl
  have hh := tendsto_iff_forall_lipschitz_integral_tendsto.mp hX.tendsto φ hb hl
  obtain ⟨K,hK⟩ := hl
  apply hh.congr'
  filter_upwards [he] with n hn
  change (∫ x,φ x ∂(P n).map (X n))=(∫ x,φ x ∂(Q n).map (Y n))
  rw [integral_map (hX.forall_aemeasurable n) hK.continuous.aestronglyMeasurable,
    integral_map (hY n) hK.continuous.aestronglyMeasurable]
  exact (hn φ).symm

end Hurst
