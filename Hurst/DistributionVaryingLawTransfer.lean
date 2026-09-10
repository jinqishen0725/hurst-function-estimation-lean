import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-- Convergence in distribution is unchanged by rowwise replacement with an
identically distributed variable, even when both row probability spaces vary. -/
theorem tendstoInDistribution_of_identDistrib_rows_varying
    {ι F Omega' : Type*} {Omega Psi : ι → Type*}
    [∀ i, MeasurableSpace (Omega i)] [∀ i, MeasurableSpace (Psi i)]
    (P : ∀ i, Measure (Omega i)) [∀ i, IsProbabilityMeasure (P i)]
    (nu : ∀ i, Measure (Psi i)) [∀ i, IsProbabilityMeasure (nu i)]
    [MeasurableSpace Omega'] (P' : Measure Omega') [IsProbabilityMeasure P']
    [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    (X : ∀ i, Omega i → F) (Y : ∀ i, Psi i → F)
    (Z : Omega' → F) (l : Filter ι)
    (hXY : ∀ i, IdentDistrib (X i) (Y i) (P i) (nu i))
    (hY : TendstoInDistribution Y l Z nu P') :
    TendstoInDistribution X l Z P P' where
  forall_aemeasurable i := (hXY i).aemeasurable_fst
  aemeasurable_limit := hY.aemeasurable_limit
  tendsto := by
    refine (tendsto_congr' ?_).mpr hY.tendsto
    exact Eventually.of_forall fun i => Subtype.ext (hXY i).map_eq

end Hurst
