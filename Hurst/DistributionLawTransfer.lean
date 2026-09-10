import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-- Convergence in distribution may be proved on a common probability space
after replacing every row by an identically distributed random variable. -/
theorem tendstoInDistribution_of_identDistrib_rows
    {ι E Ω' Θ : Type*} {Ω : ι → Type*}
    [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]
    [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (X : (i : ι) → Ω i → E) (Y : ι → Θ → E)
    [MeasurableSpace Ω'] (Z : Ω' → E) (μ' : Measure Ω')
    [IsProbabilityMeasure μ'] (l : Filter ι)
    (hXY : ∀ i, IdentDistrib (X i) (Y i) (μ i) ν)
    (hY : TendstoInDistribution Y l Z (fun _ => ν) μ') :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable i := (hXY i).aemeasurable_fst
  aemeasurable_limit := hY.aemeasurable_limit
  tendsto := by
    refine (tendsto_congr' ?_).mpr hY.tendsto
    exact Eventually.of_forall fun i => Subtype.ext (hXY i).map_eq

end Hurst
