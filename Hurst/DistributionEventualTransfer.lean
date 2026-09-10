import Hurst.DistributionLawTransfer

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-- A finite initial segment of a triangular array does not affect convergence
in distribution.  Measurability of the replacement rows is stated separately
because `TendstoInDistribution` records it for every index, not just
asymptotically. -/
theorem tendstoInDistribution_congr_eventually
    {ι E Ω' : Type*} {Ω : ι → Type*}
    [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]
    [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (X Y : (i : ι) → Ω i → E) (Z : Ω' → E) (l : Filter ι)
    (hYmeas : ∀ i, AEMeasurable (Y i) (μ i))
    (hXY : ∀ᶠ i in l, X i =ᵐ[μ i] Y i)
    (hX : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution Y l Z μ μ' where
  forall_aemeasurable := hYmeas
  aemeasurable_limit := hX.aemeasurable_limit
  tendsto := by
    apply hX.tendsto.congr'
    filter_upwards [hXY] with i hi
    apply Subtype.ext
    exact Measure.map_congr hi

end Hurst
