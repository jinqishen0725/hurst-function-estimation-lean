import Hurst.DistributionSubsequence

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace Hurst

/-- Convergence in distribution is preserved by a cofinal reindexing, including
when every row has its own sample space and probability measure. -/
theorem TendstoInDistribution.comp_atTop
    {E Ω' : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → E)
    [MeasurableSpace Ω'] (Z : Ω' → E) (μ' : Measure Ω')
    [IsProbabilityMeasure μ']
    (hX : TendstoInDistribution X atTop Z μ μ')
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop) :
    TendstoInDistribution (fun k => X (s k)) atTop Z
      (fun k => μ (s k)) μ' where
  forall_aemeasurable k := hX.forall_aemeasurable (s k)
  aemeasurable_limit := hX.aemeasurable_limit
  tendsto := hX.tendsto.comp hs

/-- If a cofinal sequence of exact-size rows has the same laws as a
variable-size array, an exact-row CLT transfers to that array.  This is the
purely topological/law part of the active-card reduction; construction of the
exact-row extension remains a separate algebraic task. -/
theorem tendstoInDistribution_of_identDistrib_exactRows
    {E Ω' : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → E)
    (Ξ : ℕ → Type*) [mΞ : ∀ n, MeasurableSpace (Ξ n)]
    (ν : (n : ℕ) → Measure (Ξ n)) [hν : ∀ n, IsProbabilityMeasure (ν n)]
    (Y : (n : ℕ) → Ξ n → E)
    [MeasurableSpace Ω'] (Z : Ω' → E) (μ' : Measure Ω')
    [IsProbabilityMeasure μ']
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (hY : TendstoInDistribution Y atTop Z ν μ')
    (hid : ∀ k, IdentDistrib (X k) (Y (s k)) (μ k) (ν (s k))) :
    TendstoInDistribution X atTop Z μ μ' where
  forall_aemeasurable k := (hid k).aemeasurable_fst
  aemeasurable_limit := hY.aemeasurable_limit
  tendsto := by
    have hcomp := (TendstoInDistribution.comp_atTop Ξ ν Y Z μ' hY s hs).tendsto
    apply hcomp.congr'
    filter_upwards with k
    exact Subtype.ext (hid k).map_eq.symm

end Hurst
