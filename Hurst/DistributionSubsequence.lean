import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

noncomputable section
open MeasureTheory Filter
namespace Hurst

/-- Along every cofinal subsequence, a row-size function tending to infinity
has a further subsequence on which the row sizes are strictly increasing. -/
theorem exists_strictMono_rowSize_subsequence
    (rowSize ns : ℕ → ℕ)
    (hrow : Tendsto rowSize atTop atTop)
    (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      StrictMono (fun k => rowSize (ns (ms k))) := by
  obtain ⟨ms, hms, hrowms⟩ :=
    @Filter.strictMono_subseq_of_tendsto_atTop ℕ Nat.instLinearOrder
      Nat.instNoMaxOrder (rowSize ∘ ns) (hrow.comp hns)
  refine ⟨ms, hms, ?_⟩
  intro a b hab
  have hh := hrowms hab
  change Nat.lt (rowSize (ns (ms a))) (rowSize (ns (ms b))) at hh
  exact hh

/-- A subsequence criterion for convergence in distribution with row-dependent
sample spaces.  This is the topological step needed when a triangular array is
first restricted to a cofinal sequence of row sizes. -/
theorem tendstoInDistribution_of_every_subsequence
    {E Ω' : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → E)
    [MeasurableSpace Ω'] (Z : Ω' → E) (μ' : Measure Ω')
    [IsProbabilityMeasure μ']
    (hX : ∀ n, AEMeasurable (X n) (μ n))
    (hZ : AEMeasurable Z μ')
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ,
        TendstoInDistribution
          (fun k => X (ns (ms k))) atTop Z
          (fun k => μ (ns (ms k))) μ') :
    TendstoInDistribution X atTop Z μ μ' where
  forall_aemeasurable := hX
  aemeasurable_limit := hZ
  tendsto := tendsto_of_subseq_tendsto fun ns hns => by
    obtain ⟨ms, hms⟩ := hsub ns hns
    exact ⟨ms, hms.tendsto⟩

end Hurst
