import Hurst.ExternalSecondChaosLimit

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-- The finite partial sum in the spectral representation of a centered
second-chaos variable. -/
def secondChaosSeriesPartial
    {Omega : Type*} (lambda : ℕ → ℝ) (Z : ℕ → Omega → ℝ)
    (K : ℕ) (x : Omega) : ℝ :=
  ∑ j ∈ Finset.range K, lambda j * ((Z j x) ^ 2 - 1)

/-- The almost-sure convergence included in the exact spectral-series
representation immediately gives convergence in distribution of its finite
spectral truncations.  This downstream step is internal Lean, not part of the
external citation. -/
theorem IsSecondChaosSeriesLaw.partial_tendstoInDistribution
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (Q : Omega → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P Q lambda) :
    ∃ Z : ℕ → Omega → ℝ,
      (∀ j, AEMeasurable (Z j) P) ∧ iIndepFun Z P ∧
      (∀ j, P.map (Z j) = gaussianReal 0 1) ∧
      TendstoInDistribution (secondChaosSeriesPartial lambda Z)
        atTop Q (fun _ => P) P := by
  rcases hQ with ⟨hQmeas, _hlambda, Z, hZmeas, hZi, hZlaw,
    _hmem, _hL2, hZae⟩
  refine ⟨Z, hZmeas, hZi, hZlaw, ?_⟩
  apply tendstoInDistribution_of_ae_tendsto
    (fun K => ?_) hQmeas
    (by simpa only [secondChaosSeriesPartial] using hZae)
  unfold secondChaosSeriesPartial
  have hm : AEMeasurable
      (∑ j ∈ Finset.range K,
        fun x => lambda j * ((Z j x) ^ 2 - 1)) P := by
    apply Finset.aemeasurable_sum
    intro j hj
    exact ((hZmeas j).pow_const 2).sub aemeasurable_const |>.const_mul _
  convert hm using 1
  funext x
  simp

end Hurst
