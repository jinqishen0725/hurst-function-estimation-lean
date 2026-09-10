import Hurst.TriangularL1Transfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem distribution_add_deterministic {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ∀ n,Ω n → ℝ) (Z : Ω' → ℝ) (b : ℕ → ℝ) (β : ℝ)
    (hX : TendstoInDistribution X atTop Z P P') (hb : Tendsto b atTop (𝓝 β)) :
    TendstoInDistribution (fun n x => X n x+b n) atTop (fun z => Z z+β) P P' := by
  have hc := hX.continuous_comp (show Continuous (fun z : ℝ => z+β) by fun_prop)
  apply triangular_L1_distribution_transfer P P' (fun n x => X n x+β) _ _ hc
    (fun n => (hX.forall_aemeasurable n).add aemeasurable_const)
  · apply Eventually.of_forall
    intro n
    have hid (x : Ω n) : X n x+b n-(X n x+β)=b n-β := by ring
    simp only [hid]
    exact integrable_const _
  · have hid (n : ℕ) (x : Ω n) : X n x+b n-(X n x+β)=b n-β := by ring
    simp only [hid,integral_const,probReal_univ,one_smul]
    convert (hb.sub_const β).abs using 1 <;> first | rfl | simp

end Hurst
