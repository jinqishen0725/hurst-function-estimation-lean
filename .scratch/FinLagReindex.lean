import Hurst.TruncatedVarianceTail

noncomputable section
namespace Hurst

#check Finset.sum_dite
#check Finset.sum_dite_irrel
#check Finset.sum_filter
#check Finset.sum_bij

theorem test_fin_zeroExtended_lag_sum_eq_range
    (m k : ℕ) (F : Fin m → Fin m → ℝ) :
    (∑ i : Fin m, if h : i.val + k < m then
      F i ⟨i.val + k, h⟩ else 0) =
      ∑ i : Fin (m - k),
        F ⟨i.val, by have := i.isLt; omega⟩
          ⟨i.val + k, by have := i.isLt; omega⟩ := by
  change (∑ i ∈ Finset.univ, if h : i.val + k < m then
      F i ⟨i.val + k, h⟩ else 0) = _
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  apply Finset.sum_bij (fun i hi =>
    ⟨i.val, by
      trace_state
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega⟩)
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj hij
    exact Fin.ext (congrArg Fin.val hij)
  · intro j hj
    let i : Fin m := ⟨j.val, by have := j.isLt; omega⟩
    refine ⟨i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, i]
      omega
    · exact Fin.ext rfl
  · intro i hi
    rfl

end Hurst
