import Hurst.FiniteAverageMSE

noncomputable section
open Set MeasureTheory
namespace Hurst

theorem finite_average_abs_le (m : ℕ) (hm : 0 < m) (x : Fin m → ℝ) (R : ℝ)
    (hx : ∀ i, |x i| ≤ R) : |(∑ i, x i)/(m:ℝ)| ≤ R := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  rw [abs_div, abs_of_pos hmR]
  apply (div_le_iff₀ hmR).mpr
  have he := (Finset.abs_sum_le_sum_abs x Finset.univ).trans (Finset.sum_le_sum (fun i _ => hx i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using he

theorem finite_average_expectation_bias {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (hm : 0 < m) (X : Fin m → Ω → ℝ) (θ : Fin m → ℝ) (R : ℝ)
    (hX : ∀ i, Integrable (X i) P) (hb : ∀ i, |(∫ x, X i x ∂P)-θ i| ≤ R) :
    |(∫ x, (∑ i, X i x)/(m:ℝ) ∂P)-(∑ i, θ i)/(m:ℝ)| ≤ R := by
  rw [integral_div, integral_finsetSum _ (fun i _ => hX i), ← sub_div, ← Finset.sum_sub_distrib]
  exact finite_average_abs_le m hm _ R hb

end Hurst
