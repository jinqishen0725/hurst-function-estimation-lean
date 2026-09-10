import Hurst.Moments
import Mathlib.Algebra.Order.Chebyshev

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

theorem finite_average_sq_le (m : ℕ) (hm : 0 < m) (x : Fin m → ℝ) :
    ((∑ i, x i)/(m:ℝ))^2 ≤ (∑ i, (x i)^2)/(m:ℝ) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hmR)).mpr
  calc
    _ ≤ (m:ℝ)*(∑ i, (x i)^2) := h
    _ = (∑ i, (x i)^2)/(m:ℝ)*(m:ℝ)^2 := by field_simp

/-- Averaging correlated errors needs no independence and yields no unproved extra factor. -/
theorem finite_average_mse_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (hm : 0 < m) (X : Fin m → Ω → ℝ) (R : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hr : ∀ i, (∫ x, (X i x)^2 ∂P) ≤ R) :
    (∫ x, ((∑ i, X i x)/(m:ℝ))^2 ∂P) ≤ R := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hs : MemLp (fun x => ∑ i, X i x) 2 P := memLp_finsetSum _ (fun i _ => hX i)
  have ha : MemLp (fun x => (∑ i, X i x)/(m:ℝ)) 2 P := by
    simpa only [div_eq_mul_inv] using hs.mul_const (m:ℝ)⁻¹
  have hb : Integrable (fun x => (∑ i, (X i x)^2)/(m:ℝ)) P :=
    (integrable_finsetSum _ (fun i _ => (hX i).integrable_sq)).div_const _
  have he := integral_mono ha.integrable_sq hb (fun x => finite_average_sq_le m hm (fun i => X i x))
  rw [integral_div, integral_finsetSum _ (fun i _ => (hX i).integrable_sq)] at he
  apply he.trans
  apply (div_le_iff₀ hmR).mpr
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hr i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hh

end Hurst
