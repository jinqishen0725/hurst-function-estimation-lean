import Hurst.DirectBiasRepair
import Hurst.BumpPacking
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Hurst

theorem oscillation_le_derivative_integral (f df : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (df x) x)
    (hdf : Integrable df) (a b x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x - f y| ≤ ∫ u in a..b, |df u| := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hlocal {u v : ℝ} (huv : u ≤ v) : |f v - f u| ≤ ∫ t in u..v, |df t| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le_integral_of_norm_deriv_le_of_le huv
      hc.continuousOn hd.differentiableOn
      (Filter.Eventually.of_forall fun t _ => by rw [(hf t).deriv, Real.norm_eq_abs])
      hdf.abs.intervalIntegrable
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm]
    exact (hlocal hxy).trans (intervalIntegral.integral_mono_interval hx.1 hxy hy.2
      (Filter.Eventually.of_forall fun t => abs_nonneg _) hdf.abs.intervalIntegrable)
  · exact (hlocal hyx).trans (intervalIntegral.integral_mono_interval hy.1 hyx hx.2
      (Filter.Eventually.of_forall fun t => abs_nonneg _) hdf.abs.intervalIntegrable)

theorem midpoint_cell_quadrature (f df : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (df x) x)
    (hdf : Integrable df) (a h : ℝ) (hh : 0 < h) :
    |h * f (a + h / 2) - ∫ x in a..a + h, f x| ≤ h * ∫ x in a..a + h, |df x| := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have he : h * f (a + h / 2) - ∫ x in a..a + h, f x =
      ∫ x in a..a + h, (f (a + h / 2) - f x) := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, smul_eq_mul]
  rw [he]
  have hbound : ∀ x ∈ Set.uIoc a (a + h), ‖f (a + h / 2) - f x‖ ≤ ∫ u in a..a + h, |df u| := by
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    simpa only [Real.norm_eq_abs] using oscillation_le_derivative_integral f df hf hdf a (a + h)
      (a + h / 2) x ⟨by linarith, by linarith⟩ ⟨hx.1.le, hx.2⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh, mul_comm] using hb

theorem shifted_midpoint_quadrature (f df : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (df x) x)
    (hdf : Integrable df) (a h : ℝ) (hh : 0 < h) (n : ℕ) :
    |h * (∑ i ∈ Finset.range n, f (a + ((i : ℝ) + 1 / 2) * h)) - ∫ x in a..a + (n : ℝ) * h, f x| ≤
      h * ∫ x in a..a + (n : ℝ) * h, |df x| := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := fun i : ℕ => a + (i : ℝ) * h) (n := n) (fun _ _ => hc.intervalIntegrable _ _)
  have hsumdf := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => a + (i : ℝ) * h) (n := n) (fun _ _ => hdf.abs.intervalIntegrable)
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one] at hsum hsumdf
  rw [← hsum, ← hsumdf, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have he := midpoint_cell_quadrature f df hf hdf (a + (i : ℝ) * h) h hh
  convert! he using 1 <;> congr 2 <;> ring

/-- Uniform in the grid offset and length; its constant is the fixed total derivative integral. -/
theorem shifted_midpoint_quadrature_uniform (f df : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (df x) x)
    (hdf : Integrable df) (a h : ℝ) (hh : 0 < h) (n : ℕ) :
    |h * (∑ i ∈ Finset.range n, f (a + ((i : ℝ) + 1 / 2) * h)) - ∫ x in a..a + (n : ℝ) * h, f x| ≤
      h * ∫ x : ℝ, |df x| := by
  apply (shifted_midpoint_quadrature f df hf hdf a h hh n).trans
  apply mul_le_mul_of_nonneg_left _ hh.le
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hh.le))]
  exact setIntegral_le_integral hdf.abs (Filter.Eventually.of_forall fun x => abs_nonneg _)

theorem finite_tail_sum_bound (f : ℕ → ℝ) (B : ℝ) (hB : ∀ i, |f i| ≤ B) (n q : ℕ) (hq : q ≤ n) :
    |(∑ i ∈ Finset.range n, f i) - ∑ i ∈ Finset.range (n - q), f i| ≤ q * B := by
  have hn : n - q + q = n := Nat.sub_add_cancel hq
  have he := Finset.sum_range_add f (n - q) q
  rw [hn] at he
  rw [he, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range q, B := Finset.sum_le_sum (fun i _ => hB _)
    _ = q * B := by simp

/-- Uniform quadrature for the actual valid midpoint observations, including deleted terminal differences. -/
theorem midpoint_design_quadrature_uniform (f df : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (df x) x)
    (hdf : Integrable df) (B : ℝ) (hB : ∀ x, |f x| ≤ B)
    (n q : ℕ) (hn : 0 < n) (hq : q ≤ n) (b t : ℝ) (hb : 0 < b) :
    |((n : ℝ) * b)⁻¹ * (∑ i : Fin (n - q), f ((grid n i.val - t) / b)) -
      ∫ x in (-t / b)..((1 - t) / b), f x| ≤
      ((∫ x : ℝ, |df x|) + q * B) / ((n : ℝ) * b) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : 0 < ((n : ℝ) * b)⁻¹ := by positivity
  have he := shifted_midpoint_quadrature_uniform f df hf hdf (-t / b) (((n : ℝ) * b)⁻¹) hh n
  have harg (i : ℕ) : -t / b + ((i : ℝ) + 1 / 2) * ((n : ℝ) * b)⁻¹ = (grid n i - t) / b := by
    unfold grid
    field_simp
    ring
  have hend : -t / b + (n : ℝ) * ((n : ℝ) * b)⁻¹ = (1 - t) / b := by field_simp; ring
  simp only [harg, hend] at he
  rw [Fin.sum_univ_eq_sum_range (fun i => f ((grid n i - t) / b))]
  have htail := finite_tail_sum_bound (fun i => f ((grid n i - t) / b)) B (fun i => hB _) n q hq
  have hdiff : |((n : ℝ) * b)⁻¹ * (∑ i ∈ Finset.range (n - q), f ((grid n i - t) / b)) -
      ((n : ℝ) * b)⁻¹ * (∑ i ∈ Finset.range n, f ((grid n i - t) / b))| ≤ ((n : ℝ) * b)⁻¹ * (q * B) := by
    rw [← mul_sub, abs_mul, abs_of_pos hh, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left htail hh.le
  have htri := abs_sub_le (((n : ℝ) * b)⁻¹ * ∑ i ∈ Finset.range (n - q), f ((grid n i - t) / b))
    (((n : ℝ) * b)⁻¹ * ∑ i ∈ Finset.range n, f ((grid n i - t) / b))
    (∫ x in (-t / b)..((1 - t) / b), f x)
  have hs := htri.trans (add_le_add hdiff he)
  exact hs.trans_eq (by ring)

end Hurst
