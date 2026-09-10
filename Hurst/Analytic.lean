import Hurst.Rates
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open Filter
open scoped Topology
namespace Hurst

/-- The variance transfer in Lemma 8.3 requires this positive lower bound.
This quantitative estimate avoids any use of log at zero. -/
theorem log_lipschitz_from_below (x y m : ℝ) (hm : 0 < m)
    (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y|/m := by
  have hx0 : 0 < x := hm.trans_le hx
  have hy0 : 0 < y := hm.trans_le hy
  by_cases hxy : y ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at h
    have he : x/y-1 = (x-y)/y := by field_simp
    rw [he] at h
    exact h.trans (div_le_div_of_nonneg_left (by linarith) hm hy)
  · have hxy : x ≤ y := le_of_lt (lt_of_not_ge hxy)
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx0 hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    have he : y/x-1 = (y-x)/x := by field_simp
    rw [he] at h
    have hb := h.trans (div_le_div_of_nonneg_left (by linarith : 0 ≤ y-x) hm hx)
    simpa only [neg_sub] using hb

theorem G_two_strictAnti (L c : ℝ) (hL : 0 < L) :
    StrictAntiOn (G 2 L c) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have hg : g 2 y 0 1 < g 2 x 0 1 := by
    rw [g_two_unit x (ne_of_gt hx.1), g_two_unit y (ne_of_gt hy.1)]
    have hp := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) (by norm_num)
      (show 2*x < 2*y by linarith)
    linarith
  have hl := Real.log_lt_log (g_two_pos y hy.1 hy.2) hg
  unfold G
  nlinarith

/-- The actual derivative calculation underlying the factor 1/2 correction. -/
theorem second_rpow_derivative (H x : ℝ) :
    deriv (deriv (fun u : ℝ => u^(2*H))) x =
      (2*H)*(2*H-1)*x^(2*H-2) := by
  rw [Real.deriv_rpow_const']
  rw [deriv_const_mul_field, Real.deriv_rpow_const]
  rw [show 2*H-1-1 = 2*H-2 by ring]
  ring

theorem half_second_rpow (H x : ℝ) :
    (1/2:ℝ) * deriv (deriv (fun u : ℝ => u^(2*H))) x =
      leadingOne H * x^(2*H-2) := by
  rw [second_rpow_derivative H x]
  unfold leadingOne
  ring

/-- Brownian error rate used to specialize the S.6.1 counterexample. -/
theorem brownian_rho_tendsto :
    Tendsto (fun n : ℕ => Real.log n / n + (n:ℝ)⁻¹) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using hl.add hi

theorem proposition_S6_1_raw_counterexample :
    ¬ Asymptotics.IsBigO atTop (fun n : ℕ => |(n:ℝ)⁻¹-1|)
      (fun n : ℕ => Real.log n/n+(n:ℝ)⁻¹) :=
  raw_variance_error_not_bigO brownian_rho_tendsto

/-- The p=3/2,d=3 endpoint in the rate remark leaves a log(n) factor
in the quadrature-to-bias ratio: it is not o(1). -/
theorem log_not_tendsto_zero : ¬ Tendsto (fun n : ℕ => Real.log n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact not_tendsto_nhds_of_tendsto_atTop h 0

end Hurst
