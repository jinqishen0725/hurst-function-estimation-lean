import Hurst.CalibratedBiasLimit

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem scalar_approximation_tendsto {A B e : ℕ → ℝ} {b C : ℝ}
    (hB : Tendsto B atTop (𝓝 b)) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,|A n-B n|≤C*e n) : Tendsto A atTop (𝓝 b) := by
  have hz := squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg (A n-B n))) hbound
    (by simpa only [mul_zero] using he.const_mul C)
  have hd : Tendsto (fun n => A n-B n) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero,Real.norm_eq_abs] using hz
  have hh := hB.add hd
  simpa only [add_sub_cancel,add_zero] using hh

theorem scalar_scaled_approximation_tendsto (A B den e : ℕ → ℝ) (b C : ℝ)
    (hden : ∀ᶠ n in atTop,0<den n)
    (hB : Tendsto (fun n => B n/den n) atTop (𝓝 b))
    (he : Tendsto (fun n => e n/den n) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,|A n-B n|≤C*e n) :
    Tendsto (fun n => A n/den n) atTop (𝓝 b) := by
  apply scalar_approximation_tendsto hB he
  filter_upwards [hden,hbound] with n hn hb
  rw [← sub_div,abs_div,abs_of_pos hn]
  exact (div_le_div_of_nonneg_right hb hn.le).trans_eq (by ring)

end Hurst
