import Hurst.OptimalBandwidth
import Hurst.GridCorrelationRows

noncomputable section
open Filter
open scoped Topology
namespace Hurst

def scaleAverageResolution (p : ℝ) (n : ℕ) : ℕ := Nat.ceil ((optimalLocalBandwidth p n)⁻¹)

theorem scaleAverageResolution_design (p : ℝ) (n : ℕ) (hδ : 0 < optimalLocalBandwidth p n) :
    0 < scaleAverageResolution p n ∧ 1 ≤ (scaleAverageResolution p n:ℝ)*optimalLocalBandwidth p n := by
  have hm : (optimalLocalBandwidth p n)⁻¹ ≤ (scaleAverageResolution p n:ℝ) := Nat.le_ceil _
  have hmpos : (0:ℝ) < scaleAverageResolution p n := (inv_pos.mpr hδ).trans_le hm
  refine ⟨by exact_mod_cast hmpos, ?_⟩
  have he := mul_le_mul_of_nonneg_right hm hδ.le
  rwa [inv_mul_cancel₀ hδ.ne'] at he

/-- At the final optimal bandwidth, the full scale MSE divided by log squared has the target rate. -/
theorem scale_optimal_rate_eventually (p : ℝ) (hp : 1 ≤ p) :
    ∀ᶠ n : ℕ in atTop,
      ((Real.log n*(optimalLocalBandwidth p n)^p)^2+
        (Real.log n*gridCovarianceError (1/2) 1 n)^2+(Real.log n)^2/(n:ℝ)+
        1/((n:ℝ)*optimalLocalBandwidth p n))/(Real.log n)^2 ≤ 4*(lowerBoundRate p n)^2 := by
  have hg := (gridCovarianceError_square_row_tendsto (1/2) 1 (by norm_num)).eventually_le_const (by norm_num : (0:ℝ) < 1)
  filter_upwards [optimalLocalBandwidth_eventual_design p 1 hp, hg] with n hn he
  obtain ⟨hn1, hδ, _, _, hrate, hL⟩ := hn
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : 0 < Real.log (n:ℝ) := by linarith
  have hb := optimalLocalBandwidth_bias_balance p n
  have hv := optimalLocalBandwidth_variance_balance p hp n hn1
  have he' : (gridCovarianceError (1/2) 1 n)^2 ≤ 1/(n:ℝ) := (le_div_iff₀ hnR).mpr (by simpa only [mul_comm] using he)
  have hδpow : ((optimalLocalBandwidth p n)^p)^2 = (lowerBoundRate p n)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    convert hb using 1 <;> ring
  have hid : ((Real.log n*(optimalLocalBandwidth p n)^p)^2+
        (Real.log n*gridCovarianceError (1/2) 1 n)^2+(Real.log n)^2/(n:ℝ)+
        1/((n:ℝ)*optimalLocalBandwidth p n))/(Real.log n)^2 =
      ((optimalLocalBandwidth p n)^p)^2+(gridCovarianceError (1/2) 1 n)^2+1/(n:ℝ)+
        1/((n:ℝ)*optimalLocalBandwidth p n*(Real.log n)^2) := by
    field_simp
    <;> ring
  rw [hid, hδpow, hv]
  linarith

end Hurst
