import Hurst.SmoothTaylor
import Hurst.InverseRepair

noncomputable section
open Set
namespace Hurst

def q2LogCorrection (h : ℝ) : ℝ := Real.log (4 - (2 : ℝ) ^ (2 * h))

theorem q2LogCorrection_smooth : ContDiffOn ℝ (⊤ : ℕ∞) q2LogCorrection (Ioo (0 : ℝ) 1) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun h : ℝ => (2 : ℝ) ^ (2 * h)) :=
    contDiff_const.rpow (contDiff_const.mul contDiff_id) (by intro h; norm_num)
  exact (contDiff_const.sub hp).contDiffOn.log (fun h hh => (calibrationTwo_positive_inside h hh.2).ne')

theorem q2LogCorrection_uniform_quadratic (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 0, ∀ h k : ℝ, h ∈ Icc a b → k ∈ Icc a b →
      |q2LogCorrection k - q2LogCorrection h - (k - h) * deriv q2LogCorrection h| ≤ C * |k - h| ^ 2 :=
  smooth_uniform_quadratic_remainder q2LogCorrection q2LogCorrection_smooth a b ha hb

theorem q2LogCorrection_uniform_derivative (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 0, ∀ h ∈ Icc a b, |deriv q2LogCorrection h| ≤ C := by
  obtain ⟨C, hC, hc⟩ := smooth_uniform_iteratedDeriv_bound q2LogCorrection q2LogCorrection_smooth a b ha hb 1
  exact ⟨C, hC, by simpa only [iteratedDeriv_one] using hc⟩

end Hurst
