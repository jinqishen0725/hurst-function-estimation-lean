import Hurst.OracleScaleL1

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem scaled_L1_of_second_moment_tendsto {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)] (S : ∀ n,Ω n → ℝ) (D : ℕ → ℝ)
    (hS : ∀ᶠ n in atTop,MemLp (S n) 2 (P n)) (hD : ∀ᶠ n in atTop,0<D n)
    (hQ : Tendsto (fun n => (∫ ω,(S n ω)^2 ∂P n)/(D n)^2) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω,|S n ω| ∂P n)/D n) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (by simpa only [Real.sqrt_zero] using hQ.sqrt)
  · filter_upwards [hD] with n hn
    exact div_nonneg (integral_nonneg (fun ω => abs_nonneg _)) hn.le
  filter_upwards [hS,hD] with n hs hd
  have hmem : MemLp (fun ω => S n ω/D n) 2 (P n) := by
    simpa only [div_eq_mul_inv] using hs.mul_const (D n)⁻¹
  have he := integral_abs_le_sqrt_second_moment (P n) _ hmem
  simpa only [abs_div,abs_of_pos hd,div_pow,integral_div] using he

end Hurst
