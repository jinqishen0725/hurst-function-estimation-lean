import Hurst.InverseRepair
import Hurst.DirectBiasRepair

/-! Rate consequences of the repaired finite-sample inequalities.
Input-model rates remain explicit premises, so these do not assert an
unproved covariance bound for mBm. -/
noncomputable section
open MeasureTheory ProbabilityTheory Asymptotics Filter Set
open scoped Topology
namespace Hurst

/-- Scaling a nonnegative error bound preserves its Big-O rate. -/
theorem rate_transfer_div_square (U V m R : ℕ → ℝ)
    (hU : ∀ n, 0 ≤ U n) (hbound : ∀ n, U n ≤ V n/(m n)^2)
    (hV : V =O[atTop] R) : U =O[atTop] (fun n => R n/(m n)^2) := by
  have hUV : U =O[atTop] (fun n => V n/(m n)^2) :=
    IsBigO.of_norm_le (fun n => by simpa [Real.norm_eq_abs, abs_of_nonneg (hU n)] using hbound n)
  have hprod := hV.mul (isBigO_refl (fun n => ((m n)^2)⁻¹) atTop)
  exact hUV.trans (by simpa only [div_eq_mul_inv] using hprod)

/-- A full statistical rate-transfer theorem for a sequence of repaired
inverse estimators. It accepts changing calibrations, cutoffs and slopes. -/
theorem boundedInverse_rate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (f : ℕ → ℝ → ℝ) (a b m R : ℕ → ℝ) (H : ℝ)
    (hm : ∀ n, 0 < m n) (hab : ∀ n, a n ≤ b n)
    (hc : ∀ n, ContinuousOn (f n) (Icc (a n) (b n)))
    (hf : ∀ n, StrongDecrease (f n) (a n) (b n) (m n))
    (hH : ∀ n, H ∈ Icc (a n) (b n)) (hX : ∀ n, MemLp (X n) 2 μ)
    (hinput : (fun n => variance (X n) μ + ((∫ ω, X n ω ∂μ)-f n H)^2) =O[atTop] R) :
    (fun n => ∫ ω, (boundedInverse (f n) (a n) (b n) (X n ω)-H)^2 ∂μ)
      =O[atTop] (fun n => R n/(m n)^2) :=
  rate_transfer_div_square _ _ m R (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun n => boundedInverse_mse μ (X n) (f n) (a n) (b n) (m n) H
      (hm n) (hab n) (hc n) (hf n) (hH n) (hX n)) hinput

end Hurst
