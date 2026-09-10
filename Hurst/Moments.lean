import Hurst.Corrections
import Mathlib.Probability.Moments.Variance

/-! Exact probability-space identities used by the paper. All integrability
hypotheses are explicit. No Gaussian process or limit theorem is assumed to
have been constructed merely by importing this file. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Full MSE decomposition on an arbitrary probability space. -/
theorem mse_decomposition (X : Ω → ℝ) (θ : ℝ) (hX : MemLp X 2 μ) :
    (∫ ω, (X ω-θ)^2 ∂μ) = variance X μ + ((∫ ω, X ω ∂μ)-θ)^2 := by
  have hshift : MemLp (fun ω => X ω-θ) 2 μ := hX.sub (memLp_const θ)
  have hvar := variance_eq_sub hshift
  rw [variance_sub_const hX.aestronglyMeasurable θ] at hvar
  have hInt : (∫ ω, X ω-θ ∂μ) = (∫ ω, X ω ∂μ)-θ := by
    rw [integral_sub (hX.integrable one_le_two) (integrable_const θ), integral_const]
    simp
  change variance X μ = (∫ ω, (X ω-θ)^2 ∂μ) - (∫ ω, X ω-θ ∂μ)^2 at hvar
  rw [hInt] at hvar
  linarith

/-- Corrected form of S.3.17, starting from W=sZ with Z nonzero almost surely.
For standard Gaussian Z the remaining expectation is E log χ₁². -/
theorem expected_log_square_scale (Z : Ω → ℝ) (s : ℝ) (hs : s ≠ 0)
    (hZ : ∀ᵐ ω ∂μ, Z ω ≠ 0) (hint : Integrable (fun ω => Real.log ((Z ω)^2)) μ) :
    (∫ ω, Real.log ((s*Z ω)^2) ∂μ) = Real.log (s^2) + ∫ ω, Real.log ((Z ω)^2) ∂μ := by
  calc
    (∫ ω, Real.log ((s*Z ω)^2) ∂μ) =
        ∫ ω, Real.log (s^2)+Real.log ((Z ω)^2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hZ] with ω hω
      exact log_square_scale s (Z ω) hs hω
    _ = _ := by rw [integral_add (integrable_const _) hint, integral_const]; simp

/-- Joint law is not needed for this algebraic part of the Hermite rank-two argument. -/
theorem centered_square_covariance (X Y : Ω → ℝ)
    (hX : Integrable (fun ω => (X ω)^2) μ)
    (hY : Integrable (fun ω => (Y ω)^2) μ)
    (hXY : Integrable (fun ω => (X ω)^2*(Y ω)^2) μ)
    (hx : (∫ ω, (X ω)^2 ∂μ) = 1) (hy : (∫ ω, (Y ω)^2 ∂μ) = 1) :
    (∫ ω, ((X ω)^2-1)*((Y ω)^2-1) ∂μ) = (∫ ω, (X ω)^2*(Y ω)^2 ∂μ)-1 := by
  have he : (fun ω => ((X ω)^2-1)*((Y ω)^2-1)) =
      (fun ω => ((X ω)^2*(Y ω)^2-(X ω)^2)-(Y ω)^2+1) := by funext ω; ring
  rw [he]
  have hsub : Integrable (fun ω => (X ω)^2*(Y ω)^2-(X ω)^2-(Y ω)^2) μ := (hXY.sub hX).sub hY
  have hsub1 : Integrable (fun ω => (X ω)^2*(Y ω)^2-(X ω)^2) μ := hXY.sub hX
  rw [integral_add hsub (integrable_const 1),
    integral_sub hsub1 hY, integral_sub hXY hX, hx, hy, integral_const]
  simp

end Hurst
