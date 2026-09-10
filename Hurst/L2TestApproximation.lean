import Hurst.GaussianSymmetry

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem integral_abs_le_sqrt_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P) :
    (∫ ω,|X ω| ∂P) ≤ Real.sqrt (∫ ω,(X ω)^2 ∂P) := by
  have hc := abs_integral_mul_le_sqrt_integrals P (fun ω => |X ω|) (fun _ => 1)
    hX.abs (memLp_const 1)
  simpa only [mul_one,sq_abs,one_pow,integral_const,probReal_univ,smul_eq_mul,
    Real.sqrt_one,mul_one,abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] using hc

theorem bounded_lipschitz_integral_L2_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (φ : ℝ → ℝ)
    (hφ : LipschitzWith 1 φ) (hb : ∀ x,|φ x|≤1) :
    |(∫ ω,φ (X ω) ∂P)-(∫ ω,φ (Y ω) ∂P)| ≤
      Real.sqrt (∫ ω,(X ω-Y ω)^2 ∂P) := by
  have hi (Z : Ω → ℝ) (hZ : MemLp Z 2 P) : Integrable (fun ω => φ (Z ω)) P := by
    apply (integrable_const (1:ℝ)).mono'
      (hφ.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hb (Z ω))
  rw [← integral_sub (hi X hX) (hi Y hY)]
  calc
    _ ≤ ∫ ω,|φ (X ω)-φ (Y ω)| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => φ (X ω)-φ (Y ω))
    _ ≤ ∫ ω,|X ω-Y ω| ∂P := by
      apply integral_mono ((hi X hX).sub (hi Y hY)).abs ((hX.sub hY).integrable (by norm_num)).abs
      intro ω
      have hh : |φ (X ω)-φ (Y ω)|≤|X ω-Y ω| := by
        simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hφ.dist_le_mul (X ω) (Y ω)
      convert hh using 1 <;> rfl
    _ ≤ _ := integral_abs_le_sqrt_second_moment P _ (hX.sub hY)

end Hurst
