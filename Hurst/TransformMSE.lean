import Hurst.Moments

noncomputable section
open Set MeasureTheory
namespace Hurst

theorem continuous_transform_mse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → ℝ) (hF : Continuous F)
    (θ c C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, |F y-c| ≤ C*|y-θ|)
    (X : Ω → ℝ) (hX : MemLp X 2 P) :
    MemLp (fun x => F (X x)-c) 2 P ∧
    (∫ x, (F (X x)-c)^2 ∂P) ≤ C^2*(∫ x, (X x-θ)^2 ∂P) := by
  have hbase : MemLp (fun x => X x-θ) 2 P := hX.sub (memLp_const θ)
  have hm : AEStronglyMeasurable (fun x => F (X x)-c) P :=
    (hF.comp_aestronglyMeasurable hX.aestronglyMeasurable).sub aestronglyMeasurable_const
  have hmem := (hbase.const_mul C).of_le hm (by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC] using hbound (X x))
  refine ⟨hmem, ?_⟩
  have hi := integral_mono hmem.integrable_sq (hbase.integrable_sq.const_mul (C^2)) (fun x => by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hbound (X x)) 2
    simpa only [sq_abs, mul_pow] using hh)
  rwa [integral_const_mul] at hi

end Hurst
