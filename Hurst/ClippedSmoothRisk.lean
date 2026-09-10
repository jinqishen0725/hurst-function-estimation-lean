import Hurst.ClippedSmooth
import Hurst.SpatialRisk

noncomputable section
open Set MeasureTheory
namespace Hurst

theorem smooth_clipped_memLp_mse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (phi : ℝ → ℝ) (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Ioo (0 : ℝ) 1))
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 1, ∀ H : ℝ, H ∈ Icc a b → ∀ X : Ω → ℝ, MemLp X 2 P →
      MemLp (fun x => phi (clip a b (X x))-phi H) 2 P ∧
      (∫ x, (phi (clip a b (X x))-phi H)^2 ∂P) ≤ C^2*(∫ x, (X x-H)^2 ∂P) := by
  obtain ⟨C, hC, herr⟩ := smooth_clipped_error phi hphi a b ha hb
  refine ⟨C, hC, ?_⟩
  intro H hH X hX
  have hC0 : 0 ≤ C := by linarith
  have hcont : Continuous (fun y => phi (clip a b y)) :=
    (hphi.continuousOn.mono (fun y hy => ⟨ha.trans_le hy.1, hy.2.trans_lt hb⟩)).comp_continuous
      (clip_continuous a b) (fun y => clip_mem a b y (hH.1.trans hH.2))
  have hbase : MemLp (fun x => X x-H) 2 P := hX.sub (memLp_const H)
  have hm : AEStronglyMeasurable (fun x => phi (clip a b (X x))-phi H) P :=
    (hcont.comp_aestronglyMeasurable hX.aestronglyMeasurable).sub aestronglyMeasurable_const
  have hmem := (hbase.const_mul C).of_le hm (by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC0] using herr (X x) H hH)
  refine ⟨hmem, ?_⟩
  have hi := integral_mono hmem.integrable_sq (hbase.integrable_sq.const_mul (C^2)) (fun x => by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (herr (X x) H hH) 2
    simpa only [sq_abs, mul_pow] using hh)
  rwa [integral_const_mul] at hi

end Hurst
