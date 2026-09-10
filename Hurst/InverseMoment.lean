import Hurst.AllFiniteRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem boundedInverse_rpow_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (G : ℝ → ℝ)
    (a b m H s : ℝ) (hm : 0<m) (hs : 1≤s) (hab : a≤b)
    (hc : ContinuousOn G (Icc a b)) (hG : StrongDecrease G a b m) (hH : H∈Icc a b)
    (hX : MemLp X (ENNReal.ofReal s) P) :
    (∫ x,|boundedInverse G a b (X x)-H|^s ∂P)≤(∫ x,|X x-G H|^s ∂P)/m^s := by
  have hs0 : 0<s := by linarith
  have hY : MemLp (fun x => boundedInverse G a b (X x)) (ENNReal.ofReal s) P := by
    apply memLp_of_bounded (Filter.Eventually.of_forall (fun x => (boundedInverse_spec G a b (X x) hab hc).1))
    exact (boundedInverse_lipschitz G a b m hm hab hc hG).continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable
  have hi : Integrable (fun x => |boundedInverse G a b (X x)-H|^s) P := by
    convert (hY.sub (memLp_const H)).integrable_norm_rpow' using 1 <;> simp only [Real.norm_eq_abs,Pi.sub_apply,ENNReal.toReal_ofReal hs0.le]
  have hraw : Integrable (fun x => |X x-G H|^s) P := by
    convert (hX.sub (memLp_const (G H))).integrable_norm_rpow' using 1 <;> simp only [Real.norm_eq_abs,Pi.sub_apply,ENNReal.toReal_ofReal hs0.le]
  calc
    _ ≤ ∫ x,|X x-G H|^s/m^s ∂P := by
      apply integral_mono hi (hraw.div_const _)
      intro x
      have he := Real.rpow_le_rpow (abs_nonneg _) (boundedInverse_error G a b m (X x) H hm hab hc hG hH) hs0.le
      rwa [Real.div_rpow (abs_nonneg _) hm.le] at he
    _ = _ := integral_div _ _

theorem boundedInverse_moment_rate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (G : ℝ → ℝ)
    (a b m H s e : ℝ) (hm : 0<m) (hs : 1≤s) (he : 0≤e) (hab : a≤b)
    (hc : ContinuousOn G (Icc a b)) (hG : StrongDecrease G a b m) (hH : H∈Icc a b)
    (hX : MemLp X (ENNReal.ofReal s) P)
    (hraw : (∫ x,|X x-G H|^s ∂P)≤(m*e)^s) :
    (∫ x,|boundedInverse G a b (X x)-H|^s ∂P)≤e^s := by
  apply (boundedInverse_rpow_moment P X G a b m H s hm hs hab hc hG hH hX).trans
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hm s)).mpr
  rw [Real.mul_rpow hm.le he] at hraw
  simpa only [mul_comm] using hraw

theorem unitLpRisk_rate_of_uniform_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℝ) (hs : 2≤s) (e : ℝ) (he : 0≤e)
    (F : Ω → ℝ → ℝ) (g : ℝ → ℝ)
    (hF : Measurable (fun z : Ω × ℝ => F z.1 z.2)) (hg : Continuous g)
    (hFc : ∀ x,Continuous (F x)) (hFb : ∀ x t,F x t∈Icc (0:ℝ) 1)
    (hgb : ∀ t,g t∈Icc (0:ℝ) 1)
    (hpoint : ∀ t∈Ioo (0:ℝ) 1,(∫ x,|F x t-g t|^s ∂P)≤e^s) :
    (∫ x,(unitLpLoss s (F x) g)^2 ∂P)≤e^2 := by
  have hh := unitLpRisk_le_uniform_moment P s hs F g (e^s) hF hg hFc hFb hgb hpoint
  have hs0 : s≠0 := by linarith
  rw [← Real.rpow_mul he,show s*(2/s)=2 by field_simp,Real.rpow_two] at hh
  exact hh

end Hurst
