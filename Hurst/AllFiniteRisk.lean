import Hurst.MinimaxUpperTransfer

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem second_moment_le_higher_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (s : ℝ) (hs : 2≤s)
    (hX : MemLp X (ENNReal.ofReal s) P) :
    (∫ x,(X x)^2 ∂P)≤(∫ x,|X x|^s ∂P)^(2/s) := by
  have hs0 : 0<s := by linarith
  have h2 : (2:ENNReal)≤ENNReal.ofReal s := by simpa using (ENNReal.ofReal_le_ofReal hs)
  have hX2 := hX.mono_exponent h2
  have he := eLpNorm_le_eLpNorm_of_exponent_le h2 hX.aestronglyMeasurable
  rw [hX2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hX.eLpNorm_eq_integral_rpow_norm (by positivity) (by simp)] at he
  simp only [ENNReal.toReal_ofReal hs0.le,ENNReal.toReal_ofNat,Real.norm_eq_abs,Real.rpow_two,sq_abs] at he
  rw [show (2:ℝ)⁻¹=1/2 by norm_num,← Real.sqrt_eq_rpow] at he
  have hb := (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg
    (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)) _)).mp he
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  rw [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),← Real.rpow_two,
    ← Real.rpow_mul (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _))] at hh
  convert hh using 1 <;> first | rfl | congr 1 <;> ring

theorem unitLpRisk_le_uniform_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℝ) (hs : 2≤s)
    (F : Ω → ℝ → ℝ) (g : ℝ → ℝ) (C : ℝ)
    (hF : Measurable (fun z : Ω × ℝ => F z.1 z.2)) (hg : Continuous g)
    (hFc : ∀ x,Continuous (F x)) (hFb : ∀ x t,F x t∈Icc (0:ℝ) 1)
    (hgb : ∀ t,g t∈Icc (0:ℝ) 1)
    (hpoint : ∀ t∈Ioo (0:ℝ) 1,(∫ x,|F x t-g t|^s ∂P)≤C) :
    (∫ x,(unitLpLoss s (F x) g)^2 ∂P)≤C^(2/s) := by
  have hs0 : 0<s := by linarith
  have hdiff (x : Ω) (t : ℝ) : |F x t-g t|≤1 := by
    have hx := hFb x t
    have ht := hgb t
    exact abs_le.mpr ⟨by linarith [hx.1,ht.2],by linarith [hx.2,ht.1]⟩
  have hbound (x : Ω) : unitLpLoss s (F x) g≤1 := by
    have he := continuousHurstDecision_edist_le_bound ⟨s,by linarith⟩ (F x) g (hFc x) hg 1
      (fun t ht => hdiff x t)
    rw [continuousHurstDecision_distance_integral] at he
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp he
  have hmem : MemLp (fun x => unitLpLoss s (F x) g) (ENNReal.ofReal s) P := by
    apply MemLp.of_bound (unitLpLoss_measurable s F g hF hg.measurable).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (unitLpLoss_nonneg _ _ _)]; exact hbound x)
  have hi : Integrable (fun z : Ω × ℝ => |F z.1 z.2-g z.2|^s)
      (P.prod (volume.restrict (Ioo (0:ℝ) 1))) := by
    apply Integrable.of_bound (show Measurable (fun z : Ω × ℝ => |F z.1 z.2-g z.2|^s) by fun_prop).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_one (abs_nonneg _) (hdiff _ _) hs0.le
  have hI : (∫ x,|unitLpLoss s (F x) g|^s ∂P)≤C := by
    have hid (x : Ω) : |unitLpLoss s (F x) g|^s=∫ t in Ioo (0:ℝ) 1,|F x t-g t|^s := by
      rw [abs_of_nonneg (unitLpLoss_nonneg _ _ _),unitLpLoss,Real.rpow_inv_rpow]
      · exact integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) s)
      · exact hs0.ne'
    simp_rw [hid]
    rw [integral_integral_swap hi]
    have hh := integral_mono_ae hi.integral_prod_right (integrable_const C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hpoint t ht)
    simpa using hh
  exact (second_moment_le_higher_moment P _ s hs hmem).trans
    (Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)) hI (by positivity))

end Hurst
