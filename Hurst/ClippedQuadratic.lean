import Hurst.LogCorrectionSmooth

noncomputable section
open Set
namespace Hurst

theorem clip_displacement_quadratic (l u x H d : ℝ) (hd : 0<d)
    (hlH : l+d≤H) (hHu : H+d≤u) :
    |clip l u x-x|≤|x-H|^2/d := by
  have hlu : l≤u := by linarith
  by_cases hx : x<l
  · have hclip : clip l u x=l := by
      simp [clip,min_eq_right (hx.le.trans (by linarith : l≤u)),max_eq_left hx.le]
    rw [hclip,abs_of_nonneg (by linarith : 0≤l-x),abs_of_nonpos (by linarith : x-H≤0)]
    have hxd : d≤H-x := by linarith
    have hx0 : 0≤H-x := by linarith
    have hmul := mul_le_mul_of_nonneg_right hxd hx0
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · by_cases hu : u<x
    · have hclip : clip l u x=u := by
        simp [clip,min_eq_left hu.le,max_eq_right (by linarith : l≤u)]
      rw [hclip,abs_of_nonpos (by linarith : u-x≤0),abs_of_nonneg (by linarith : 0≤x-H)]
      have hxd : d≤x-H := by linarith
      have hx0 : 0≤x-H := by linarith
      have hmul := mul_le_mul_of_nonneg_right hxd hx0
      apply (le_div_iff₀ hd).mpr
      nlinarith
    · rw [clip_identity l u x ⟨le_of_not_gt hx,le_of_not_gt hu⟩,sub_self,abs_zero]
      positivity

/-- Taylor's quadratic remainder remains quadratic after clipping, provided
the true value stays a fixed positive distance from both clipping endpoints. -/
theorem q2LogCorrection_clipped_quadratic (l u d : ℝ)
    (hl : 0<l) (hu : u<1) (hlu : l≤u) (hd : 0<d) :
    ∃ C≥0,∀ x H : ℝ,H∈Icc (l+d) (u-d) →
      |q2LogCorrection (clip l u x)-q2LogCorrection H-
        (x-H)*deriv q2LogCorrection H|≤C*|x-H|^2 := by
  obtain ⟨C,hC,hquad⟩ := q2LogCorrection_uniform_quadratic l u hl hu
  obtain ⟨K,hK,hderiv⟩ := q2LogCorrection_uniform_derivative l u hl hu
  refine ⟨C+K/d,by positivity,?_⟩
  intro x H hH
  have hH' : H∈Icc l u := ⟨by linarith [hH.1],by linarith [hH.2]⟩
  have hclip := clip_mem l u x hlu
  have hq := hquad H (clip l u x) hH' hclip
  have hc := clip_displacement_quadratic l u x H d hd hH.1 (by linarith [hH.2])
  have hdv := hderiv H hH'
  have hid : q2LogCorrection (clip l u x)-q2LogCorrection H-(x-H)*deriv q2LogCorrection H =
      (q2LogCorrection (clip l u x)-q2LogCorrection H-
        (clip l u x-H)*deriv q2LogCorrection H)+
      (clip l u x-x)*deriv q2LogCorrection H := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have hcliperr := clip_error l u x H hH'
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hcliperr 2
  calc
    _ ≤ C * |clip l u x-H|^2+|clip l u x-x| * |deriv q2LogCorrection H| :=
      add_le_add hq le_rfl
    _ ≤ C * |x-H|^2+(|x-H|^2/d)*K := add_le_add
      (mul_le_mul_of_nonneg_left hsq hC)
      (mul_le_mul hc hdv (abs_nonneg _) (by positivity))
    _ = (C+K/d)*|x-H|^2 := by ring

end Hurst
