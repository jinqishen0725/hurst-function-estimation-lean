import Mathlib
import Hurst.RieszOperatorPositivity

open MeasureTheory Measure Real Set

#check @MeasureTheory.integral_prod
#check @MeasureTheory.integral_prod_swap
#check @MeasureTheory.integral_prod_mul
#check @MeasureTheory.integral_mul_right
#check @MeasureTheory.integral_mul_left
#check @MeasureTheory.integral_indicator
#check @MeasureTheory.integral_nonneg
#check @MeasureTheory.setIntegral_nonneg
#check @MeasureTheory.Integrable.prod_mul
#check @MeasureTheory.Integrable.mono
#check @MeasureTheory.Integrable.abs
#check @MeasureTheory.memLp_one_iff_integrable
#check @MeasureTheory.MemLp.of_exponent
#check @MeasureTheory.Lp.memLp
#check @Real.Gamma_one
#check @MeasureTheory.integral_rpow_mul_exp_neg_mul_rpow
#check @Set.indicator_inter_mul
#check @Set.indicator_mul_indicator
#check @MeasureTheory.integral_congr_ae
#check @MeasureTheory.integral_congr
#check @HS.Lp.memLp
#check @HS.volIsFin
example : MeasurableSet (Ici (0:ℝ)) := measurableSet_Ici
#check @MeasureTheory.setIntegral_add_right_eq
#check @MeasureTheory.setIntegral_add_left_eq
#check @MeasureTheory.integral_add_right_eq
#check @MeasureTheory.integral_add_left_eq_self
#check @MeasureTheory.Integrable.const_mul
#check @MeasureTheory.aestronglyMeasurable_comp
#check @MeasureTheory.Integrable.comp_fst
#check @MeasureTheory.Integrable.comp_snd
#check @HS.kpair
#check @HS.KernelPSD
