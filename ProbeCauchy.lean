import Mathlib
import Hurst.RieszOperatorPositivity

open MeasureTheory Measure Real Set

#check @MeasureTheory.setIntegral_one
#check @MeasureTheory.Measure.real_restrict
#check @Real.volume_real_Iio
#check @AEStronglyMeasurable.mul
#check @MeasureTheory.Integrable.aestronglyMeasurable
#check @MeasureTheory.Measure.prod_prod
#check @MeasureTheory.MemLp.mul
#check @MeasureTheory.MemLp.comp_snd
#check @MeasureTheory.ae_iff
example : volume (Iio (1:ℝ)) = 1 := by simp
example (m : ℝ) (hm : 0 < m) (hm1 : m ≤ 1) :
    (volume.restrict (Iio (1:ℝ))).real (Iio m) = m := by
  rw [Measure.real_restrict (measurableSet_Iio _) (measurableSet_Iio _)]
  sorry
example (u : ℝ) (x v : ℝ) :
    MeasurableSet {q : (ℝ × ℝ) × ℝ | q.2 < exp (-(2 * u * q.1.1))} := by measurability
example (u : ℝ) : Measurable (fun q : (ℝ × ℝ) × ℝ => exp (u * q.1.1)) := by measurability
example (u : ℝ) : Measurable (fun q : (ℝ × ℝ) × ℝ =>
    (Iio (exp (-(2 * u * q.1.1)))).indicator 1 q.2) := by measurability
