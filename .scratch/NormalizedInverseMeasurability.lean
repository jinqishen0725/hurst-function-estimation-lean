import Hurst.ActualUnknownConditionalLimits

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

theorem normalized_q1_inverse_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (X : Ω → ℝ) (hX : Measurable X) (A H : ℝ) :
    Measurable (fun x => 2*A*Real.log n*(boundedInverse (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (X x)-H)) := by
  by_cases hn : 1<n
  · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n)
      (by positivity) (by norm_num) (calibrationOne_continuous _ _).continuousOn
      (calibrationOne_strongDecrease _ _ _ _)).continuous.measurable
    exact ((hi.comp hX).sub measurable_const).const_mul _
  · have hn' : n≤1 := by omega
    have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
    simp only [hl,mul_zero,zero_mul]
    exact measurable_const

theorem normalized_q2_inverse_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (u : ℝ) (hu0 : 0≤u) (hu : u<1) (X : Ω → ℝ) (hX : Measurable X) (A H : ℝ) :
    Measurable (fun x => 2*A*Real.log n*(boundedInverse (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (X x)-H)) := by
  by_cases hn : 1<n
  · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hi := (boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (2*Real.log n)
      (by positivity) hu0 (calibrationTwo_continuousOn _ _ u hu)
      (calibrationTwo_strongDecrease _ _ u hu)).continuous.measurable
    exact ((hi.comp hX).sub measurable_const).const_mul _
  · have hn' : n≤1 := by omega
    have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
    simp only [hl,mul_zero,zero_mul]
    exact measurable_const

end Hurst
