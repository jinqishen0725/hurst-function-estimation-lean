import Hurst.InverseRepair
import Hurst.TransformMSE

noncomputable section
open Set MeasureTheory
namespace Hurst

theorem boundedInverse_backfit_mse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (f : ℝ → ℝ) (a b m θ : ℝ) (hm : 0 < m) (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hf : StrongDecrease f a b m) (hθ : θ ∈ Icc a b)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    (∫ x, (boundedInverse f a b (X x-Y x)-θ)^2 ∂P) ≤
      2*(∫ x, (boundedInverse f a b (X x)-θ)^2 ∂P)+2/m^2*(∫ x, (Y x)^2 ∂P) := by
  have hlip := boundedInverse_lipschitz f a b m hm hab hc hf
  have hbound : ∀ y, |boundedInverse f a b y-θ| ≤ m⁻¹*|y-f θ| := by
    intro y
    simpa only [div_eq_mul_inv, mul_comm] using boundedInverse_error f a b m y θ hm hab hc hf hθ
  have hbase := (continuous_transform_mse P _ hlip.continuous (f θ) θ m⁻¹ (by positivity) hbound X hX).1
  have hnew := (continuous_transform_mse P _ hlip.continuous (f θ) θ m⁻¹ (by positivity) hbound (X-Y) (hX.sub hY)).1
  have hpoint : ∀ x, (boundedInverse f a b (X x-Y x)-θ)^2 ≤
      2*(boundedInverse f a b (X x)-θ)^2+(2/m^2)*(Y x)^2 := by
    intro x
    have he := hlip.dist_le_mul (X x-Y x) (X x)
    simp only [Real.dist_eq, NNReal.coe_mk, sub_sub_cancel_left, abs_neg] at he
    change |boundedInverse f a b (X x-Y x)-boundedInverse f a b (X x)| ≤ m⁻¹*|Y x| at he
    have ha := abs_add_le (boundedInverse f a b (X x-Y x)-boundedInverse f a b (X x))
      (boundedInverse f a b (X x)-θ)
    rw [sub_add_sub_cancel] at ha
    have hh := pow_le_pow_left₀ (abs_nonneg _) (ha.trans (add_le_add he le_rfl)) 2
    rw [sq_abs] at hh
    have hd := sq_nonneg (m⁻¹*|Y x|-|boundedInverse f a b (X x)-θ|)
    have heq : (2/m^2)*(Y x)^2 = 2*(m⁻¹*|Y x|)^2 := by
      rw [mul_pow, sq_abs]
      field_simp
    rw [heq]
    nlinarith [sq_abs (boundedInverse f a b (X x)-θ)]
  have hh := integral_mono hnew.integrable_sq
    ((hbase.integrable_sq.const_mul 2).add (hY.integrable_sq.const_mul (2/m^2))) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  rwa [integral_add (hbase.integrable_sq.const_mul 2) (hY.integrable_sq.const_mul (2/m^2)), integral_const_mul, integral_const_mul] at hh

end Hurst
