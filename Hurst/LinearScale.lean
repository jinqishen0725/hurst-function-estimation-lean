import Hurst.PilotTransfer
import Hurst.MergedLogVariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem variance_add_le_twice {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Var[fun x => X x+Y x; P] ≤ 2*(Var[X;P]+Var[Y;P]) := by
  have ha := variance_nonneg (X := fun x => X x-Y x) (μ := P)
  rw [variance_fun_sub hX hY] at ha
  rw [variance_fun_add hX hY]
  linarith

theorem variance_linear_combination_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (a b : ℝ) : Var[fun x => a*X x+b*Y x; P] ≤ 2*a^2*Var[X;P]+2*b^2*Var[Y;P] := by
  have he := variance_add_le_twice P (fun x => a*X x) (fun x => b*Y x) (hX.const_mul a) (hY.const_mul b)
  rw [variance_const_mul, variance_const_mul] at he
  exact he.trans_eq (by ring)

def linearScaleCombination {Ω : Type*} (L : ℝ) (X Y : Ω → ℝ) : Ω → ℝ :=
  fun x => (1-L/Real.log 2)*X x+(L/Real.log 2)*Y x

theorem linearScaleCombination_pilot_identity {Ω : Type*} (L : ℝ) (X Y : Ω → ℝ) :
    linearScaleCombination L X Y = fun x => X x+2*L*twoScalePilot X Y x := by
  funext x
  unfold linearScaleCombination twoScalePilot
  ring

theorem linearScaleCombination_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (L : ℝ) (hL : 1 ≤ L) :
    Var[linearScaleCombination L X Y; P] ≤
      (4+4/(Real.log 2)^2)*L^2*(Var[X;P]+Var[Y;P]) := by
  have hl : 0 < Real.log 2 := by positivity
  have hL2 : 1 ≤ L^2 := by nlinarith
  have ha : (1-L/Real.log 2)^2 ≤ (2+2/(Real.log 2)^2)*L^2 := by
    have hh : (1-L/Real.log 2)^2 ≤ 2+2*(L/Real.log 2)^2 := by nlinarith [sq_nonneg (1+L/Real.log 2)]
    rw [div_pow] at hh
    have he : 2+2*(L^2/(Real.log 2)^2) ≤ (2+2/(Real.log 2)^2)*L^2 := by simp only [div_eq_mul_inv] at *; nlinarith
    exact hh.trans he
  have hb : (L/Real.log 2)^2 ≤ (2+2/(Real.log 2)^2)*L^2 := by
    rw [div_pow]
    have he : 0 ≤ L^2/(Real.log 2)^2 := by positivity
    simp only [div_eq_mul_inv] at *
    nlinarith [sq_nonneg L]
  have he := variance_linear_combination_le P X Y hX hY (1-L/Real.log 2) (L/Real.log 2)
  have hvx := variance_nonneg (X := X) (μ := P)
  have hvy := variance_nonneg (X := Y) (μ := P)
  have hax := mul_le_mul_of_nonneg_right ha hvx
  have hby := mul_le_mul_of_nonneg_right hb hvy
  change Var[fun x => (1-L/Real.log 2)*X x+(L/Real.log 2)*Y x; P] ≤ _
  simp only [div_eq_mul_inv] at *
  nlinarith

end Hurst
