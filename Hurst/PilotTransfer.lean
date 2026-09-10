import Hurst.Moments
import Hurst.LocalPolynomial

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

def twoScalePilot {Ω : Type*} (G₁ G₂ : Ω → ℝ) : Ω → ℝ :=
  fun x => (G₂ x - G₁ x)/(2*Real.log 2)

theorem variance_sub_le_twice {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Var[fun x => X x - Y x; P] ≤ 2*(Var[X;P]+Var[Y;P]) := by
  have ha := variance_nonneg (X := fun x => X x + Y x) (μ := P)
  rw [variance_fun_add hX hY] at ha
  rw [variance_fun_sub hX hY]
  linarith

theorem twoScalePilot_memLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) : MemLp (twoScalePilot X Y) 2 P := by
  change MemLp (fun x => (Y x-X x)/(2*Real.log 2)) 2 P
  simp only [div_eq_mul_inv]
  exact (hY.sub hX).mul_const _

theorem twoScalePilot_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Var[twoScalePilot X Y; P] ≤ (Var[X;P]+Var[Y;P])/(2*(Real.log 2)^2) := by
  unfold twoScalePilot
  simp only [div_eq_mul_inv]
  rw [variance_mul_const, mul_comm (Var[fun x => Y x-X x; P])]
  have h := mul_le_mul_of_nonneg_left (variance_sub_le_twice P Y X hY hX) (sq_nonneg ((2*Real.log 2)⁻¹))
  calc
    _ ≤ (2*Real.log 2)⁻¹^2 * (2*(Var[Y;P]+Var[X;P])) := h
    _ = (Var[X;P]+Var[Y;P]) * (2*(Real.log 2)^2)⁻¹ := by ring

theorem twoScalePilot_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    (∫ x, twoScalePilot X Y x ∂P) = ((∫ x, Y x ∂P)-(∫ x, X x ∂P))/(2*Real.log 2) := by
  unfold twoScalePilot
  rw [integral_div, integral_sub hY hX]

theorem twoScalePilot_weighted_bias {ι : Type*} [Fintype ι]
    (w H B m₁ m₂ : ι → ℝ) (θ e₁ e₂ β : ℝ)
    (h₁ : ∀ i, |m₁ i - B i| ≤ e₁)
    (h₂ : ∀ i, |m₂ i - (B i + 2*Real.log 2*H i)| ≤ e₂)
    (hβ : |smooth w H - θ| ≤ β) :
    |(smooth w m₂-smooth w m₁)/(2*Real.log 2)-θ| ≤
      β + (∑ i, |w i|)*(e₁+e₂)/(2*Real.log 2) := by
  have hL : 0 < 2*Real.log 2 := by positivity
  let e := fun i => (m₂ i-(B i+2*Real.log 2*H i))-(m₁ i-B i)
  have herr : ∀ i, |e i| ≤ e₁+e₂ := by
    intro i
    exact (abs_sub _ _).trans (by linarith [h₁ i, h₂ i])
  have hr := smooth_residual_bound w e (e₁+e₂) herr
  have hid : (smooth w m₂-smooth w m₁)/(2*Real.log 2)-θ =
      (smooth w H-θ)+smooth w e/(2*Real.log 2) := by
    unfold smooth e
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_left_comm (w _) (2*Real.log 2), ← Finset.mul_sum]
    field_simp
    <;> ring
  rw [hid]
  have hh := abs_add_le (smooth w H-θ) (smooth w e/(2*Real.log 2))
  rw [abs_div, abs_of_pos hL] at hh
  exact hh.trans (add_le_add hβ ((div_le_div_iff_of_pos_right hL).mpr hr))

end Hurst
