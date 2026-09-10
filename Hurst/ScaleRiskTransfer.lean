import Hurst.Moments

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

theorem scale_mse_from_components {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (θ B V R : ℝ)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hb : |(∫ x, X x ∂P)-θ| ≤ B) (hv : Var[X;P] ≤ V) (hr : (∫ x, (Y x)^2 ∂P) ≤ R) :
    (∫ x, (X x-θ-Y x)^2 ∂P) ≤ 2*V+2*B^2+2*R := by
  have hx : MemLp (fun x => X x-θ) 2 P := hX.sub (memLp_const θ)
  have hh := integral_mono (hx.sub hY).integrable_sq
    ((hx.integrable_sq.const_mul 2).add (hY.integrable_sq.const_mul 2))
    (fun x => by dsimp only [Pi.sub_apply, Pi.add_apply]; nlinarith [sq_nonneg (X x-θ+Y x)])
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  rw [integral_add (hx.integrable_sq.const_mul 2) (hY.integrable_sq.const_mul 2), integral_const_mul, integral_const_mul,
    mse_decomposition X θ hX] at hh
  have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hb2
  nlinarith

theorem nonnegative_four_term_bound (a b c d x y z t C : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (ha : a ≤ C) (hb : b ≤ C) (hc : c ≤ C) (hd : d ≤ C) :
    a*x+b*y+c*z+d*t ≤ C*(x+y+z+t) := by
  have h1 := mul_le_mul_of_nonneg_right ha hx
  have h2 := mul_le_mul_of_nonneg_right hb hy
  have h3 := mul_le_mul_of_nonneg_right hc hz
  have h4 := mul_le_mul_of_nonneg_right hd ht
  nlinarith

/-- Collapse the scale estimator's proved component rates into four uniform terms. -/
theorem scale_component_rate_bound (Bl El Vl Bp Ep Vp C : ℝ)
    (hVl : 0 ≤ Vl) (hVp : 0 ≤ Vp) :
    ∃ K ≥ 0, ∀ L z e u v : ℝ, 1 ≤ L → 0 ≤ u → 0 ≤ v →
      2*(Vl*L^2*u+2*(Bl*L*z)^2+2*(L*(El*e))^2)+
        2*C^2*(Vp*v+2*(Bp*z)^2+2*(Ep*e)^2) ≤
      K*((L*z)^2+(L*e)^2+L^2*u+v) := by
  let A := 4*Bl^2+4*C^2*Bp^2
  let B := 4*El^2+4*C^2*Ep^2
  let D := 2*Vl
  let F := 2*C^2*Vp
  let K := max A (max B (max D F))
  have hA : A ≤ K := le_max_left _ _
  have hB : B ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hD : D ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hF : F ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨K, (show 0 ≤ A by dsimp [A]; positivity).trans hA, ?_⟩
  intro L z e u v hL hu hv
  have hL2 : 1 ≤ L^2 := by nlinarith
  have hz := mul_le_mul_of_nonneg_right hL2 (show 0 ≤ 4*C^2*Bp^2*z^2 by positivity)
  have he := mul_le_mul_of_nonneg_right hL2 (show 0 ≤ 4*C^2*Ep^2*e^2 by positivity)
  apply le_trans _ (nonnegative_four_term_bound A B D F ((L*z)^2) ((L*e)^2) (L^2*u) v K
    (sq_nonneg _) (sq_nonneg _) (mul_nonneg (sq_nonneg _) hu) hv hA hB hD hF)
  dsimp [A,B,D,F]
  nlinarith

end Hurst
