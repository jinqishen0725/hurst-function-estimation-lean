import Hurst.ExpectedLinearization

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

theorem boundedInverse_L1_linearization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (φ : ℝ → ℝ) (a b m c H d K : ℝ)
    (hm : 0<m) (hd : 0<d) (hK : 0≤K) (hHa : a+d≤H) (hHb : H+d≤b)
    (hc : ContinuousOn (fun z => -m*z+φ z+c) (Icc a b))
    (hφ : ∀ z∈Icc a b,|φ z-φ H|≤K*|z-H|)
    (hG : StrongDecrease (fun z => -m*z+φ z+c) a b m) :
    (∫ ω,|boundedInverse (fun z => -m*z+φ z+c) a b (X ω)-H+
      (X ω-(-m*H+φ H+c))/m| ∂P) ≤
      K*Real.sqrt (∫ ω,(X ω-(-m*H+φ H+c))^2 ∂P)/m^2+
        (∫ ω,(X ω-(-m*H+φ H+c))^2 ∂P)/(m^2*d) := by
  let G := fun z => -m*z+φ z+c
  let Y := fun ω => boundedInverse G a b (X ω)
  let e := fun ω => X ω-G H
  have hY : MemLp Y 2 P := boundedInverse_memLp_two P X hX G a b m hm (by linarith) hc hG
  have he : MemLp e 2 P := hX.sub (memLp_const (G H))
  have hRi : Integrable (fun ω => Y ω-H+e ω/m) P :=
    ((hY.integrable (by norm_num)).sub (integrable_const H)).add ((he.integrable (by norm_num)).div_const m)
  have hBi : Integrable (fun ω => K*|e ω|/m^2+(e ω)^2/(m^2*d)) P :=
    ((((he.integrable (by norm_num)).abs.const_mul K).div_const _).add (he.integrable_sq.div_const _))
  change (∫ ω,|Y ω-H+e ω/m| ∂P) ≤ _
  calc
    _ ≤ ∫ ω,K*|e ω|/m^2+(e ω)^2/(m^2*d) ∂P := by
      apply integral_mono hRi.abs hBi
      intro ω
      exact boundedInverse_linearization φ a b m c H d K (X ω) hm hd hK hHa hHb hc hφ hG
    _ = K*(∫ ω,|e ω| ∂P)/m^2+(∫ ω,(e ω)^2 ∂P)/(m^2*d) := by
      rw [integral_add (((he.integrable (by norm_num)).abs.const_mul K).div_const _)
        (he.integrable_sq.div_const _),integral_div,integral_div,integral_const_mul]
    _ ≤ _ := by
      have hh := integral_abs_le_sqrt_second_moment P e he
      exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hK) (sq_nonneg m)) le_rfl


end Hurst
