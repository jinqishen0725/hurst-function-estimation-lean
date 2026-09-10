import Hurst.ClippedLinearization
import Hurst.L2TestApproximation

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

theorem boundedInverse_memLp_two {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (G : ℝ → ℝ) (a b m : ℝ) (hm : 0<m) (hab : a≤b)
    (hc : ContinuousOn G (Icc a b)) (hG : StrongDecrease G a b m) :
    MemLp (fun ω => boundedInverse G a b (X ω)) 2 P := by
  apply MemLp.of_bound ((boundedInverse_lipschitz G a b m hm hab hc hG).continuous.comp_aestronglyMeasurable
    hX.aestronglyMeasurable) (|a|+|b|)
  exact Filter.Eventually.of_forall (fun ω => by
    have hr := (boundedInverse_spec G a b (X ω) hab hc).1
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith [hr.1,hr.2,neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b])

theorem boundedInverse_expected_linearization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (φ : ℝ → ℝ) (a b m c H d K : ℝ)
    (hm : 0<m) (hd : 0<d) (hK : 0≤K) (hHa : a+d≤H) (hHb : H+d≤b)
    (hc : ContinuousOn (fun z => -m*z+φ z+c) (Icc a b))
    (hφ : ∀ z∈Icc a b,|φ z-φ H|≤K*|z-H|)
    (hG : StrongDecrease (fun z => -m*z+φ z+c) a b m) :
    |(∫ ω,boundedInverse (fun z => -m*z+φ z+c) a b (X ω) ∂P)-H+
      ((∫ ω,X ω ∂P)-(-m*H+φ H+c))/m| ≤
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
  have hYc : Integrable (fun ω => Y ω-H) P := (hY.integrable (by norm_num)).sub (integrable_const H)
  have hIntY : (∫ ω,Y ω-H ∂P)=(∫ ω,Y ω ∂P)-H := by
    simpa only [Pi.sub_apply,integral_const,probReal_univ,one_smul] using
      integral_sub (hY.integrable (by norm_num)) (integrable_const H)
  have hInte : (∫ ω,e ω ∂P)=(∫ ω,X ω ∂P)-G H := by
    simpa only [e,Pi.sub_apply,integral_const,probReal_univ,one_smul] using
      integral_sub (hX.integrable (by norm_num)) (integrable_const (G H))
  have hident : (∫ ω,Y ω ∂P)-H+((∫ ω,X ω ∂P)-G H)/m = ∫ ω,Y ω-H+e ω/m ∂P := by
    rw [integral_add hYc ((he.integrable (by norm_num)).div_const m),hIntY,integral_div,hInte]
  change |(∫ ω,Y ω ∂P)-H+((∫ ω,X ω ∂P)-G H)/m| ≤ _
  rw [hident]
  calc
    _ ≤ ∫ ω,|Y ω-H+e ω/m| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => Y ω-H+e ω/m)
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
