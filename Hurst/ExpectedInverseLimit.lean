import Hurst.ExpectedLinearization
import Hurst.MeanLimitTransfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem boundedInverse_expected_leading {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)] (X : ∀ n,Ω n → ℝ)
    (hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n))
    (φ : ℝ → ℝ) (a b c H d K A β : ℝ) (L ρ : ℕ → ℝ)
    (hd : 0<d) (hK : 0≤K) (hA : 0≤A) (hHa : a+d≤H) (hHb : H+d≤b)
    (hc : ContinuousOn φ (Icc a b))
    (hφ : ∀ z∈Icc a b,|φ z-φ H|≤K*|z-H|)
    (hG : ∀ n,StrongDecrease (fun z => -(2*L n)*z+φ z+c) a b (2*L n))
    (hL : Tendsto L atTop atTop) (hρpos : ∀ᶠ n in atTop,0<ρ n) (hρ : Tendsto ρ atTop (𝓝 0))
    (hmean : Tendsto (fun n => ((∫ ω,X n ω ∂P n)-(-(2*L n)*H+φ H+c))/(L n*ρ n)) atTop (𝓝 β))
    (hQ : ∀ᶠ n in atTop,(∫ ω,(X n ω-(-(2*L n)*H+φ H+c))^2 ∂P n)≤A^2*(L n)^2*(ρ n)^2) :
    Tendsto (fun n => ((∫ ω,boundedInverse (fun z => -(2*L n)*z+φ z+c) a b (X n ω) ∂P n)-H)/ρ n)
      atTop (𝓝 (-β/2)) := by
  have hpos : ∀ᶠ n in atTop,0<L n := hL.eventually_gt_atTop 0
  have hlin : Tendsto (fun n => -((∫ ω,X n ω ∂P n)-(-(2*L n)*H+φ H+c))/(2*L n)/ρ n)
      atTop (𝓝 (-β/2)) := by
    convert hmean.const_mul (-(1/2:ℝ)) using 1 <;> first | (funext n; ring) | ring
  have hsmall : Tendsto (fun n => K*A/(4*L n)+A^2*ρ n/(4*d)) atTop (𝓝 0) := by
    have hh := ((tendsto_inv_atTop_zero.comp hL).const_mul (K*A/4)).add (hρ.const_mul (A^2/(4*d)))
    simp only [mul_zero,add_zero] at hh
    convert hh using 1 <;> first | (funext n; simp only [Function.comp_apply]; ring) | rfl
  apply scalar_approximation_tendsto hlin hsmall (C := 1)
  filter_upwards [hX,hpos,hρpos,hQ] with n hn hLn hρn hQn
  have hcn : ContinuousOn (fun z => -(2*L n)*z+φ z+c) (Icc a b) :=
    ((continuous_const.mul continuous_id).continuousOn.add hc).add continuous_const.continuousOn
  have he := boundedInverse_expected_linearization (P n) (X n) hn φ a b (2*L n) c H d K
    (by positivity) hd hK hHa hHb hcn hφ (hG n)
  have hs : Real.sqrt (∫ ω,(X n ω-(-(2*L n)*H+φ H+c))^2 ∂P n)≤A*L n*ρ n := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    exact hQn.trans_eq (by ring)
  have hbound := he.trans (add_le_add
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hK) (sq_nonneg (2*L n)))
    (div_le_div_of_nonneg_right hQn (by positivity)))
  have hid : K*(A*L n*ρ n)/(2*L n)^2+A^2*(L n)^2*(ρ n)^2/((2*L n)^2*d) =
      (K*A/(4*L n)+A^2*ρ n/(4*d))*ρ n := by
    field_simp
    <;> ring
  rw [hid] at hbound
  rw [one_mul]
  have hratio := (div_le_iff₀ hρn).mpr hbound
  have halg (U V : ℝ) : |U/ρ n-(-V/(2*L n))/ρ n|=|U+V/(2*L n)|/ρ n := by
    rw [← sub_div,abs_div,abs_of_pos hρn]
    congr 1
    ring
  convert hratio using 1 <;> first | rfl | exact halg _ _

end Hurst
