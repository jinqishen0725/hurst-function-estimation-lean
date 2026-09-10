import Hurst.InverseL1Linearization
import Hurst.MeanLimitTransfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem boundedInverse_L1_remainder_tendsto {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)] (X : ∀ n,Ω n → ℝ)
    (hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n))
    (φ : ℝ → ℝ) (a b c H d K A : ℝ) (L ρ : ℕ → ℝ)
    (hd : 0<d) (hK : 0≤K) (hA : 0≤A) (hHa : a+d≤H) (hHb : H+d≤b)
    (hc : ContinuousOn φ (Icc a b))
    (hφ : ∀ z∈Icc a b,|φ z-φ H|≤K*|z-H|)
    (hG : ∀ n,StrongDecrease (fun z => -(2*L n)*z+φ z+c) a b (2*L n))
    (hL : Tendsto L atTop atTop) (hρpos : ∀ᶠ n in atTop,0<ρ n) (hρ : Tendsto ρ atTop (𝓝 0))
    (hQ : ∀ᶠ n in atTop,(∫ ω,(X n ω-(-(2*L n)*H+φ H+c))^2 ∂P n)≤A^2*(L n)^2*(ρ n)^2) :
    Tendsto (fun n => (∫ ω,|boundedInverse (fun z => -(2*L n)*z+φ z+c) a b (X n ω)-H+
      (X n ω-(-(2*L n)*H+φ H+c))/(2*L n)| ∂P n)/ρ n) atTop (𝓝 0) := by
  have hpos : ∀ᶠ n in atTop,0<L n := hL.eventually_gt_atTop 0
  have hsmall : Tendsto (fun n => K*A/(4*L n)+A^2*ρ n/(4*d)) atTop (𝓝 0) := by
    have hh := ((tendsto_inv_atTop_zero.comp hL).const_mul (K*A/4)).add (hρ.const_mul (A^2/(4*d)))
    simp only [mul_zero,add_zero] at hh
    convert hh using 1 <;> first | (funext n; simp only [Function.comp_apply]; ring) | rfl
  apply squeeze_zero' ?_ ?_ hsmall
  · filter_upwards [hρpos] with n hn
    exact div_nonneg (integral_nonneg (fun ω => abs_nonneg _)) hn.le
  filter_upwards [hX,hpos,hρpos,hQ] with n hn hLn hρn hQn
  have hcn : ContinuousOn (fun z => -(2*L n)*z+φ z+c) (Icc a b) :=
    ((continuous_const.mul continuous_id).continuousOn.add hc).add continuous_const.continuousOn
  have he := boundedInverse_L1_linearization (P n) (X n) hn φ a b (2*L n) c H d K
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
  exact (div_le_iff₀ hρn).mpr hbound

end Hurst
