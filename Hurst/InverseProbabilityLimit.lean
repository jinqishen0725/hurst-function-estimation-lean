import Hurst.ScaledL1Probability
import Hurst.MeanLimitTransfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem boundedInverse_linearization_in_probability {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)] (X : ∀ n,Ω n → ℝ)
    (hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n))
    (φ : ℝ → ℝ) (a b c H d K A : ℝ) (L ρ : ℕ → ℝ)
    (hd : 0<d) (hK : 0≤K) (hA : 0≤A) (hHa : a+d≤H) (hHb : H+d≤b)
    (hc : ContinuousOn φ (Icc a b))
    (hφ : ∀ z∈Icc a b,|φ z-φ H|≤K*|z-H|)
    (hG : ∀ n,StrongDecrease (fun z => -(2*L n)*z+φ z+c) a b (2*L n))
    (hL : Tendsto L atTop atTop) (hρpos : ∀ᶠ n in atTop,0<ρ n) (hρ : Tendsto ρ atTop (𝓝 0))
    (hQ : ∀ᶠ n in atTop,(∫ ω,(X n ω-(-(2*L n)*H+φ H+c))^2 ∂P n)≤A^2*(L n)^2*(ρ n)^2) (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n => (P n).real {ω | ε≤
      |boundedInverse (fun z => -(2*L n)*z+φ z+c) a b (X n ω)-H+
        (X n ω-(-(2*L n)*H+φ H+c))/(2*L n)|/ρ n}) atTop (𝓝 0) := by
  have he := boundedInverse_L1_remainder_tendsto P X hX φ a b c H d K A L ρ
    hd hK hA hHa hHb hc hφ hG hL hρpos hρ hQ
  apply scaled_L1_probability_tendsto P _ ρ ?_ hρpos he ε hε
  filter_upwards [hX,hL.eventually_gt_atTop 0] with n hn hLn
  have hcn : ContinuousOn (fun z => -(2*L n)*z+φ z+c) (Icc a b) :=
    ((continuous_const.mul continuous_id).continuousOn.add hc).add continuous_const.continuousOn
  have hY := boundedInverse_memLp_two (P n) (X n) hn _ a b (2*L n) (by positivity)
    (by linarith) hcn (hG n)
  exact ((hY.integrable (by norm_num)).sub (integrable_const H)).add
    (((hn.integrable (by norm_num)).sub (integrable_const _)).div_const (2*L n))

end Hurst
