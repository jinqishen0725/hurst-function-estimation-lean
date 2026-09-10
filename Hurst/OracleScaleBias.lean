import Hurst.OracleScaleL1

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem boundedInverse_scale_bias_transfer {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (X S : ∀ n,Ω n → ℝ) (G : ℕ → ℝ → ℝ) (a b s H R : ℝ) (L ρ : ℕ → ℝ)
    (hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n))
    (hS : ∀ᶠ n in atTop,MemLp (S n) 2 (P n))
    (hL : ∀ᶠ n in atTop,0<L n) (hρ : ∀ᶠ n in atTop,0<ρ n) (hab : a≤b)
    (hc : ∀ n,ContinuousOn (G n) (Icc a b))
    (hG : ∀ n,StrongDecrease (G n) a b (2*L n))
    (hscale : Tendsto (fun n => (∫ ω,|S n ω-s| ∂P n)/(L n*ρ n)) atTop (𝓝 0))
    (hknown : Tendsto (fun n => ((∫ ω,boundedInverse (G n) a b (X n ω-s) ∂P n)-H)/ρ n) atTop (𝓝 R)) :
    Tendsto (fun n => ((∫ ω,boundedInverse (G n) a b (X n ω-S n ω) ∂P n)-H)/ρ n) atTop (𝓝 R) := by
  have hO : ∀ᶠ n in atTop,Integrable (fun ω => boundedInverse (G n) a b (X n ω-s)) (P n) := by
    filter_upwards [hX,hL] with n hn hl
    exact (boundedInverse_memLp_two (P n) _ (hn.sub (memLp_const s)) (G n) a b (2*L n)
      (by positivity) hab (hc n) (hG n)).integrable (by norm_num)
  have hU : ∀ᶠ n in atTop,Integrable (fun ω => boundedInverse (G n) a b (X n ω-S n ω)) (P n) := by
    filter_upwards [hX,hS,hL] with n hn hs hl
    exact (boundedInverse_memLp_two (P n) _ (hn.sub hs) (G n) a b (2*L n)
      (by positivity) hab (hc n) (hG n)).integrable (by norm_num)
  refine L1_expected_bias_transfer P _ _ H R ρ hO hU hρ ?_ hknown
  apply squeeze_zero' ?_ ?_ (by simpa only [zero_div] using hscale.div_const 2)
  · filter_upwards [hρ] with n hn
    exact div_nonneg (integral_nonneg (fun ω => abs_nonneg _)) hn.le
  filter_upwards [hX,hS,hL,hρ] with n hn hs hl hr
  have he := div_le_div_of_nonneg_right (boundedInverse_scale_L1_bound (P n) (X n) (S n) hn hs
    (G n) a b (2*L n) s (by positivity) hab (hc n) (hG n)) hr.le
  exact he.trans_eq (by ring)

end Hurst
