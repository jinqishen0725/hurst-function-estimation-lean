import Hurst.OracleScaleL1

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem boundedInverse_scale_distribution_transfer {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ)
    (X S : ∀ n,Ω n → ℝ) (G : ℕ → ℝ → ℝ) (a b s : ℝ) (L A c : ℕ → ℝ)
    (hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n))
    (hS : ∀ᶠ n in atTop,MemLp (S n) 2 (P n))
    (hL : ∀ᶠ n in atTop,0<L n) (hA : ∀ᶠ n in atTop,0≤A n) (hab : a≤b)
    (hc : ∀ n,ContinuousOn (G n) (Icc a b))
    (hG : ∀ n,StrongDecrease (G n) a b (2*L n))
    (hY : ∀ n,AEMeasurable (fun ω => 2*A n*L n*(boundedInverse (G n) a b (X n ω-S n ω)-c n)) (P n))
    (hscale : Tendsto (fun n => A n*(∫ ω,|S n ω-s| ∂P n)) atTop (𝓝 0))
    (hknown : TendstoInDistribution
      (fun n ω => 2*A n*L n*(boundedInverse (G n) a b (X n ω-s)-c n)) atTop Z P P') :
    TendstoInDistribution
      (fun n ω => 2*A n*L n*(boundedInverse (G n) a b (X n ω-S n ω)-c n)) atTop Z P P' := by
  refine triangular_L1_distribution_transfer P P' _ _ Z hknown hY ?_ ?_
  · filter_upwards [hX,hS,hL] with n hn hs hl
    have hU := boundedInverse_memLp_two (P n) _ (hn.sub hs) (G n) a b (2*L n) (by positivity) hab (hc n) (hG n)
    have hO := boundedInverse_memLp_two (P n) _ (hn.sub (memLp_const s)) (G n) a b (2*L n) (by positivity) hab (hc n) (hG n)
    exact ((((hU.integrable (by norm_num)).sub (integrable_const (c n))).const_mul _).sub
      (((hO.integrable (by norm_num)).sub (integrable_const (c n))).const_mul _))
  · have he := boundedInverse_scale_L1_tendsto P X S G a b s L A hX hS hL hA hab hc hG hscale
    convert he using 1
    funext n
    apply integral_congr_ae
    filter_upwards [] with ω
    congr 1
    ring

end Hurst
