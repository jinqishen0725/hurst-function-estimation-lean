import Hurst.LocalTaylorLeading
import Hurst.InteriorDesignLimit

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem localPolynomialWeights_eventual_stability (r q : ℕ) (t : ℝ) (ht : t∈Icc (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop) :
    ∃ D>0,∀ᶠ n : ℕ in atTop,IsUnit (localDesignGram r n q (δ n) t).det ∧
      (∑ i,|localPolynomialWeights r n q (δ n) t i|)≤D := by
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := localPolynomialWeights_uniform_stability r q
  refine ⟨D,hD,?_⟩
  filter_upwards [hδpos,hδ.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    hN.eventually (eventually_ge_atTop N₀),eventually_ge_atTop (q+1)] with n hn hnδ hnN hnq
  have hs := hw n (by omega) (by omega) (δ n) t hn hnδ.le ht hnN
  exact ⟨hs.1,hs.2.2.1⟩

theorem localPolynomial_taylor_remainder_tendsto (r q k : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ k f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop) :
    Tendsto (fun n => smooth (localPolynomialWeights r n q (δ n) t)
      (fun i => f (grid n i.val)-taylorJet k f t (grid n i.val))/(δ n)^k) atTop (𝓝 0) := by
  obtain ⟨D,hD,hstable⟩ := localPolynomialWeights_eventual_stability r q t ⟨ht.1.le,ht.2.le⟩ δ hδpos hδ hN
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have heD : 0<ε/(2*D) := by positivity
  obtain ⟨η,hη,hrem⟩ := taylorJet_local_remainder f k (Ioo (0:ℝ) 1) (convex_Ioo _ _) hf t
    (isOpen_Ioo.mem_nhds ht) (ε/(2*D)) heD
  filter_upwards [hδpos,hδ.eventually (gt_mem_nhds hη),hstable] with n hn hnη hs
  have hb := localPolynomial_remainder_bound_on_support r n q k (δ n) t η (ε/(2*D)) f hn hnη heD.le hrem
  have hb' := hb.trans (mul_le_mul_of_nonneg_right hs.2 (by positivity))
  have he : D*(ε/(2*D)*(δ n)^k)=(ε/2)*(δ n)^k := by field_simp
  rw [he] at hb'
  have hpow : 0<(δ n)^k := pow_pos hn _
  simp only [Real.dist_eq,sub_zero,abs_div,abs_of_pos hpow]
  exact ((div_le_iff₀ hpow).mpr hb').trans_lt (half_lt_self hε)

theorem localPolynomial_bias_leading_tendsto (r q : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop) :
    Tendsto (fun n => (smooth (localPolynomialWeights r n q (δ n) t) (fun i => f (grid n i.val))-f t)/(δ n)^(r+1))
      atTop (𝓝 ((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1))) := by
  have hm := (localPolynomialWeights_moment_tendsto r q (r+1) t ht δ hδpos hδ hN).const_mul
    (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))
  have hr := localPolynomial_taylor_remainder_tendsto r q (r+1) f hf t ht δ hδpos hδ hN
  obtain ⟨D,hD,hstable⟩ := localPolynomialWeights_eventual_stability r q t ⟨ht.1.le,ht.2.le⟩ δ hδpos hδ hN
  have hh := hm.add hr
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hδpos,hstable] with n hn hs
  have he := localPolynomial_bias_leading_identity r n q (δ n) t f hn.ne' hs.1
  linarith

end Hurst
