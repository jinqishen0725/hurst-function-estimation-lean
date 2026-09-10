import Hurst.FirstUnknownScaleTests

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Hurst

theorem localPolynomialWeights_eventual_mass (r d : ℕ) (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop,0<δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun (n : ℕ) => (n:ℝ)*δ n) atTop atTop) :
    ∀ᶠ n in atTop,∀ t∈Icc (0:ℝ) 1,∑ i,localPolynomialWeights r n d (δ n) t i=1 := by
  obtain ⟨N,hNp,D,hD,hw⟩ := localPolynomialWeights_uniform_stability r d
  filter_upwards [hδ,hδ0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    hN.eventually_ge_atTop N,eventually_ge_atTop d,eventually_gt_atTop 0] with n hδ hδhalf hN hn hn0
  intro t ht
  have he := (hw n hn0 hn (δ n) t hδ hδhalf.le ht hN).2.2.2 0
  simpa using he

theorem averagedLocalWeights_eventual_mass (r d : ℕ) (m : ℕ → ℕ) (δ : ℕ → ℝ)
    (hm : ∀ᶠ n in atTop,0<m n) (hδ : ∀ᶠ n in atTop,0<δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun (n : ℕ) => (n:ℝ)*δ n) atTop atTop) :
    ∀ᶠ n in atTop,∑ i,averagedLocalWeights r n d (m n) (δ n) i=1 := by
  filter_upwards [hm,localPolynomialWeights_eventual_mass r d δ hδ hδ0 hN] with n hm hw
  apply averagedLocalWeights_sum _ _ _ _ hm
  intro j
  have hj := grid_mem (m n) j.val hm j.isLt
  exact hw _ ⟨hj.1.le,hj.2.le⟩

end Hurst
