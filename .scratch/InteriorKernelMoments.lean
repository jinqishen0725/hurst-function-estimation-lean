import Hurst.LocalDesign
import Hurst.PackingAsymptotics

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Hurst

def kernelMomentGrid (n q : ℕ) (δ t : ℝ) (k : ℕ) : ℝ :=
  ((n:ℝ)*δ)⁻¹ * ∑ i : Fin (n-q),kernelMomentFunction k ((grid n i.val-t)/δ)

def kernelMomentIntegral (k : ℕ) : ℝ := ∫ x in (-1:ℝ)..1,kernelMomentFunction k x

theorem kernelMomentGrid_interior_bound (k q : ℕ) :
    ∃ C≥0,∀ n : ℕ,0<n → q≤n → ∀ δ t : ℝ,0<δ → δ≤t → δ≤1-t →
      |kernelMomentGrid n q δ t k-kernelMomentIntegral k| ≤ C/((n:ℝ)*δ) := by
  obtain ⟨B,hB,hbound⟩ := kernelMomentFunction_bounded k
  refine ⟨(∫ x,|deriv (kernelMomentFunction k) x|)+(q:ℝ)*B,by positivity,?_⟩
  intro n hn hq δ t hδ hδt hδt1
  have hquad := midpoint_design_quadrature_uniform (kernelMomentFunction k)
    (deriv (kernelMomentFunction k))
    (fun x => ((kernelMomentFunction_smooth k).differentiable (by simp) x).hasDerivAt)
    (kernelMomentFunction_derivative_integrable k) B hbound n q hn hq δ t hδ
  have hleft : -t/δ≤-1 := (div_le_iff₀ hδ).mpr (by linarith)
  have hright : 1≤(1-t)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hi : (∫ x in (-t/δ)..((1-t)/δ),kernelMomentFunction k x)=kernelMomentIntegral k := by
    rw [compact_support_interval_clamp _ (kernelMomentFunction_smooth k).continuous
      (fun x hx => by simp only [kernelMomentFunction,localKernel_zero x hx,zero_mul]),
      max_eq_left hleft,min_eq_left hright]
    rfl
  simpa only [hi,kernelMomentGrid] using hquad

theorem kernelMomentGrid_tendsto (q k : ℕ) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop) :
    Tendsto (fun n => kernelMomentGrid n q (δ n) t k) atTop (𝓝 (kernelMomentIntegral k)) := by
  obtain ⟨C,hC,hquad⟩ := kernelMomentGrid_interior_bound k q
  have hsmall : ∀ᶠ n in atTop,δ n≤t ∧ δ n≤1-t :=
    (hδ.eventually (gt_mem_nhds ht.1)).and (hδ.eventually (gt_mem_nhds (by linarith [ht.2] : 0<1-t))) |>.mono
      (fun n hn => ⟨hn.1.le,hn.2.le⟩)
  have hbound : ∀ᶠ n in atTop,
      |kernelMomentGrid n q (δ n) t k-kernelMomentIntegral k|≤C/((n:ℝ)*δ n) := by
    filter_upwards [hδpos,hsmall,eventually_ge_atTop (q+1)] with n hn hs hnq
    exact hquad n (by omega) (by omega) (δ n) t hn hs.1 hs.2
  have hzero : Tendsto (fun n : ℕ => C/((n:ℝ)*δ n)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp hN).const_mul C
  have he := squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg
    (kernelMomentGrid n q (δ n) t k-kernelMomentIntegral k))) hbound hzero
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using he)

end Hurst
