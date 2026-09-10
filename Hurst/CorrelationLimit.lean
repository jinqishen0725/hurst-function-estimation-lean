import Hurst.GridCorrelationRows

noncomputable section
open Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem vectorCorrelation_tendsto_of_inner_norm
    {α E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {l : Filter α} (u v : α → E) (ρ : ℝ)
    (hi : Tendsto (fun x => ⟪u x, v x⟫) l (𝓝 ρ))
    (hu : Tendsto (fun x => ‖u x‖) l (𝓝 1))
    (hv : Tendsto (fun x => ‖v x‖) l (𝓝 1)) :
    Tendsto (fun x => vectorCorrelation (u x) (v x)) l (𝓝 ρ) := by
  unfold vectorCorrelation
  convert hi.div (hu.mul hv) (by norm_num : (1 : ℝ) * 1 ≠ 0) using 1
  · funext x
    rfl
  · ring

theorem tendsto_of_abs_sub_le_zero
    {α : Type*} {l : Filter α} (u v e : α → ℝ) (a : ℝ)
    (hv : Tendsto v l (𝓝 a)) (he : Tendsto e l (𝓝 0))
    (he0 : ∀ᶠ x in l, 0 ≤ e x)
    (hbound : ∀ᶠ x in l, |u x - v x| ≤ e x) :
    Tendsto u l (𝓝 a) := by
  have habs : Tendsto (fun x => |u x - v x|) l (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun x => abs_nonneg _
    · exact hbound
    · exact he
  have hdiff : Tendsto (fun x => u x - v x) l (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr (by
      simpa only [Function.comp_def] using habs)
  convert hdiff.add hv using 1
  · funext x
    ring
  · ring

theorem norm_tendsto_one_of_sq_error
    {α E : Type*} [NormedAddCommGroup E] {l : Filter α}
    (u : α → E) (e : α → ℝ)
    (he : Tendsto e l (𝓝 0)) (he0 : ∀ᶠ x in l, 0 ≤ e x)
    (hbound : ∀ᶠ x in l, |‖u x‖ ^ 2 - 1| ≤ e x) :
    Tendsto (fun x => ‖u x‖) l (𝓝 1) := by
  have hsquare : Tendsto (fun x => ‖u x‖ ^ 2) l (𝓝 1) := by
    apply tendsto_of_abs_sub_le_zero (fun x => ‖u x‖ ^ 2)
      (fun _ => 1) e 1 tendsto_const_nhds he he0
    simpa using hbound
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hsquare
  convert hsqrt using 1
  · funext x
    simp only [Function.comp_apply]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  · norm_num

end Hurst
