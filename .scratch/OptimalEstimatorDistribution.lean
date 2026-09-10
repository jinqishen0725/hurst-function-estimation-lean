import Hurst.LinearizedDistribution

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem estimator_distribution_of_balanced_linearization
    {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)] {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (G T : ∀ n,Ω n → ℝ) (H : ℝ) (cal L ρ c : ℕ → ℝ) (Z : Ω' → ℝ) (β : ℝ)
    (hG : ∀ᶠ n in atTop,MemLp (G n) 2 (P n))
    (hT : ∀ᶠ n in atTop,MemLp (T n) 2 (P n))
    (hm : ∀ n,AEMeasurable (fun ω => 2*c n*L n*(T n ω-H)) (P n))
    (hL : ∀ᶠ n in atTop,0<L n) (hρ : ∀ᶠ n in atTop,0<ρ n)
    (hbal : ∀ᶠ n in atTop,c n*L n*ρ n=1)
    (hCLT : TendstoInDistribution (fun n ω => c n*(G n ω-(∫ x,G n x ∂P n))) atTop Z P P')
    (hmean : Tendsto (fun n => ((∫ x,G n x ∂P n)-cal n)/(L n*ρ n)) atTop (𝓝 β))
    (hrem : Tendsto (fun n => (∫ ω,|T n ω-H+(G n ω-cal n)/(2*L n)| ∂P n)/ρ n) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => 2*c n*L n*(T n ω-H)) atTop (fun z => -Z z-β) P P' := by
  have hc : ∀ᶠ n in atTop,c n=1/(L n*ρ n) := by
    filter_upwards [hbal,hL,hρ] with n hn hl hr
    apply (eq_div_iff (mul_pos hl hr).ne').mpr
    nlinarith [hn]
  apply linearized_distribution P P' _ _ Z (fun n => c n*((∫ x,G n x ∂P n)-cal n)) β hCLT hm
  · filter_upwards [hG,hT] with n hg ht
    exact (((ht.integrable (by norm_num)).sub (integrable_const H)).const_mul _).add
      (((hg.integrable (by norm_num)).sub (integrable_const _)).const_mul _)
  · apply hmean.congr'
    filter_upwards [hc] with n hn
    rw [hn]
    ring
  · have he := hrem.const_mul 2
    simp only [mul_zero] at he
    apply he.congr'
    filter_upwards [hc,hL,hρ] with n hn hl hr
    have hid (x : Ω n) :
        2*c n*L n*(T n x-H)+c n*(G n x-(∫ y,G n y ∂P n))+
          c n*((∫ y,G n y ∂P n)-cal n)=
        (2/ρ n)*(T n x-H+(G n x-cal n)/(2*L n)) := by
      rw [hn]
      field_simp
      <;> ring
    simp only [hid,abs_mul,abs_of_pos (div_pos (by norm_num : (0:ℝ)<2) hr),integral_const_mul]
    ring

end Hurst
