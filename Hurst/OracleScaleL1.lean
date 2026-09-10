import Hurst.ExpectedLinearization
import Hurst.TriangularL1Transfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem boundedInverse_scale_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X S : Ω → ℝ)
    (hX : MemLp X 2 P) (hS : MemLp S 2 P)
    (G : ℝ → ℝ) (a b m s : ℝ) (hm : 0<m) (hab : a≤b)
    (hc : ContinuousOn G (Icc a b)) (hG : StrongDecrease G a b m) :
    (∫ ω,|boundedInverse G a b (X ω-S ω)-boundedInverse G a b (X ω-s)| ∂P)
      ≤ (∫ ω,|S ω-s| ∂P)/m := by
  have hU := boundedInverse_memLp_two P (fun ω => X ω-S ω) (hX.sub hS) G a b m hm hab hc hG
  have hO := boundedInverse_memLp_two P (fun ω => X ω-s) (hX.sub (memLp_const s)) G a b m hm hab hc hG
  calc
    _ ≤ ∫ ω,|S ω-s|/m ∂P := by
      apply integral_mono ((hU.sub hO).integrable (by norm_num)).abs
        (((hS.sub (memLp_const s)).integrable (by norm_num)).abs.div_const m)
      intro ω
      have he := clippedInverse_contraction G a b m (X ω-S ω) (X ω-s) _ _ hm hG
        (boundedInverse_spec G a b _ hab hc) (boundedInverse_spec G a b _ hab hc)
      have hid : |X ω-S ω-(X ω-s)|=|S ω-s| := by
        have h : X ω-S ω-(X ω-s)=-(S ω-s) := by ring
        rw [h,abs_neg]
      rw [hid] at he
      convert he using 1 <;> rfl
    _ = _ := integral_div _ _

theorem boundedInverse_normalized_scale_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X S : Ω → ℝ)
    (hX : MemLp X 2 P) (hS : MemLp S 2 P)
    (G : ℝ → ℝ) (a b L s A : ℝ) (hL : 0<L) (hA : 0≤A) (hab : a≤b)
    (hc : ContinuousOn G (Icc a b)) (hG : StrongDecrease G a b (2*L)) :
    (∫ ω,|2*A*L*(boundedInverse G a b (X ω-S ω)-boundedInverse G a b (X ω-s))| ∂P)
      ≤ A*(∫ ω,|S ω-s| ∂P) := by
  have hid (z : ℝ) : |2*A*L*z|=2*A*L*|z| := by
    rw [abs_mul,abs_of_nonneg (show 0≤2*A*L by positivity)]
  simp only [hid]
  rw [integral_const_mul]
  have he := mul_le_mul_of_nonneg_left (boundedInverse_scale_L1_bound P X S hX hS G a b (2*L) s
    (by positivity) hab hc hG) (show 0≤2*A*L by positivity)
  exact he.trans_eq (by field_simp <;> ring)

theorem boundedInverse_scale_L1_tendsto {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (X S : ∀ n,Ω n → ℝ) (G : ℕ → ℝ → ℝ) (a b s : ℝ) (L A : ℕ → ℝ)
    (hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n))
    (hS : ∀ᶠ n in atTop,MemLp (S n) 2 (P n))
    (hL : ∀ᶠ n in atTop,0<L n) (hA : ∀ᶠ n in atTop,0≤A n) (hab : a≤b)
    (hc : ∀ n,ContinuousOn (G n) (Icc a b))
    (hG : ∀ n,StrongDecrease (G n) a b (2*L n))
    (hscale : Tendsto (fun n => A n*(∫ ω,|S n ω-s| ∂P n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,|2*A n*L n*(boundedInverse (G n) a b (X n ω-S n ω)-
      boundedInverse (G n) a b (X n ω-s))| ∂P n) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun ω => abs_nonneg _))) ?_ hscale
  filter_upwards [hX,hS,hL,hA] with n hn hs hl ha
  exact boundedInverse_normalized_scale_L1_bound (P n) (X n) (S n) hn hs (G n) a b (L n) s (A n) hl ha hab (hc n) (hG n)

theorem L1_expected_bias_transfer {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (X Y : ∀ n,Ω n → ℝ) (H R : ℝ) (ρ : ℕ → ℝ)
    (hX : ∀ᶠ n in atTop,Integrable (X n) (P n))
    (hY : ∀ᶠ n in atTop,Integrable (Y n) (P n))
    (hρ : ∀ᶠ n in atTop,0<ρ n)
    (hL1 : Tendsto (fun n => (∫ ω,|Y n ω-X n ω| ∂P n)/ρ n) atTop (𝓝 0))
    (hOX : Tendsto (fun n => ((∫ ω,X n ω ∂P n)-H)/ρ n) atTop (𝓝 R)) :
    Tendsto (fun n => ((∫ ω,Y n ω ∂P n)-H)/ρ n) atTop (𝓝 R) := by
  apply scalar_approximation_tendsto hOX hL1 (C := 1)
  filter_upwards [hX,hY,hρ] with n hx hy hr
  rw [one_mul,← sub_div,abs_div,abs_of_pos hr,sub_sub_sub_cancel_right,← integral_sub hy hx]
  apply div_le_div_of_nonneg_right _ hr.le
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => Y n ω-X n ω)

end Hurst
