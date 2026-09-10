import Hurst.TriangularL1Transfer

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem linearized_distribution {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X Y : ∀ n,Ω n → ℝ) (Z : Ω' → ℝ) (b : ℕ → ℝ) (β : ℝ)
    (hXZ : TendstoInDistribution X atTop Z P P')
    (hY : ∀ n,AEMeasurable (Y n) (P n))
    (hi : ∀ᶠ n in atTop,Integrable (fun ω => Y n ω+X n ω) (P n))
    (hb : Tendsto b atTop (𝓝 β))
    (hR : Tendsto (fun n => ∫ ω,|Y n ω+X n ω+b n| ∂P n) atTop (𝓝 0)) :
    TendstoInDistribution Y atTop (fun ω => -Z ω-β) P P' := by
  have hbase := hXZ.continuous_comp (show Continuous (fun z : ℝ => -z-β) by fun_prop)
  apply triangular_L1_distribution_transfer P P' (fun n ω => -X n ω-β) Y
    (fun ω => -Z ω-β) hbase hY
  · filter_upwards [hi] with n hn
    convert hn.add (integrable_const β) using 1 <;> first | rfl | (funext ω; simp only [Pi.add_apply]; ring)
  · have hsmall : Tendsto (fun n => |β-b n|) atTop (𝓝 0) := by
      convert (tendsto_const_nhds.sub hb).abs using 1 <;> first | rfl | simp
    apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun _ => abs_nonneg _)))
      _ (by simpa only [add_zero] using hR.add hsmall)
    filter_upwards [hi] with n hn
    have hRi : Integrable (fun ω => Y n ω+X n ω+b n) (P n) := by
      convert hn.add (integrable_const (b n)) using 1 <;> rfl
    have hDi : Integrable (fun ω => Y n ω-(-X n ω-β)) (P n) := by
      convert hn.add (integrable_const β) using 1 <;> first | rfl | (funext ω; simp only [Pi.add_apply]; ring)
    calc
      _ ≤ ∫ ω,(|Y n ω+X n ω+b n|+|β-b n|) ∂P n := by
        have hsum : Integrable (fun ω => |Y n ω+X n ω+b n|+|β-b n|) (P n) := by
          convert hRi.abs.add (integrable_const |β-b n|) using 1 <;> rfl
        apply integral_mono hDi.abs hsum
        intro ω
        convert abs_add_le (Y n ω+X n ω+b n) (β-b n) using 1 <;> ring
      _ = _ := by rw [integral_add hRi.abs (integrable_const _),integral_const,probReal_univ,one_smul]

end Hurst
