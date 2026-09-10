import Hurst.MeanLimitTransfer
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem lipschitz_integral_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hD : Integrable (fun ω => Y ω-X ω) P) (φ : ℝ → ℝ) (K : NNReal)
    (hφ : LipschitzWith K φ) (hb : ∃ M : ℝ,∀ x y,dist (φ x) (φ y)≤M) :
    |(∫ ω,φ (Y ω) ∂P)-(∫ ω,φ (X ω) ∂P)|≤(K:ℝ)*(∫ ω,|Y ω-X ω| ∂P) := by
  obtain ⟨M,hM⟩ := hb
  have hi (Z : Ω → ℝ) (hZ : AEMeasurable Z P) : Integrable (fun ω => φ (Z ω)) P := by
    apply Integrable.of_bound (hφ.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable) (|φ 0|+M)
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs]
    have hh := (abs_sub_abs_le_abs_sub (φ (Z ω)) (φ 0)).trans (hM (Z ω) 0)
    linarith
  rw [← integral_sub (hi Y hY) (hi X hX)]
  calc
    _ ≤ ∫ ω,|φ (Y ω)-φ (X ω)| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => φ (Y ω)-φ (X ω))
    _ ≤ ∫ ω,(K:ℝ)*|Y ω-X ω| ∂P := by
      apply integral_mono ((hi Y hY).sub (hi X hX)).abs (hD.abs.const_mul K)
      intro ω
      have hh : |φ (Y ω)-φ (X ω)|≤(K:ℝ)*|Y ω-X ω| := by
        simpa only [Real.dist_eq] using hφ.dist_le_mul (Y ω) (X ω)
      convert hh using 1 <;> rfl
    _ = _ := integral_const_mul _ _

theorem triangular_L1_distribution_transfer {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X Y : ∀ n,Ω n → ℝ) (Z : Ω' → ℝ)
    (hXZ : TendstoInDistribution X atTop Z P P')
    (hY : ∀ n,AEMeasurable (Y n) (P n))
    (hD : ∀ᶠ n in atTop,Integrable (fun ω => Y n ω-X n ω) (P n))
    (hL1 : Tendsto (fun n => ∫ ω,|Y n ω-X n ω| ∂P n) atTop (𝓝 0)) :
    TendstoInDistribution Y atTop Z P P' := by
  refine ⟨hY,hXZ.aemeasurable_limit,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hb hlip
  have hbase := tendsto_iff_forall_lipschitz_integral_tendsto.mp hXZ.tendsto φ hb hlip
  obtain ⟨K,hK⟩ := hlip
  apply scalar_approximation_tendsto hbase hL1
  filter_upwards [hD] with n hn
  change |(∫ x,φ x ∂(P n).map (Y n))-(∫ x,φ x ∂(P n).map (X n))|≤_
  rw [integral_map (hY n) hK.continuous.aestronglyMeasurable,
    integral_map (hXZ.forall_aemeasurable n) hK.continuous.aestronglyMeasurable]
  exact lipschitz_integral_L1_bound (P n) (X n) (Y n) (hXZ.forall_aemeasurable n) (hY n) hn φ K hK hb

end Hurst
