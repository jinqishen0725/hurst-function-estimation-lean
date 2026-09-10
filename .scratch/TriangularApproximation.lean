import Hurst.TriangularL1Transfer
import Hurst.L2TestApproximation

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem scalar_double_approximation (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (b : ℕ → ℝ) (z : ℝ) (e : ℕ → ℝ)
    (hB : ∀ k,Tendsto (B k) atTop (𝓝 (b k)))
    (hb : Tendsto b atTop (𝓝 z)) (he : Tendsto e atTop (𝓝 0))
    (hE : ∀ k,∀ᶠ n in atTop,|A n-B k n|≤e k) :
    Tendsto A atTop (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he' := he.eventually (gt_mem_nhds (show 0<ε/3 by linarith))
  have hb' := (Metric.tendsto_nhds.mp hb) (ε/3) (by linarith)
  obtain ⟨k,hkE,hkb⟩ := (he'.and hb').exists
  filter_upwards [hE k,(Metric.tendsto_nhds.mp (hB k)) (ε/3) (by linarith)] with n hn hbn
  rw [Real.dist_eq] at hbn hkb ⊢
  have ht := abs_add_three (A n-B k n) (B k n-b k) (b k-z)
  have hid : A n-B k n+(B k n-b k)+(b k-z)=A n-z := by ring
  rw [hid] at ht
  linarith

theorem triangular_L1_approximation {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ∀ n,Ω n → ℝ) (Y : ℕ → ∀ n,Ω n → ℝ) (Zk : ℕ → Ω' → ℝ) (Z : Ω' → ℝ)
    (hX : ∀ n,AEMeasurable (X n) (P n))
    (hY : ∀ k,TendstoInDistribution (Y k) atTop (Zk k) P P')
    (hZ : TendstoInDistribution Zk atTop Z (fun _ => P') P')
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hE : ∀ k,∀ᶠ n in atTop,Integrable (fun ω => X n ω-Y k n ω) (P n) ∧
      (∫ ω,|X n ω-Y k n ω| ∂P n)≤e k) :
    TendstoInDistribution X atTop Z P P' := by
  refine ⟨hX,hZ.aemeasurable_limit,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hb hlip
  obtain ⟨K,hK⟩ := hlip
  have hBk (k : ℕ) := tendsto_iff_forall_lipschitz_integral_tendsto.mp (hY k).tendsto φ hb ⟨K,hK⟩
  have hbZ := tendsto_iff_forall_lipschitz_integral_tendsto.mp hZ.tendsto φ hb ⟨K,hK⟩
  apply scalar_double_approximation _ _ _ _ (fun k => (K:ℝ)*e k) hBk hbZ
    (by simpa only [mul_zero] using he.const_mul (K:ℝ))
  intro k
  filter_upwards [hE k] with n hn
  change |(∫ x,φ x ∂(P n).map (X n))-(∫ x,φ x ∂(P n).map (Y k n))|≤_
  rw [integral_map (hX n) hK.continuous.aestronglyMeasurable,
    integral_map ((hY k).forall_aemeasurable n) hK.continuous.aestronglyMeasurable]
  exact (lipschitz_integral_L1_bound (P n) (Y k n) (X n)
    ((hY k).forall_aemeasurable n) (hX n) hn.1 φ K hK hb).trans
      (mul_le_mul_of_nonneg_left hn.2 K.coe_nonneg)

theorem triangular_L2_approximation {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ∀ n,Ω n → ℝ) (Y : ℕ → ∀ n,Ω n → ℝ) (Zk : ℕ → Ω' → ℝ) (Z : Ω' → ℝ)
    (hX : ∀ n,AEMeasurable (X n) (P n))
    (hY : ∀ k,TendstoInDistribution (Y k) atTop (Zk k) P P')
    (hZ : TendstoInDistribution Zk atTop Z (fun _ => P') P')
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hE : ∀ k,∀ᶠ n in atTop,MemLp (fun ω => X n ω-Y k n ω) 2 (P n) ∧
      (∫ ω,(X n ω-Y k n ω)^2 ∂P n)≤e k) :
    TendstoInDistribution X atTop Z P P' := by
  apply triangular_L1_approximation P P' X Y Zk Z hX hY hZ (fun k => Real.sqrt (e k))
    (by convert Real.continuous_sqrt.continuousAt.tendsto.comp he using 1 <;> first | rfl | simp only [Real.sqrt_zero])
  intro k
  filter_upwards [hE k] with n hn
  exact ⟨hn.1.integrable (by norm_num),
    (integral_abs_le_sqrt_second_moment (P n) _ hn.1).trans (Real.sqrt_le_sqrt hn.2)⟩

end Hurst
