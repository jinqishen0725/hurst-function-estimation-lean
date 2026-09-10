import Hurst.WeakCorrelationGrouping

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem grouped_evenMoment_integral_bound
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hY : ∀ i, MemLp (Y i) (2 * k : ℕ) P)
    {d : ℕ} (color : ι → Fin d) :
    (∫ ω, |∑ i, Y i ω| ^ (2 * k) ∂P) ≤
      (d : ℝ) ^ (2 * k - 1) *
        ∑ c, ∫ ω, |colorClassSum color (fun i => Y i ω) c| ^ (2 * k) ∂P := by
  classical
  have hfullMem : MemLp (fun ω => ∑ i, Y i ω) (2 * k : ℕ) P :=
    memLp_finsetSum Finset.univ (fun i _ => hY i)
  have hfull : Integrable (fun ω => |∑ i, Y i ω| ^ (2 * k)) P := by
    simpa only [Real.norm_eq_abs] using hfullMem.integrable_norm_pow'
  have hgroupMem : ∀ c, MemLp
      (fun ω => colorClassSum color (fun i => Y i ω) c) (2 * k : ℕ) P := by
    intro c
    unfold colorClassSum
    exact memLp_finsetSum _ (fun i _ => hY i)
  have hgroup : ∀ c, Integrable
      (fun ω => |colorClassSum color (fun i => Y i ω) c| ^ (2 * k)) P := by
    intro c
    simpa only [Real.norm_eq_abs] using (hgroupMem c).integrable_norm_pow'
  have hright : Integrable (fun ω =>
      (d : ℝ) ^ (2 * k - 1) *
        ∑ c, |colorClassSum color (fun i => Y i ω) c| ^ (2 * k)) P :=
    (integrable_finsetSum Finset.univ (fun c _ => hgroup c)).const_mul _
  have horder : 2 * k - 1 + 1 = 2 * k := by omega
  calc
    _ ≤ ∫ ω, (d : ℝ) ^ (2 * k - 1) *
        ∑ c, |colorClassSum color (fun i => Y i ω) c| ^ (2 * k) ∂P := by
      apply integral_mono hfull hright
      intro ω
      simpa only [horder] using
        abs_sum_pow_le_colorClassSum color (fun i => Y i ω) (2 * k - 1)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun c _ => hgroup c)]

theorem grouped_evenMoment_integral_uniform
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hY : ∀ i, MemLp (Y i) (2 * k : ℕ) P)
    {d : ℕ} (color : ι → Fin d) (B : ℝ)
    (hB : ∀ c, (∫ ω, |colorClassSum color (fun i => Y i ω) c| ^ (2 * k) ∂P) ≤ B) :
    (∫ ω, |∑ i, Y i ω| ^ (2 * k) ∂P) ≤
      (d : ℝ) ^ (2 * k) * B := by
  calc
    _ ≤ (d : ℝ) ^ (2 * k - 1) *
        ∑ c, ∫ ω, |colorClassSum color (fun i => Y i ω) c| ^ (2 * k) ∂P :=
      grouped_evenMoment_integral_bound P Y k hk hY color
    _ ≤ (d : ℝ) ^ (2 * k - 1) * ∑ _c : Fin d, B := by
      gcongr with c
      exact hB c
    _ = (d : ℝ) ^ (2 * k) * B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have horder : 2 * k - 1 + 1 = 2 * k := by omega
      calc
        (d : ℝ) ^ (2 * k - 1) * ((d : ℝ) * B) =
            ((d : ℝ) ^ (2 * k - 1) * (d : ℝ)) * B := by ring
        _ = (d : ℝ) ^ (2 * k - 1 + 1) * B := by rw [pow_succ]
        _ = (d : ℝ) ^ (2 * k) * B := by rw [horder]

end Hurst
