import Hurst.PatternNormEnvelope

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

def centeredLogLinearPatternFunction {m : ℕ} {ι : Type*}
    (a : ι → ℝ) (q : MomentPattern m) (j : Fin q.1.val) (i : ι) (x : ℝ) : ℝ :=
  a i * centeredGaussianLog x ^ momentMultiplicity q j

theorem centeredLogLinearPatternFunction_memLp_two {m : ℕ} {ι : Type*}
    (a : ι → ℝ) (q : MomentPattern m) (j : Fin q.1.val) (i : ι) :
    MemLp (centeredLogLinearPatternFunction a q j i) 2 (gaussianReal 0 1) := by
  unfold centeredLogLinearPatternFunction
  exact (centeredGaussianLog_pow_memLp_two (momentMultiplicity q j)).const_mul _

theorem centeredLogLinearPatternFunction_rank_singleton {m : ℕ} {ι : Type*}
    (a : ι → ℝ) (q : MomentPattern m) (j : Fin q.1.val)
    (hj : momentMultiplicity q j = 1) (i : ι) :
    HermiteRankAtLeastTwo (centeredLogLinearPatternFunction a q j i) := by
  unfold centeredLogLinearPatternFunction
  rw [hj]
  simpa only [pow_one] using centeredGaussianLog_rankAtLeastTwo.const_mul (a i)

theorem centeredLogLinearPatternFunction_norm_bound {k : ℕ} {ι : Type*}
    (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W) (ha : ∀ i, |a i| ≤ W)
    (q : MomentPattern (2 * k)) (j : Fin q.1.val) (i : ι) :
    eLpNorm (centeredLogLinearPatternFunction a q j i) 2 (gaussianReal 0 1) ≤
      ENNReal.ofReal (W * gaussianLogPowerL2Envelope k) := by
  let f : ℝ → ℝ := fun x => centeredGaussianLog x ^ momentMultiplicity q j
  have hf := gaussianLogPowerL2Envelope_bound k (momentMultiplicity q j)
    (momentMultiplicity_le_order q j)
  have hai : ‖a i‖ₑ ≤ ENNReal.ofReal W := by
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (ha i)
  change eLpNorm (fun x => a i * f x) 2 (gaussianReal 0 1) ≤ _
  rw [show (fun x => a i * f x) = a i • f by rfl, eLpNorm_const_smul]
  calc
    ‖a i‖ₑ * eLpNorm f 2 (gaussianReal 0 1) ≤
        ENNReal.ofReal W * ENNReal.ofReal (gaussianLogPowerL2Envelope k) :=
      mul_le_mul hai hf bot_le bot_le
    _ = ENNReal.ofReal (W * gaussianLogPowerL2Envelope k) := by
      rw [ENNReal.ofReal_mul hW0]

/-- Bardet--Surgailis applied after retaining exactly one copy of each weight in
every distinct-index block. The remaining copies are handled deterministically. -/
theorem bardetSurgailis_linear_pattern_bound
    {k : ℕ} (q : MomentPattern (2 * k)) (hv : 2 ≤ q.1.val)
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hBS : BardetSurgailisLemmaOneScalarFor P X)
    (hGaussian : HasGaussianLaw (fun ω => fun i => X i ω) P)
    (hstandard : ∀ i, MeasurePreserving (X i) P (gaussianReal 0 1))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / ((q.1.val : ℝ) - 1))
    (hcorr : ∀ i j, i ≠ j → |cov[X i, X j; P]| ≤ ε)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; P]| ^ 2 ≤ Q)
    (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W) (ha : ∀ i, |a i| ≤ W) :
    ∃ C > 0,
      (∑ g : Fin q.1.val ↪ ι,
        |∫ ω, ∏ j : Fin q.1.val,
          a (g j) * centeredGaussianLog (X (g j) ω) ^ momentMultiplicity q j ∂P|) ≤
        C * (W * gaussianLogPowerL2Envelope k) ^ q.1.val *
          (Fintype.card ι : ℝ) ^ ((q.1.val : ℝ) -
            ((Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2) *
          Q ^ (((Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2) := by
  let A : Finset (Fin q.1.val) :=
    Finset.univ.filter (fun j => momentMultiplicity q j = 1)
  obtain ⟨C, hC, hb⟩ := hBS hGaussian hstandard q.1.val A hv ε hε0 hε
  refine ⟨C, hC, ?_⟩
  let F : Fin q.1.val → ι → ℝ → ℝ := centeredLogLinearPatternFunction a q
  have hm : ∀ j i, MemLp (F j i) 2 (gaussianReal 0 1) :=
    fun j i => centeredLogLinearPatternFunction_memLp_two a q j i
  have hn : ∀ j i, eLpNorm (F j i) 2 (gaussianReal 0 1) ≤
      ENNReal.ofReal (W * gaussianLogPowerL2Envelope k) :=
    fun j i => centeredLogLinearPatternFunction_norm_bound a W hW0 ha q j i
  have hr : ∀ j ∈ A, ∀ i, HermiteRankAtLeastTwo (F j i) := by
    intro j hj i
    exact centeredLogLinearPatternFunction_rank_singleton a q j
      (Finset.mem_filter.mp hj).2 i
  have h := hb hcorr Q (W * gaussianLogPowerL2Envelope k) hQ
    (mul_nonneg hW0 (le_trans (by norm_num) (gaussianLogPowerL2Envelope_one_le k)))
    hrow F hm hn hr
  simpa only [F, centeredLogLinearPatternFunction] using h

end Hurst
