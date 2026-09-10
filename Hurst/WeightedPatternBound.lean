import Hurst.PatternWeightExtraction
import Hurst.PatternMomentAggregation

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

/-- Complete bound for one equality pattern: repeated weights are extracted,
Bardet--Surgailis controls the remaining distinct-index sum, and the partition
arithmetic reduces the cardinality exponent to `k`. -/
theorem bardetSurgailis_weighted_pattern_bound
    {k : ℕ} (q : MomentPattern (2 * k)) (hv : 2 ≤ q.1.val)
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hBS : BardetSurgailisLemmaOneScalarFor P X)
    (hGaussian : HasGaussianLaw (fun ω => fun i => X i ω) P)
    (hstandard : ∀ i, MeasurePreserving (X i) P (gaussianReal 0 1))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / ((q.1.val : ℝ) - 1))
    (hcorr : ∀ i j, i ≠ j → |cov[X i, X j; P]| ≤ ε)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; P]| ^ 2 ≤ Q)
    (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W) (ha : ∀ i, |a i| ≤ W) :
    ∃ D > 0,
      (∑ g : Fin q.1.val ↪ ι,
        |∫ ω, ∏ j : Fin q.1.val,
          (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P|) ≤
        D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
  obtain ⟨C, hC, hlin⟩ := bardetSurgailis_linear_pattern_bound q hv P X hBS
    hGaussian hstandard ε hε0 hε hcorr Q hQ hrow a W hW0 ha
  let G := gaussianLogPowerL2Envelope k
  let α := (Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card
  let N : ℝ := Fintype.card ι
  let D := C * G ^ q.1.val * (Q ^ ((α : ℝ) / 2) + 1)
  have hG : 1 ≤ G := gaussianLogPowerL2Envelope_one_le k
  have hQpow : 0 ≤ Q ^ ((α : ℝ) / 2) := Real.rpow_nonneg hQ _
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, ?_⟩
  have hext := pattern_sum_le_residual_times_linear P
    (fun i ω => centeredGaussianLog (X i ω)) a W hW0 ha q
  have hpre := hext.trans (mul_le_mul_of_nonneg_left hlin (pow_nonneg hW0 _))
  have hvle : q.1.val ≤ 2 * k := Nat.lt_succ_iff.mp q.1.isLt
  have hpow : W ^ (2 * k - q.1.val) * (W * G) ^ q.1.val =
      W ^ (2 * k) * G ^ q.1.val := by
    rw [mul_pow, ← mul_assoc, ← pow_add]
    rw [Nat.sub_add_cancel hvle]
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hNr : N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) ≤ N ^ k := by
    exact momentPattern_card_rpow_le_evenOrder q N hN
  change _ ≤ D * W ^ (2 * k) * N ^ k
  calc
    _ ≤ W ^ (2 * k - q.1.val) *
        (C * (W * G) ^ q.1.val * N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) *
          Q ^ ((α : ℝ) / 2)) := hpre
    _ = (C * G ^ q.1.val * Q ^ ((α : ℝ) / 2)) *
        W ^ (2 * k) * N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) := by
      calc
        _ = C * (W ^ (2 * k - q.1.val) * (W * G) ^ q.1.val) *
            N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) * Q ^ ((α : ℝ) / 2) := by ring
        _ = C * (W ^ (2 * k) * G ^ q.1.val) *
            N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) * Q ^ ((α : ℝ) / 2) := by rw [hpow]
        _ = _ := by ring
    _ ≤ D * W ^ (2 * k) * N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) := by
      have hcD : C * G ^ q.1.val * Q ^ ((α : ℝ) / 2) ≤ D := by
        dsimp only [D]
        nlinarith [mul_nonneg hC.le (pow_nonneg (le_trans (by norm_num) hG) q.1.val)]
      gcongr
    _ ≤ D * W ^ (2 * k) * N ^ k := by
      exact mul_le_mul_of_nonneg_left hNr
        (mul_nonneg hD.le (pow_nonneg hW0 _))

end Hurst
