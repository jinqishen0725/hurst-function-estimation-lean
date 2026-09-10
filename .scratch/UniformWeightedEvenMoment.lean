import Hurst.UniformWeightedMoment
import Hurst.OneBlockExplicit

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem bardetSurgailis_uniform_weighted_evenMoment_bound
    (hBS : BardetSurgailisLemmaOneScalar)
    (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / (2 * k : ℝ)) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ D > 0, ∀ {ι Ω : Type}, ∀ [Fintype ι] [Nonempty ι] [DecidableEq ι]
      [MeasurableSpace Ω], ∀ (P : Measure Ω), ∀ [IsProbabilityMeasure P],
      ∀ (X : ι → Ω → ℝ),
      HasGaussianLaw (fun ω => fun i => X i ω) P →
      (∀ i, MeasurePreserving (X i) P (gaussianReal 0 1)) →
      (∀ i j, i ≠ j → |cov[X i, X j; P]| ≤ ε) →
      (∀ i, ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; P]| ^ 2 ≤ Q) →
      ∀ (a : ι → ℝ) (W : ℝ), 0 ≤ W → (∀ i, |a i| ≤ W) →
      (∫ ω, |∑ i, a i * centeredGaussianLog (X i ω)| ^ (2 * k) ∂P) ≤
        D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
  let GoodPattern := {q : MomentPattern (2 * k) // 2 ≤ q.1.val}
  have hεq : ∀ z : GoodPattern, ε < 1 / ((z.val.1.val : ℝ) - 1) := by
    intro z
    have hvle : z.val.1.val ≤ 2 * k := Nat.lt_succ_iff.mp z.val.1.isLt
    have hvR : (2 : ℝ) ≤ z.val.1.val := by exact_mod_cast z.property
    have hvleR : (z.val.1.val : ℝ) ≤ 2 * k := by exact_mod_cast hvle
    have hden : 0 < (z.val.1.val : ℝ) - 1 := by linarith
    exact hε.trans_le (one_div_le_one_div_of_le hden (by linarith))
  have hCexists : ∀ z : GoodPattern, ∃ C > 0,
      ∀ {ι Ω : Type}, ∀ [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω],
      ∀ (P : Measure Ω), ∀ [IsProbabilityMeasure P], ∀ (X : ι → Ω → ℝ),
      HasGaussianLaw (fun ω => fun i => X i ω) P →
      (∀ i, MeasurePreserving (X i) P (gaussianReal 0 1)) →
      (∀ i j, i ≠ j → |cov[X i, X j; P]| ≤ ε) →
      ∀ (Q L : ℝ), 0 ≤ Q → 0 ≤ L →
      (∀ i, ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; P]| ^ 2 ≤ Q) →
      ∀ (F : Fin z.val.1.val → ι → ℝ → ℝ),
      (∀ j i, MemLp (F j i) 2 (gaussianReal 0 1)) →
      (∀ j i, eLpNorm (F j i) 2 (gaussianReal 0 1) ≤ ENNReal.ofReal L) →
      (∀ j ∈ Finset.univ.filter
        (fun j => momentMultiplicity z.val j = 1), ∀ i,
          HermiteRankAtLeastTwo (F j i)) →
      (∑ g : Fin z.val.1.val ↪ ι,
        |∫ ω, ∏ j : Fin z.val.1.val, F j (g j) (X (g j) ω) ∂P|) ≤
        C * L ^ z.val.1.val * (Fintype.card ι : ℝ) ^
          ((z.val.1.val : ℝ) -
            ((Finset.univ.filter (fun j => momentMultiplicity z.val j = 1)).card : ℝ) / 2) *
          Q ^ (((Finset.univ.filter
            (fun j => momentMultiplicity z.val j = 1)).card : ℝ) / 2) := by
    intro z
    exact hBS z.val.1.val
      (Finset.univ.filter (fun j => momentMultiplicity z.val j = 1))
      z.property ε hε0 (hεq z)
  choose C hC hExt using hCexists
  let μ := ∫ x, centeredGaussianLog x ^ (2 * k) ∂gaussianReal 0 1
  let Dq : MomentPattern (2 * k) → ℝ := fun q =>
    if h : 2 ≤ q.1.val then
      C ⟨q, h⟩ * gaussianLogPowerL2Envelope k ^ q.1.val *
        (Q ^ ((((Finset.univ.filter
          (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2)) + 1)
    else μ + 1
  have hDq : ∀ q, 0 < Dq q := by
    intro q
    simp only [Dq]
    split_ifs with h
    · have hGpos : 0 < gaussianLogPowerL2Envelope k :=
        lt_of_lt_of_le (by norm_num) (gaussianLogPowerL2Envelope_one_le k)
      have hQp : 0 ≤ Q ^
          (((Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2) :=
        Real.rpow_nonneg hQ _
      exact mul_pos (mul_pos (hC ⟨q, h⟩) (pow_pos hGpos _)) (by linarith)
    · have hm : 0 ≤ μ := centeredGaussianLog_evenMoment_nonneg k
      linarith
  let D := 1 + ∑ q : MomentPattern (2 * k), Dq q
  have hD : 0 < D := by
    dsimp only [D]
    have hs : 0 ≤ ∑ q : MomentPattern (2 * k), Dq q :=
      Finset.sum_nonneg (fun q _ => (hDq q).le)
    linarith
  refine ⟨D, hD, ?_⟩
  intro ι Ω _ _ _ _ P _ X hGaussian hstandard hcorr hrow a W hW0 ha
  let B := W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hW0 _) (by positivity)
  have hpattern : ∀ q : MomentPattern (2 * k),
      (∑ g : Fin q.1.val ↪ ι,
        |∫ ω, ∏ j : Fin q.1.val,
          (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P|) ≤
        Dq q * B := by
    intro q
    have hqpos := momentPattern_card_pos hk q
    by_cases hv : 2 ≤ q.1.val
    · let z : GoodPattern := ⟨q, hv⟩
      let F : Fin q.1.val → ι → ℝ → ℝ := centeredLogLinearPatternFunction a q
      have hlin := hExt z P X hGaussian hstandard hcorr Q
        (W * gaussianLogPowerL2Envelope k) hQ
        (mul_nonneg hW0 (le_trans (by norm_num) (gaussianLogPowerL2Envelope_one_le k)))
        hrow F
        (fun j i => centeredLogLinearPatternFunction_memLp_two a q j i)
        (fun j i => centeredLogLinearPatternFunction_norm_bound a W hW0 ha q j i)
        (by
          intro j hj i
          exact centeredLogLinearPatternFunction_rank_singleton a q j
            (Finset.mem_filter.mp hj).2 i)
      have hwtd := weighted_pattern_bound_of_linear_bound q P X a W hW0 ha Q
        (C z) hQ (hC z)
        (by simpa only [z, F, centeredLogLinearPatternFunction] using hlin)
      simpa only [Dq, dif_pos hv, B, mul_assoc] using hwtd
    · have hq : q.1.val = 1 := by omega
      have hone := oneBlock_weighted_pattern_bound_explicit hk q hq P X hstandard
        a W hW0 ha
      simpa only [Dq, dif_neg hv, μ, B, mul_assoc] using hone
  have hY : ∀ i, MemLp (fun ω => a i * centeredGaussianLog (X i ω))
      (2 * k : ℕ) P := by
    intro i
    have hs := (centeredGaussianLog_memLp_finite (2 * k : ℝ)).comp_measurePreserving
      (hstandard i)
    have ha' := hs.const_mul (a i)
    have he : (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by norm_num
    rw [he, ENNReal.ofReal_natCast] at ha'
    simpa only [Function.comp_apply] using ha'
  have hm := moment_sum_bound_of_distinct_pattern_bounds P
    (fun i ω => a i * centeredGaussianLog (X i ω)) (2 * k) hY Dq B hpattern
  have hmabs : (∫ ω, |∑ i, a i * centeredGaussianLog (X i ω)| ^ (2 * k) ∂P) ≤
      (∑ q : MomentPattern (2 * k), Dq q) * B := by
    convert hm using 1
    apply integral_congr_ae
    filter_upwards [] with ω
    exact Even.pow_abs (even_two_mul k) (∑ i, a i * centeredGaussianLog (X i ω))
  calc
    _ ≤ (∑ q : MomentPattern (2 * k), Dq q) * B := hmabs
    _ ≤ D * B := mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) hB
    _ = D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by dsimp only [B]; ring

end Hurst
