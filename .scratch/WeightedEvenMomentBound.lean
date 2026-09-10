import Hurst.OneBlockPatternBound

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem momentPattern_card_pos {k : ℕ} (hk : 1 ≤ k)
    (q : MomentPattern (2 * k)) : 0 < q.1.val := by
  by_contra h
  have hv : q.1.val = 0 := Nat.eq_zero_of_not_pos h
  let i : Fin (2 * k) := ⟨0, by omega⟩
  have z : Fin 0 := hv ▸ q.2.val i
  exact Fin.elim0 z

/-- Generic complete `2k`-moment bound for a weighted standardized Gaussian
array. This closes every internal equality-pattern case; its only probability
input is the stated Bardet--Surgailis interface. -/
theorem bardetSurgailis_weighted_evenMoment_bound
    (k : ℕ) (hk : 1 ≤ k)
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hBS : BardetSurgailisLemmaOneScalarFor P X)
    (hGaussian : HasGaussianLaw (fun ω => fun i => X i ω) P)
    (hstandard : ∀ i, MeasurePreserving (X i) P (gaussianReal 0 1))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / (2 * k : ℝ))
    (hcorr : ∀ i j, i ≠ j → |cov[X i, X j; P]| ≤ ε)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, |cov[X i, X j; P]| ^ 2 ≤ Q)
    (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W) (ha : ∀ i, |a i| ≤ W) :
    ∃ D > 0,
      (∫ ω, |∑ i, a i * centeredGaussianLog (X i ω)| ^ (2 * k) ∂P) ≤
        D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
  have hper : ∀ q : MomentPattern (2 * k), ∃ D > 0,
      (∑ g : Fin q.1.val ↪ ι,
        |∫ ω, ∏ j : Fin q.1.val,
          (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P|) ≤
        D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
    intro q
    have hqpos := momentPattern_card_pos hk q
    by_cases hq : q.1.val = 1
    · exact oneBlock_weighted_pattern_bound hk q hq P X hstandard a W hW0 ha
    · have hv : 2 ≤ q.1.val := by omega
      have hvle : q.1.val ≤ 2 * k := Nat.lt_succ_iff.mp q.1.isLt
      have hvR : (2 : ℝ) ≤ q.1.val := by exact_mod_cast hv
      have hvleR : (q.1.val : ℝ) ≤ 2 * k := by exact_mod_cast hvle
      have hden : 0 < (q.1.val : ℝ) - 1 := by linarith
      have hle : (q.1.val : ℝ) - 1 ≤ (2 * k : ℝ) := by linarith
      have hεq : ε < 1 / ((q.1.val : ℝ) - 1) :=
        hε.trans_le (one_div_le_one_div_of_le hden hle)
      exact bardetSurgailis_weighted_pattern_bound q hv P X hBS hGaussian hstandard
        ε hε0 hεq hcorr Q hQ hrow a W hW0 ha
  choose D hD hpattern using hper
  let B := W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hW0 _) (by positivity)
  have hY : ∀ i, MemLp (fun ω => a i * centeredGaussianLog (X i ω))
      (2 * k : ℕ) P := by
    intro i
    have hg := centeredGaussianLog_memLp_finite (2 * k : ℝ)
    have hs := hg.comp_measurePreserving (hstandard i)
    have ha' := hs.const_mul (a i)
    have he : (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by norm_num
    rw [he, ENNReal.ofReal_natCast] at ha'
    simpa only [Function.comp_apply] using ha'
  have hm := moment_sum_bound_of_distinct_pattern_bounds P
    (fun i ω => a i * centeredGaussianLog (X i ω)) (2 * k) hY D B (by
      intro q
      simpa only [B, mul_assoc] using hpattern q)
  have hmabs : (∫ ω, |∑ i, a i * centeredGaussianLog (X i ω)| ^ (2 * k) ∂P) ≤
      (∑ q : MomentPattern (2 * k), D q) * B := by
    convert hm using 1
    apply integral_congr_ae
    filter_upwards [] with ω
    exact Even.pow_abs (even_two_mul k) (∑ i, a i * centeredGaussianLog (X i ω))
  let DT := 1 + ∑ q : MomentPattern (2 * k), D q
  have hDT : 0 < DT := by
    dsimp only [DT]
    have hs : 0 ≤ ∑ q : MomentPattern (2 * k), D q :=
      Finset.sum_nonneg (fun q _ => (hD q).le)
    linarith
  refine ⟨DT, hDT, ?_⟩
  calc
    _ ≤ (∑ q : MomentPattern (2 * k), D q) * B := hmabs
    _ ≤ DT * B := by
      exact mul_le_mul_of_nonneg_right (by dsimp only [DT]; linarith) hB
    _ = DT * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
      dsimp only [B]
      ring

end Hurst
