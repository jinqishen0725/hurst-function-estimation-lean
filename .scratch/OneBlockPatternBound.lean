import Hurst.WeightedPatternBound
import Mathlib.Data.Fintype.CardEmbedding

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

theorem centeredGaussianLog_evenMoment_nonneg (k : ℕ) :
    0 ≤ ∫ x, centeredGaussianLog x ^ (2 * k) ∂gaussianReal 0 1 := by
  apply integral_nonneg
  intro x
  exact Even.pow_nonneg (even_two_mul k) _

theorem standardGaussian_weightedLog_evenMoment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : MeasurePreserving X P (gaussianReal 0 1))
    (a W : ℝ) (hW0 : 0 ≤ W) (ha : |a| ≤ W) (k : ℕ) :
    |∫ ω, (a * centeredGaussianLog (X ω)) ^ (2 * k) ∂P| ≤
      W ^ (2 * k) *
        (∫ x, centeredGaussianLog x ^ (2 * k) ∂gaussianReal 0 1) := by
  have hm := centeredGaussianLog_memLp_finite (2 * k : ℝ)
  have hi : Integrable (fun x => centeredGaussianLog x ^ (2 * k))
      (gaussianReal 0 1) := by
    simpa only [ENNReal.ofReal_natCast, ← memLp_one_iff_integrable] using
      (centeredGaussianLog_pow_memLp_two (2 * k)).mono_exponent (by norm_num)
  have hlaw : HasLaw X (gaussianReal 0 1) P :=
    ⟨hX.measurable.aemeasurable, hX.map_eq⟩
  have hint := hlaw.integral_comp hi.1
  change (∫ ω, centeredGaussianLog (X ω) ^ (2 * k) ∂P) =
    ∫ x, centeredGaussianLog x ^ (2 * k) ∂gaussianReal 0 1 at hint
  simp_rw [mul_pow]
  rw [integral_const_mul]
  rw [hint]
  rw [abs_mul, abs_pow, abs_of_nonneg (centeredGaussianLog_evenMoment_nonneg k)]
  have hap : |a| ^ (2 * k) ≤ W ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg _) ha _
  exact mul_le_mul_of_nonneg_right hap (centeredGaussianLog_evenMoment_nonneg k)

/-- The one-distinct-index equality pattern, proved internally from the standard
Gaussian marginal law. -/
theorem oneBlock_weighted_pattern_bound
    {k : ℕ} (hk : 1 ≤ k) (q : MomentPattern (2 * k)) (hq : q.1.val = 1)
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ)
    (hstandard : ∀ i, MeasurePreserving (X i) P (gaussianReal 0 1))
    (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W) (ha : ∀ i, |a i| ≤ W) :
    ∃ D > 0,
      (∑ g : Fin q.1.val ↪ ι,
        |∫ ω, ∏ j : Fin q.1.val,
          (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P|) ≤
        D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
  let μ := ∫ x, centeredGaussianLog x ^ (2 * k) ∂gaussianReal 0 1
  let D := μ + 1
  have hμ : 0 ≤ μ := centeredGaussianLog_evenMoment_nonneg k
  have hD : 0 < D := by dsimp only [D]; linarith
  refine ⟨D, hD, ?_⟩
  letI : Unique (Fin q.1.val) := Classical.choice
    (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using hq))
  have hmult : momentMultiplicity q default = 2 * k := by
    have hs := momentMultiplicity_sum q
    simpa only [Fintype.sum_unique] using hs
  have hterm : ∀ g : Fin q.1.val ↪ ι,
      |∫ ω, ∏ j : Fin q.1.val,
        (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P| ≤
        W ^ (2 * k) * μ := by
    intro g
    simp only [Fintype.prod_unique, hmult]
    exact standardGaussian_weightedLog_evenMoment_bound P (X (g default))
      (hstandard (g default)) (a (g default)) W hW0 (ha (g default)) k
  calc
    (∑ g : Fin q.1.val ↪ ι,
      |∫ ω, ∏ j : Fin q.1.val,
        (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P|) ≤
        ∑ _g : Fin q.1.val ↪ ι, W ^ (2 * k) * μ :=
      Finset.sum_le_sum (fun g _ => hterm g)
    _ = (Fintype.card ι : ℝ) * (W ^ (2 * k) * μ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      exact_mod_cast Fintype.card_embedding_eq_of_unique
    _ ≤ D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
      have hcard : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) ^ k := by
        have hc : (1 : ℝ) ≤ Fintype.card ι := by
          exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
        nth_rewrite 1 [← pow_one (Fintype.card ι : ℝ)]
        exact pow_le_pow_right₀ hc (by omega)
      have hμD : μ ≤ D := by dsimp only [D]; linarith
      calc
        (Fintype.card ι : ℝ) * (W ^ (2 * k) * μ) =
            (W ^ (2 * k) * μ) * (Fintype.card ι : ℝ) := by ring
        _ ≤ (W ^ (2 * k) * D) * (Fintype.card ι : ℝ) := by
          gcongr
        _ ≤ (W ^ (2 * k) * D) * (Fintype.card ι : ℝ) ^ k := by
          exact mul_le_mul_of_nonneg_left hcard
            (mul_nonneg (pow_nonneg hW0 _) hD.le)
        _ = D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by ring

end Hurst
