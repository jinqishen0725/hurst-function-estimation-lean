import Hurst.OneBlockPatternBound

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

theorem oneBlock_weighted_pattern_bound_explicit
    {k : ℕ} (hk : 1 ≤ k) (q : MomentPattern (2 * k)) (hq : q.1.val = 1)
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ)
    (hstandard : ∀ i, MeasurePreserving (X i) P (gaussianReal 0 1))
    (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W) (ha : ∀ i, |a i| ≤ W) :
    (∑ g : Fin q.1.val ↪ ι,
      |∫ ω, ∏ j : Fin q.1.val,
        (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P|) ≤
      ((∫ x, centeredGaussianLog x ^ (2 * k) ∂gaussianReal 0 1) + 1) *
        W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
  let μ := ∫ x, centeredGaussianLog x ^ (2 * k) ∂gaussianReal 0 1
  let D := μ + 1
  have hμ : 0 ≤ μ := centeredGaussianLog_evenMoment_nonneg k
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
        _ ≤ (W ^ (2 * k) * D) * (Fintype.card ι : ℝ) := by gcongr
        _ ≤ (W ^ (2 * k) * D) * (Fintype.card ι : ℝ) ^ k := by
          exact mul_le_mul_of_nonneg_left hcard
            (mul_nonneg (pow_nonneg hW0 _) (by dsimp only [D]; linarith))
        _ = D * W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by ring
    _ = _ := rfl

end Hurst
