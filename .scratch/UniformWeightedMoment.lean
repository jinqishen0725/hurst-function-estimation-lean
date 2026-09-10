import Hurst.WeightedEvenMomentBound

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem weighted_pattern_bound_of_linear_bound
    {k : ℕ} (q : MomentPattern (2 * k))
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ)
    (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W) (ha : ∀ i, |a i| ≤ W)
    (Q C : ℝ) (hQ : 0 ≤ Q) (hC : 0 < C)
    (hlin :
      (∑ g : Fin q.1.val ↪ ι,
        |∫ ω, ∏ j : Fin q.1.val,
          a (g j) * centeredGaussianLog (X (g j) ω) ^ momentMultiplicity q j ∂P|) ≤
        C * (W * gaussianLogPowerL2Envelope k) ^ q.1.val *
          (Fintype.card ι : ℝ) ^ ((q.1.val : ℝ) -
            ((Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2) *
          Q ^ (((Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2)) :
    (∑ g : Fin q.1.val ↪ ι,
      |∫ ω, ∏ j : Fin q.1.val,
        (a (g j) * centeredGaussianLog (X (g j) ω)) ^ momentMultiplicity q j ∂P|) ≤
      (C * gaussianLogPowerL2Envelope k ^ q.1.val *
        (Q ^ ((((Finset.univ.filter
          (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2)) + 1)) *
        W ^ (2 * k) * (Fintype.card ι : ℝ) ^ k := by
  let G := gaussianLogPowerL2Envelope k
  let α := (Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card
  let N : ℝ := Fintype.card ι
  let D := C * G ^ q.1.val * (Q ^ ((α : ℝ) / 2) + 1)
  have hG : 1 ≤ G := gaussianLogPowerL2Envelope_one_le k
  have hQpow : 0 ≤ Q ^ ((α : ℝ) / 2) := Real.rpow_nonneg hQ _
  have hD : 0 < D := by dsimp only [D]; positivity
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
  have hNr : N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) ≤ N ^ k :=
    momentPattern_card_rpow_le_evenOrder q N hN
  change _ ≤ D * W ^ (2 * k) * N ^ k
  calc
    _ ≤ W ^ (2 * k - q.1.val) *
        (C * (W * G) ^ q.1.val * N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) *
          Q ^ ((α : ℝ) / 2)) := hpre
    _ = (C * G ^ q.1.val * Q ^ ((α : ℝ) / 2)) * W ^ (2 * k) *
        N ^ ((q.1.val : ℝ) - (α : ℝ) / 2) := by
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
    _ ≤ D * W ^ (2 * k) * N ^ k :=
      mul_le_mul_of_nonneg_left hNr (mul_nonneg hD.le (pow_nonneg hW0 _))

end Hurst
