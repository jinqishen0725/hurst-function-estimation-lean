import Hurst.FrozenLagSummability
import Hurst.WeightEnergyLimit
import Hurst.GaussianLogRank

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem gaussianLogTruncationCovariance_nonneg (K : ℕ) (ρ : ℝ) :
    0 ≤ gaussianLogTruncationCovariance K ρ := by
  unfold gaussianLogTruncationCovariance
  exact Finset.sum_nonneg fun k _ => gaussianLog_series_term_nonneg ρ k

theorem gaussianLogTruncationCovariance_one_pos (K : ℕ) (hK : 3 ≤ K) :
    0 < gaussianLogTruncationCovariance K 1 := by
  have hmem : 2 ∈ Finset.range K := Finset.mem_range.mpr (by omega)
  have hle : gaussianLogHermiteCoefficient 2 ^ 2 * (1 : ℝ) ^ 2 ≤
      ∑ k ∈ Finset.range K, gaussianLogHermiteCoefficient k ^ 2 * (1 : ℝ) ^ k := by
    exact Finset.single_le_sum (fun k _ => gaussianLog_series_term_nonneg 1 k) hmem
  rw [gaussianLogHermiteCoefficient, gaussianLog_hermite_coefficient_two,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hle
  unfold gaussianLogTruncationCovariance
  norm_num at hle ⊢
  linarith

theorem firstIncrementLagCorrelation_zero (h : ℝ) (hh : 0 < h) :
    firstIncrementLagCorrelation h 0 = 1 := by
  unfold firstIncrementLagCorrelation
  norm_num [Real.zero_rpow (by positivity : 2 * h ≠ 0)]

theorem secondIncrementLagCorrelation_zero
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    secondIncrementLagCorrelation h 0 = 1 := by
  unfold secondIncrementLagCorrelation
  rw [firstIncrementLagCorrelation_zero h hh]
  unfold firstIncrementLagCorrelation
  norm_num [Real.zero_rpow (by positivity : 2 * h ≠ 0)]
  have hden : 4 - (2 : ℝ) ^ (2 * h) ≠ 0 := by
    have hp : (2 : ℝ) ^ (2 * h) < (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    norm_num at hp
    linarith
  field_simp
  ring

theorem equivalentKernel_square_integral_pos (r : ℕ) :
    0 < ∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2 := by
  have hex : ∃ c ∈ Icc (-1 : ℝ) 1, equivalentKernel r c ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (∫ x in (-1 : ℝ)..1, equivalentKernel r x) = 0 := by
      calc
        (∫ x in (-1 : ℝ)..1, equivalentKernel r x) =
            ∫ x in (-1 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact h x (by
            simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)
        _ = 0 := intervalIntegral.integral_zero
    rw [equivalentKernel_integral] at hzero
    norm_num at hzero
  obtain ⟨c, hc, hc0⟩ := hex
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (a := (-1 : ℝ)) (b := 1) (f := fun _ => (0 : ℝ))
    (g := fun x => equivalentKernel r x ^ 2)
    (by norm_num) continuousOn_const
    ((equivalentKernel_continuous r).pow 2).continuousOn
    (fun x hx => sq_nonneg _) ⟨c, hc, sq_pos_of_ne_zero hc0⟩
  simpa only [intervalIntegral.integral_zero] using hlt

theorem firstIncrement_symmetric_truncationCovariance_pos
    (K : ℕ) (h : ℝ) (hK : 3 ≤ K) (hh : 0 < h) (hhb : h < 3 / 4) :
    0 < ∑' k : ℕ, (if k = 0 then 1 else 2) *
      gaussianLogTruncationCovariance K (firstIncrementLagCorrelation h k) := by
  have hs := firstIncrement_symmetric_truncationCovariance_summable K h hh hhb
  exact hs.tsum_pos
    (fun k => mul_nonneg (by split_ifs <;> norm_num)
      (gaussianLogTruncationCovariance_nonneg K _)) 0 (by
        simp only [if_pos, one_mul, Nat.cast_zero,
          firstIncrementLagCorrelation_zero h hh]
        exact gaussianLogTruncationCovariance_one_pos K hK)

theorem secondIncrement_symmetric_truncationCovariance_pos
    (K : ℕ) (h : ℝ) (hK : 3 ≤ K) (hh : 0 < h) (hh1 : h < 1) :
    0 < ∑' k : ℕ, (if k = 0 then 1 else 2) *
      gaussianLogTruncationCovariance K (secondIncrementLagCorrelation h k) := by
  have hs := secondIncrement_symmetric_truncationCovariance_summable K h hh hh1
  exact hs.tsum_pos
    (fun k => mul_nonneg (by split_ifs <;> norm_num)
      (gaussianLogTruncationCovariance_nonneg K _)) 0 (by
        simp only [if_pos, one_mul, Nat.cast_zero,
          secondIncrementLagCorrelation_zero h hh hh1]
        exact gaussianLogTruncationCovariance_one_pos K hK)

theorem firstIncrement_full_truncatedVariance_limit_pos
    (r K : ℕ) (h : ℝ) (hK : 3 ≤ K) (hh : 0 < h) (hhb : h < 3 / 4) :
    0 < (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
      ∑' k : ℕ, (if k = 0 then 1 else 2) *
        gaussianLogTruncationCovariance K (firstIncrementLagCorrelation h k) :=
  mul_pos (equivalentKernel_square_integral_pos r)
    (firstIncrement_symmetric_truncationCovariance_pos K h hK hh hhb)

theorem secondIncrement_full_truncatedVariance_limit_pos
    (r K : ℕ) (h : ℝ) (hK : 3 ≤ K) (hh : 0 < h) (hh1 : h < 1) :
    0 < (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
      ∑' k : ℕ, (if k = 0 then 1 else 2) *
        gaussianLogTruncationCovariance K (secondIncrementLagCorrelation h k) :=
  mul_pos (equivalentKernel_square_integral_pos r)
    (secondIncrement_symmetric_truncationCovariance_pos K h hK hh hh1)

end Hurst
