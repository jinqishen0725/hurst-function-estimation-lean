import Hurst.MomentExpansion

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem momentPattern_card_rpow_le_evenOrder {k : ℕ} (q : MomentPattern (2 * k))
    (M : ℝ) (hM : 1 ≤ M) :
    M ^ ((q.1.val : ℝ) -
      ((Finset.univ.filter (fun j => momentMultiplicity q j = 1)).card : ℝ) / 2) ≤
      M ^ k := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hM (momentMultiplicity_exponent_le q)

/-- Once every distinct-index equality pattern has the `M^k` bound supplied by
Bardet--Surgailis (with the one-block case handled directly), the complete
`2k`-th moment follows. This is the finite aggregation step omitted in the paper. -/
theorem weighted_evenMoment_of_pattern_bounds
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (k : ℕ) (hY : ∀ i, MemLp (Y i) (2 * k : ℕ) P)
    (C : MomentPattern (2 * k) → ℝ) (M : ℝ)
    (hpattern : ∀ q : MomentPattern (2 * k),
      (∑ g : Fin q.1.val ↪ ι,
        |∫ ω, ∏ j : Fin q.1.val, (Y (g j) ω) ^ momentMultiplicity q j ∂P|) ≤
        C q * M ^ k) :
    (∫ ω, |∑ i, Y i ω| ^ (2 * k) ∂P) ≤
      (∑ q : MomentPattern (2 * k), C q) * M ^ k := by
  have h := moment_sum_bound_of_distinct_pattern_bounds P Y (2 * k) hY C (M ^ k) hpattern
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  exact Even.pow_abs (even_two_mul k) (∑ i, Y i ω)

end Hurst
