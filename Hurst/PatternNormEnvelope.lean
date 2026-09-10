import Hurst.BSPatternMoment

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

/-- One finite `L²` envelope for all powers of the centered Gaussian log that
can occur in a `2k`-th moment expansion. -/
def gaussianLogPowerL2Envelope (k : ℕ) : ℝ :=
  1 + ∑ r : Fin (2 * k + 1),
    (eLpNorm (fun x : ℝ => centeredGaussianLog x ^ r.val) 2
      (gaussianReal 0 1)).toReal

theorem gaussianLogPowerL2Envelope_one_le (k : ℕ) :
    1 ≤ gaussianLogPowerL2Envelope k := by
  unfold gaussianLogPowerL2Envelope
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem gaussianLogPowerL2Envelope_bound (k r : ℕ) (hr : r ≤ 2 * k) :
    eLpNorm (fun x : ℝ => centeredGaussianLog x ^ r) 2 (gaussianReal 0 1) ≤
      ENNReal.ofReal (gaussianLogPowerL2Envelope k) := by
  let rr : Fin (2 * k + 1) := ⟨r, by omega⟩
  have hm := centeredGaussianLog_pow_memLp_two r
  have hfin : eLpNorm (fun x : ℝ => centeredGaussianLog x ^ r) 2
      (gaussianReal 0 1) ≠ ∞ := ne_of_lt hm.eLpNorm_lt_top
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianLogPowerL2Envelope
  calc
    (eLpNorm (fun x : ℝ => centeredGaussianLog x ^ r) 2
      (gaussianReal 0 1)).toReal =
        (eLpNorm (fun x : ℝ => centeredGaussianLog x ^ rr.val) 2
          (gaussianReal 0 1)).toReal := by rfl
    _ ≤ ∑ s : Fin (2 * k + 1),
        (eLpNorm (fun x : ℝ => centeredGaussianLog x ^ s.val) 2
          (gaussianReal 0 1)).toReal := by
      exact Finset.single_le_sum
        (f := fun s : Fin (2 * k + 1) =>
          (eLpNorm (fun x : ℝ => centeredGaussianLog x ^ s.val) 2
            (gaussianReal 0 1)).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ rr)
    _ ≤ 1 + _ := by linarith

theorem momentMultiplicity_le_order {m : ℕ} (q : MomentPattern m)
    (j : Fin q.1.val) : momentMultiplicity q j ≤ m := by
  have hsingle : momentMultiplicity q j ≤ ∑ u, momentMultiplicity q u := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [momentMultiplicity_sum] at hsingle
  exact hsingle

end Hurst
