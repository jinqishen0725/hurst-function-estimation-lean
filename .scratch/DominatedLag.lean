import Hurst.ShiftedWeightEnergy
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open Filter
open scoped Topology
namespace Hurst

theorem tendsto_sum_range_of_dominated_lag
    {α : Type*} {𝓕 : Filter α} (m : α → ℕ)
    (f : α → ℕ → ℝ) (g bound : ℕ → ℝ)
    (hsupport : ∀ n k, m n ≤ k → f n k = 0)
    (hpoint : ∀ k, Tendsto (fun n => f n k) 𝓕 (𝓝 (g k)))
    (hsum : Summable bound)
    (hbound : ∀ᶠ n in 𝓕, ∀ k, |f n k| ≤ bound k) :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), f n k)
      𝓕 (𝓝 (∑' k, g k)) := by
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint (by
    filter_upwards [hbound] with n hn
    intro k
    simpa only [Real.norm_eq_abs] using hn k)
  convert ht using 1
  funext n
  rw [tsum_eq_sum (s := Finset.range (m n)) (fun k hk =>
    hsupport n k (le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))))]

end Hurst
