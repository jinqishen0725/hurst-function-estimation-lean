import Hurst.LocalWeights

noncomputable section
open Set
namespace Hurst

def localWeightActiveSet (n q : ℕ) (δ t : ℝ) : Finset (Fin (n - q)) :=
  Finset.univ.filter (fun i => |(grid n i.val - t) / δ| < 1)

theorem localWeightActiveSet_card (n q : ℕ) (hn : 0 < n)
    (δ t : ℝ) (hδ : 0 < δ) (hN : 1 ≤ (n : ℝ) * δ) :
    ((localWeightActiveSet n q δ t).card : ℝ) ≤ 3 * ((n : ℝ) * δ) := by
  have h := midpoint_active_card_bound n (n - q) hn δ t hδ
    (localWeightActiveSet n q δ t)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  linarith

theorem localPolynomialWeights_zero_outside_activeSet
    (r n q : ℕ) (δ t : ℝ) (i : Fin (n - q))
    (hi : i ∉ localWeightActiveSet n q δ t) :
    localPolynomialWeights r n q δ t i = 0 := by
  apply localPolynomialWeights_zero
  have hnlt : ¬ |(grid n i.val - t) / δ| < 1 := by
    simpa only [localWeightActiveSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  exact le_of_not_gt hnlt

end Hurst
