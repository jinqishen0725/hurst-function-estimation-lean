import Hurst.CorrelationTailTransfer

noncomputable section
open Filter Set
open scoped Topology
namespace Hurst

/-- Uniform row-tail version of the correlation transfer lemma.  It is the
form needed for signed local-polynomial weights: max weight times L1 mass
reduces a weighted double sum to a supremum of correlation row tails. -/
theorem correlation_square_row_tail_vanishes
    (m : ℕ → ℕ) (r : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (d : ℕ → ℝ) (hd : Summable (fun k => d k ^ 2))
    (hd0 : ∀ k, 0 ≤ d k) (A : ℝ) (hA : 0 ≤ A) (e : ℕ → ℝ)
    (he0 : ∀ᶠ n in atTop, 0 ≤ e n)
    (herr : ∀ᶠ n in atTop, ∀ i j,
      |r n i j| ≤ A * d (Nat.dist j.val i.val) + e n)
    (herate : Tendsto (fun n => (m n : ℝ) * (e n) ^ 2) atTop (nhds 0)) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop, ∀ i,
      ∑ j, (if K < Nat.dist j.val i.val then |r n i j| ^ 2 else 0) ≤ ε := by
  intro ε hε
  have hden : 0 < 8 * A ^ 2 + 1 := by positivity
  have htail := (cutoff_square_tsum_tendsto_zero d hd).eventually
    (eventually_lt_nhds (div_pos hε hden))
  obtain ⟨K, hK⟩ := htail.exists
  have hsmall := herate.eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε / 4 by linarith))
  refine ⟨K, ?_⟩
  filter_upwards [he0, herr, hsmall] with n hen hrn hsn
  intro i
  let tail : ℕ → ℝ := fun k => if K < k then d k ^ 2 else 0
  have htailsum : Summable tail := summable_cutoff_tail hd K
  have htail0 : ∀ k, 0 ≤ tail k := by
    intro k
    dsimp only [tail]
    split_ifs <;> positivity
  have hs : (∑ j, if K < Nat.dist j.val i.val then |r n i j| ^ 2 else 0) ≤
      ∑ j : Fin (m n), (2 * A ^ 2 * tail (Nat.dist j.val i.val) +
        2 * (e n) ^ 2) := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hdist : K < Nat.dist j.val i.val
    · simp only [hdist, if_true, tail]
      have hpow := pow_le_pow_left₀ (abs_nonneg _) (hrn i j) 2
      rw [sq_abs] at hpow ⊢
      nlinarith [sq_nonneg (A * d (Nat.dist j.val i.val) - e n)]
    · simp only [hdist, if_false]
      positivity
  have hdist := grid_distance_sum_le_tsum tail htailsum htail0 (m n) i
  have hmul := mul_le_mul_of_nonneg_left hdist
    (show 0 ≤ 2 * A ^ 2 by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hs' : (∑ j, if K < Nat.dist j.val i.val then |r n i j| ^ 2 else 0) ≤
      4 * A ^ 2 * (∑' k, tail k) + 2 * m n * (e n) ^ 2 := by
    nlinarith
  apply hs'.trans
  have ht0 : 0 ≤ (∑' k, if K < k then d k ^ 2 else 0) :=
    tsum_nonneg (fun k => by split_ifs <;> positivity)
  have hfirst : 4 * A ^ 2 * (∑' k, if K < k then d k ^ 2 else 0) < ε / 2 := by
    have hprod := (lt_div_iff₀ hden).mp hK
    nlinarith
  dsimp only [tail]
  nlinarith

end Hurst
